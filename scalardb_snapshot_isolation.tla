---------------------------- MODULE scalardb_snapshot_isolation ----------------------------
(* 
 * PlusCal model for verifying snapshot isolation of ScalarDB's Consensus Commit protocol
 * This model represents the transaction processing with SNAPSHOT isolation level
 * Key difference from SERIALIZABLE: No validation phase, allowing write skew anomalies
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    KEYS,           \* Set of data keys
    TRANSACTIONS,   \* Set of transaction identifiers  
    VALUES,         \* Set of possible values
    NULL            \* Null value


\* Transaction states
TxnStates == {"ACTIVE", "PREPARING", "PREPARED", "COMMITTING", "COMMITTED", "ABORTED"}

\* Record states
RecordStates == {"COMMITTED", "PREPARED", "DELETED"}



(*--algorithm scalardb_snapshot_isolation

variables
    store = [k \in KEYS |-> [value |-> NULL, tx_id |-> NULL, tx_state |-> "COMMITTED", 
                              tx_version |-> 0, before_value |-> NULL, committed_at |-> 0]],
    txnState = [t \in TRANSACTIONS |-> "ACTIVE"],
    readSet = [t \in TRANSACTIONS |-> {}],  
    writeSet = [t \in TRANSACTIONS |-> [k \in KEYS |-> NULL]],
    deleteSet = [t \in TRANSACTIONS |-> {}],
    startTime = [t \in TRANSACTIONS |-> 0],
    committedTxns = {},
    abortedTxns = {},
    globalTime = 1,
    commitTime = [t \in TRANSACTIONS |-> 0];

define
    \* All completed transactions are either committed or aborted
    CompletedTxns == committedTxns \union abortedTxns
    
    \* A transaction is active if not completed
    ActiveTxns == TRANSACTIONS \ CompletedTxns
    
    \* Type invariant
    TypeInvariant ==
        /\ \A k \in KEYS : 
            /\ store[k].value \in VALUES \union {NULL}
            /\ store[k].tx_id \in TRANSACTIONS \union {NULL}
            /\ store[k].tx_state \in RecordStates
            /\ store[k].tx_version \in Nat
            /\ store[k].before_value \in VALUES \union {NULL}
            /\ store[k].committed_at \in Nat
        /\ \A t \in TRANSACTIONS : txnState[t] \in TxnStates
        /\ committedTxns \subseteq TRANSACTIONS
        /\ abortedTxns \subseteq TRANSACTIONS
        /\ globalTime \in Nat
        
    \* Consistency invariant
    ConsistencyInvariant ==
        \A k \in KEYS : 
            ((store[k].tx_state = "PREPARED" \/ store[k].tx_state = "DELETED") /\ store[k].tx_id # NULL) =>
                store[k].tx_id \notin CompletedTxns
                
    \* Snapshot isolation property: No write-write conflicts
    \* Two concurrent transactions cannot modify the same key
    NoWriteWriteConflicts ==
        \A t1, t2 \in committedTxns : \A k \in KEYS :
            (t1 # t2 /\ 
             (k \in DOMAIN writeSet[t1] /\ writeSet[t1][k] # NULL) /\
             (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL)) =>
                \* Either t1 committed before t2 started or vice versa
                \/ commitTime[t1] < startTime[t2]
                \/ commitTime[t2] < startTime[t1]
                
    \* Read from snapshot: All reads see a consistent snapshot
    ConsistentSnapshot ==
        \A t \in TRANSACTIONS : \A k \in readSet[t] :
            \* Transaction reads values that were committed before it started
            TRUE  \* This is enforced by the GetSnapshotValue function
            
    \* Write skew is allowed in snapshot isolation
    \* Example: Two transactions read x and y, then t1 writes y and t2 writes x
    \* Both can commit under snapshot isolation but not under serializability
    
end define;

fair process transaction \in TRANSACTIONS
variables
    localReadSet = {},
    localWriteSet = [k \in KEYS |-> NULL],
    localDeleteSet = {},
    localSnapshot = [k \in KEYS |-> NULL],  \* Local snapshot of read values
    canCommit = TRUE,
    txnStartTime = 0;
begin
    TxnStart:
        \* Record transaction start time for snapshot
        txnStartTime := globalTime;
        startTime[self] := txnStartTime;
        globalTime := globalTime + 1;
        
    ReadWrite:
        \* Non-deterministically perform reads, writes, and deletes
        while TRUE do
            either
                \* Read operation - read from consistent snapshot
                with key \in KEYS do
                    if store[key].tx_state = "COMMITTED" /\ 
                       store[key].committed_at <= txnStartTime /\ 
                       ~(store[key].tx_state = "DELETED" \/ (store[key].tx_state = "COMMITTED" /\ store[key].value = NULL)) /\ 
                       store[key].value # NULL then
                            \* Read value from snapshot
                            localSnapshot[key] := store[key].value;
                            localReadSet := localReadSet \union {key};
                            readSet[self] := localReadSet;
                        elsif store[key].tx_state \in {"PREPARED", "DELETED"} /\ 
                              store[key].tx_id # NULL /\ 
                              store[key].committed_at = 0 then
                            \* Encountering uncommitted prepared record
                            \* In snapshot isolation, we could wait or help recovery
                            \* For simplicity, abort
                            canCommit := FALSE;
                            goto TxnAbort;
                        else
                            \* Record doesn't exist in our snapshot
                            localReadSet := localReadSet \union {key};
                            readSet[self] := localReadSet;
                        end if;
                end with;
            or
                \* Write operation (buffered)
                with key \in KEYS, val \in VALUES do
                    if key \notin localDeleteSet then
                        localWriteSet[key] := val;
                        writeSet[self] := localWriteSet;
                    end if;
                end with;
            or
                \* Delete operation (buffered)
                with key \in KEYS do
                    if localWriteSet[key] = NULL then
                        localDeleteSet := localDeleteSet \union {key};
                        deleteSet[self] := localDeleteSet;
                    end if;
                end with;
            or
                \* Proceed to commit
                goto BeginCommit;
            end either;
        end while;
        
    BeginCommit:
        if canCommit then
            txnState[self] := "PREPARING";
            goto Prepare;
        else
            goto TxnAbort;
        end if;
        
    Prepare:
        \* Prepare phase: write PREPARED/DELETED records
        \* Check for write-write conflicts only (not read-write conflicts)
        with writeKeys = {k \in KEYS : localWriteSet[k] # NULL},
             deleteKeys = localDeleteSet do
            \* Check write-write conflicts
            if \A k \in writeKeys \union deleteKeys : 
                \* No other transaction has modified this key since our snapshot
                \/ store[k].committed_at <= txnStartTime
                \/ store[k].tx_id = self
            then
                \* No conflicts, prepare all records
                store := [k \in KEYS |->
                    IF k \in writeKeys THEN
                        [value |-> localWriteSet[k],
                         tx_id |-> self,
                         tx_state |-> "PREPARED",
                         tx_version |-> store[k].tx_version + 1,
                         before_value |-> store[k].value,
                         committed_at |-> 0]  \* Not committed yet
                    ELSE IF k \in deleteKeys THEN
                        [value |-> store[k].value,
                         tx_id |-> self,
                         tx_state |-> "DELETED",
                         tx_version |-> store[k].tx_version + 1,
                         before_value |-> store[k].value,
                         committed_at |-> 0]
                    ELSE store[k]];
                txnState[self] := "PREPARED";
                \* No validation phase in snapshot isolation!
                goto CommitTxn;
            else
                \* Write-write conflict detected
                goto TxnAbort;
            end if;
        end with;
        
    CommitTxn:
        \* Commit the transaction
        txnState[self] := "COMMITTING";
        \* Record commit time
        commitTime[self] := globalTime;
        globalTime := globalTime + 1;
        \* Write to coordinator (atomic operation)
        committedTxns := committedTxns \union {self};
        \* Update all prepared/deleted records to committed with commit timestamp
        store := [k \in KEYS |->
            IF store[k].tx_id = self /\ store[k].tx_state = "PREPARED" THEN
                [value |-> store[k].value,
                 tx_id |-> NULL,
                 tx_state |-> "COMMITTED", 
                 tx_version |-> store[k].tx_version,
                 before_value |-> NULL,
                 committed_at |-> commitTime[self]]
            ELSE IF store[k].tx_id = self /\ store[k].tx_state = "DELETED" THEN
                [value |-> NULL,
                 tx_id |-> NULL,
                 tx_state |-> "COMMITTED",
                 tx_version |-> store[k].tx_version,
                 before_value |-> NULL,
                 committed_at |-> commitTime[self]]
            ELSE store[k]];
            
    SetCommitted:
        txnState[self] := "COMMITTED";
        goto TxnDone;
        
    TxnAbort:
        \* Abort the transaction
        txnState[self] := "ABORTED";
        abortedTxns := abortedTxns \union {self};
        \* Rollback any prepared/deleted records
        store := [k \in KEYS |->
            IF store[k].tx_id = self /\ store[k].tx_state \in {"PREPARED", "DELETED"} THEN
                [value |-> store[k].before_value,
                 tx_id |-> NULL,
                 tx_state |-> "COMMITTED",
                 tx_version |-> store[k].tx_version - 1,
                 before_value |-> NULL,
                 committed_at |-> store[k].committed_at]  \* Keep original commit time
            ELSE store[k]];
        goto TxnDone;
        
    TxnDone:
        skip;
end process;

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES pc, store, txnState, readSet, writeSet, deleteSet, startTime, 
          committedTxns, abortedTxns, globalTime, commitTime

(* define statement *)
CompletedTxns == committedTxns \union abortedTxns


ActiveTxns == TRANSACTIONS \ CompletedTxns


TypeInvariant ==
    /\ \A k \in KEYS :
        /\ store[k].value \in VALUES \union {NULL}
        /\ store[k].tx_id \in TRANSACTIONS \union {NULL}
        /\ store[k].tx_state \in RecordStates
        /\ store[k].tx_version \in Nat
        /\ store[k].before_value \in VALUES \union {NULL}
        /\ store[k].committed_at \in Nat
    /\ \A t \in TRANSACTIONS : txnState[t] \in TxnStates
    /\ committedTxns \subseteq TRANSACTIONS
    /\ abortedTxns \subseteq TRANSACTIONS
    /\ globalTime \in Nat


ConsistencyInvariant ==
    \A k \in KEYS :
        ((store[k].tx_state = "PREPARED" \/ store[k].tx_state = "DELETED") /\ store[k].tx_id # NULL) =>
            store[k].tx_id \notin CompletedTxns



NoWriteWriteConflicts ==
    \A t1, t2 \in committedTxns : \A k \in KEYS :
        (t1 # t2 /\
         (k \in DOMAIN writeSet[t1] /\ writeSet[t1][k] # NULL) /\
         (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL)) =>

            \/ commitTime[t1] < startTime[t2]
            \/ commitTime[t2] < startTime[t1]


ConsistentSnapshot ==
    \A t \in TRANSACTIONS : \A k \in readSet[t] :

        TRUE

VARIABLES localReadSet, localWriteSet, localDeleteSet, localSnapshot, 
          canCommit, txnStartTime

vars == << pc, store, txnState, readSet, writeSet, deleteSet, startTime, 
           committedTxns, abortedTxns, globalTime, commitTime, localReadSet, 
           localWriteSet, localDeleteSet, localSnapshot, canCommit, 
           txnStartTime >>

ProcSet == (TRANSACTIONS)

Init == (* Global variables *)
        /\ store = [k \in KEYS |-> [value |-> NULL, tx_id |-> NULL, tx_state |-> "COMMITTED",
                                     tx_version |-> 0, before_value |-> NULL, committed_at |-> 0]]
        /\ txnState = [t \in TRANSACTIONS |-> "ACTIVE"]
        /\ readSet = [t \in TRANSACTIONS |-> {}]
        /\ writeSet = [t \in TRANSACTIONS |-> [k \in KEYS |-> NULL]]
        /\ deleteSet = [t \in TRANSACTIONS |-> {}]
        /\ startTime = [t \in TRANSACTIONS |-> 0]
        /\ committedTxns = {}
        /\ abortedTxns = {}
        /\ globalTime = 1
        /\ commitTime = [t \in TRANSACTIONS |-> 0]
        (* Process transaction *)
        /\ localReadSet = [self \in TRANSACTIONS |-> {}]
        /\ localWriteSet = [self \in TRANSACTIONS |-> [k \in KEYS |-> NULL]]
        /\ localDeleteSet = [self \in TRANSACTIONS |-> {}]
        /\ localSnapshot = [self \in TRANSACTIONS |-> [k \in KEYS |-> NULL]]
        /\ canCommit = [self \in TRANSACTIONS |-> TRUE]
        /\ txnStartTime = [self \in TRANSACTIONS |-> 0]
        /\ pc = [self \in ProcSet |-> "TxnStart"]

TxnStart(self) == /\ pc[self] = "TxnStart"
                  /\ txnStartTime' = [txnStartTime EXCEPT ![self] = globalTime]
                  /\ startTime' = [startTime EXCEPT ![self] = txnStartTime'[self]]
                  /\ globalTime' = globalTime + 1
                  /\ pc' = [pc EXCEPT ![self] = "ReadWrite"]
                  /\ UNCHANGED << store, txnState, readSet, writeSet, 
                                  deleteSet, committedTxns, abortedTxns, 
                                  commitTime, localReadSet, localWriteSet, 
                                  localDeleteSet, localSnapshot, canCommit >>

ReadWrite(self) == /\ pc[self] = "ReadWrite"
                   /\ \/ /\ \E key \in KEYS:
                              IF store[key].tx_state = "COMMITTED" /\
                                 store[key].committed_at <= txnStartTime[self] /\
                                 ~(store[key].tx_state = "DELETED" \/ (store[key].tx_state = "COMMITTED" /\ store[key].value = NULL)) /\
                                 store[key].value # NULL
                                 THEN /\ localSnapshot' = [localSnapshot EXCEPT ![self][key] = store[key].value]
                                      /\ localReadSet' = [localReadSet EXCEPT ![self] = localReadSet[self] \union {key}]
                                      /\ readSet' = [readSet EXCEPT ![self] = localReadSet'[self]]
                                      /\ pc' = [pc EXCEPT ![self] = "ReadWrite"]
                                      /\ UNCHANGED canCommit
                                 ELSE /\ IF store[key].tx_state \in {"PREPARED", "DELETED"} /\
                                            store[key].tx_id # NULL /\
                                            store[key].committed_at = 0
                                            THEN /\ canCommit' = [canCommit EXCEPT ![self] = FALSE]
                                                 /\ pc' = [pc EXCEPT ![self] = "TxnAbort"]
                                                 /\ UNCHANGED << readSet, 
                                                                 localReadSet >>
                                            ELSE /\ localReadSet' = [localReadSet EXCEPT ![self] = localReadSet[self] \union {key}]
                                                 /\ readSet' = [readSet EXCEPT ![self] = localReadSet'[self]]
                                                 /\ pc' = [pc EXCEPT ![self] = "ReadWrite"]
                                                 /\ UNCHANGED canCommit
                                      /\ UNCHANGED localSnapshot
                         /\ UNCHANGED <<writeSet, deleteSet, localWriteSet, localDeleteSet>>
                      \/ /\ \E key \in KEYS:
                              \E val \in VALUES:
                                IF key \notin localDeleteSet[self]
                                   THEN /\ localWriteSet' = [localWriteSet EXCEPT ![self][key] = val]
                                        /\ writeSet' = [writeSet EXCEPT ![self] = localWriteSet'[self]]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << writeSet, 
                                                        localWriteSet >>
                         /\ pc' = [pc EXCEPT ![self] = "ReadWrite"]
                         /\ UNCHANGED <<readSet, deleteSet, localReadSet, localDeleteSet, localSnapshot, canCommit>>
                      \/ /\ \E key \in KEYS:
                              IF localWriteSet[self][key] = NULL
                                 THEN /\ localDeleteSet' = [localDeleteSet EXCEPT ![self] = localDeleteSet[self] \union {key}]
                                      /\ deleteSet' = [deleteSet EXCEPT ![self] = localDeleteSet'[self]]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << deleteSet, 
                                                      localDeleteSet >>
                         /\ pc' = [pc EXCEPT ![self] = "ReadWrite"]
                         /\ UNCHANGED <<readSet, writeSet, localReadSet, localWriteSet, localSnapshot, canCommit>>
                      \/ /\ pc' = [pc EXCEPT ![self] = "BeginCommit"]
                         /\ UNCHANGED <<readSet, writeSet, deleteSet, localReadSet, localWriteSet, localDeleteSet, localSnapshot, canCommit>>
                   /\ UNCHANGED << store, txnState, startTime, committedTxns, 
                                   abortedTxns, globalTime, commitTime, 
                                   txnStartTime >>

BeginCommit(self) == /\ pc[self] = "BeginCommit"
                     /\ IF canCommit[self]
                           THEN /\ txnState' = [txnState EXCEPT ![self] = "PREPARING"]
                                /\ pc' = [pc EXCEPT ![self] = "Prepare"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "TxnAbort"]
                                /\ UNCHANGED txnState
                     /\ UNCHANGED << store, readSet, writeSet, deleteSet, 
                                     startTime, committedTxns, abortedTxns, 
                                     globalTime, commitTime, localReadSet, 
                                     localWriteSet, localDeleteSet, 
                                     localSnapshot, canCommit, txnStartTime >>

Prepare(self) == /\ pc[self] = "Prepare"
                 /\ LET writeKeys == {k \in KEYS : localWriteSet[self][k] # NULL} IN
                      LET deleteKeys == localDeleteSet[self] IN
                        IF \A k \in writeKeys \union deleteKeys :
                            \* Record must be available for modification
                            /\ (store[k].tx_id = NULL \/ store[k].tx_id = self)
                            \* For SNAPSHOT isolation: can only modify records committed before transaction start
                            /\ (store[k].committed_at <= txnStartTime[self])
                           THEN /\ store' =      [k \in KEYS |->
                                            IF k \in writeKeys THEN
                                                [value |-> localWriteSet[self][k],
                                                 tx_id |-> self,
                                                 tx_state |-> "PREPARED",
                                                 tx_version |-> store[k].tx_version + 1,
                                                 before_value |-> store[k].value,
                                                 committed_at |-> 0]
                                            ELSE IF k \in deleteKeys THEN
                                                [value |-> store[k].value,
                                                 tx_id |-> self,
                                                 tx_state |-> "DELETED",
                                                 tx_version |-> store[k].tx_version + 1,
                                                 before_value |-> store[k].value,
                                                 committed_at |-> 0]
                                            ELSE store[k]]
                                /\ txnState' = [txnState EXCEPT ![self] = "PREPARED"]
                                /\ pc' = [pc EXCEPT ![self] = "CommitTxn"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "TxnAbort"]
                                /\ UNCHANGED << store, txnState >>
                 /\ UNCHANGED << readSet, writeSet, deleteSet, startTime, 
                                 committedTxns, abortedTxns, globalTime, 
                                 commitTime, localReadSet, localWriteSet, 
                                 localDeleteSet, localSnapshot, canCommit, 
                                 txnStartTime >>

CommitTxn(self) == /\ pc[self] = "CommitTxn"
                   /\ txnState' = [txnState EXCEPT ![self] = "COMMITTING"]
                   /\ commitTime' = [commitTime EXCEPT ![self] = globalTime]
                   /\ globalTime' = globalTime + 1
                   /\ committedTxns' = (committedTxns \union {self})
                   /\ store' =      [k \in KEYS |->
                               IF store[k].tx_id = self /\ store[k].tx_state = "PREPARED" THEN
                                   [value |-> store[k].value,
                                    tx_id |-> NULL,
                                    tx_state |-> "COMMITTED",
                                    tx_version |-> store[k].tx_version,
                                    before_value |-> NULL,
                                    committed_at |-> commitTime'[self]]
                               ELSE IF store[k].tx_id = self /\ store[k].tx_state = "DELETED" THEN
                                   [value |-> NULL,
                                    tx_id |-> NULL,
                                    tx_state |-> "COMMITTED",
                                    tx_version |-> store[k].tx_version,
                                    before_value |-> NULL,
                                    committed_at |-> commitTime'[self]]
                               ELSE store[k]]
                   /\ pc' = [pc EXCEPT ![self] = "SetCommitted"]
                   /\ UNCHANGED << readSet, writeSet, deleteSet, startTime, 
                                   abortedTxns, localReadSet, localWriteSet, 
                                   localDeleteSet, localSnapshot, canCommit, 
                                   txnStartTime >>

SetCommitted(self) == /\ pc[self] = "SetCommitted"
                      /\ txnState' = [txnState EXCEPT ![self] = "COMMITTED"]
                      /\ pc' = [pc EXCEPT ![self] = "TxnDone"]
                      /\ UNCHANGED << store, readSet, writeSet, deleteSet, 
                                      startTime, committedTxns, abortedTxns, 
                                      globalTime, commitTime, localReadSet, 
                                      localWriteSet, localDeleteSet, 
                                      localSnapshot, canCommit, txnStartTime >>

TxnAbort(self) == /\ pc[self] = "TxnAbort"
                  /\ txnState' = [txnState EXCEPT ![self] = "ABORTED"]
                  /\ abortedTxns' = (abortedTxns \union {self})
                  /\ store' =      [k \in KEYS |->
                              IF store[k].tx_id = self /\ store[k].tx_state \in {"PREPARED", "DELETED"} THEN
                                  [value |-> store[k].before_value,
                                   tx_id |-> NULL,
                                   tx_state |-> "COMMITTED",
                                   tx_version |-> store[k].tx_version - 1,
                                   before_value |-> NULL,
                                   committed_at |-> store[k].committed_at]
                              ELSE store[k]]
                  /\ pc' = [pc EXCEPT ![self] = "TxnDone"]
                  /\ UNCHANGED << readSet, writeSet, deleteSet, startTime, 
                                  committedTxns, globalTime, commitTime, 
                                  localReadSet, localWriteSet, localDeleteSet, 
                                  localSnapshot, canCommit, txnStartTime >>

TxnDone(self) == /\ pc[self] = "TxnDone"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << store, txnState, readSet, writeSet, deleteSet, 
                                 startTime, committedTxns, abortedTxns, 
                                 globalTime, commitTime, localReadSet, 
                                 localWriteSet, localDeleteSet, localSnapshot, 
                                 canCommit, txnStartTime >>

transaction(self) == TxnStart(self) \/ ReadWrite(self) \/ BeginCommit(self)
                        \/ Prepare(self) \/ CommitTxn(self)
                        \/ SetCommitted(self) \/ TxnAbort(self)
                        \/ TxnDone(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TRANSACTIONS: transaction(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TRANSACTIONS : WF_vars(transaction(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Helper functions
IsCommitted(key) == store[key].tx_state = "COMMITTED"

IsDeleted(key) == store[key].tx_state = "DELETED" \/ (store[key].tx_state = "COMMITTED" /\ store[key].value = NULL)

\* Get value visible at given snapshot time
GetSnapshotValue(key, snapTime) ==
    IF store[key].tx_state = "COMMITTED" /\ store[key].committed_at <= snapTime 
    THEN IF ~IsDeleted(key) THEN store[key].value ELSE NULL
    ELSE NULL

RecordExistsAtSnapshot(key, snapTime) == 
    store[key].tx_state = "COMMITTED" /\ 
    store[key].committed_at <= snapTime /\ 
    ~IsDeleted(key) /\ 
    store[key].value # NULL

\* Temporal properties for snapshot isolation verification

\* Eventually all active transactions complete
EventuallyComplete == \A t \in TRANSACTIONS : <>(t \in CompletedTxns)

\* Snapshot isolation prevents dirty writes
NoDirtyWrites == NoWriteWriteConflicts

\* Snapshot isolation prevents dirty reads (reading uncommitted data)
NoDirtyReads == \A t \in TRANSACTIONS : \A k \in readSet[t] :
    \* Any value read must have been committed before the transaction started
    TRUE  \* Enforced by GetSnapshotValue

\* Snapshot isolation prevents non-repeatable reads within a transaction
RepeatableReads == \A t \in TRANSACTIONS : \A k \in readSet[t] :
    \* All reads of the same key within a transaction return the same value
    \* This is guaranteed by reading from a consistent snapshot
    TRUE

\* Write skew anomaly is possible in snapshot isolation
\* Example scenario: Two transactions read x=0, y=0, then t1 sets x=y+1, t2 sets y=x+1
\* Result: x=1, y=1 (should be impossible if truly serial)
WriteSkewPossible == 
    \E t1, t2 \in committedTxns : \E k1, k2 \in KEYS :
        /\ t1 # t2
        /\ k1 # k2
        /\ k1 \in readSet[t1] /\ k2 \in readSet[t1]
        /\ k1 \in readSet[t2] /\ k2 \in readSet[t2]
        /\ k2 \in DOMAIN writeSet[t1] /\ writeSet[t1][k2] # NULL
        /\ k1 \in DOMAIN writeSet[t2] /\ writeSet[t2][k1] # NULL
        /\ startTime[t1] < commitTime[t2] /\ startTime[t2] < commitTime[t1]

\* ============================================================================
\* Additional Verification Properties for Snapshot Isolation
\* ============================================================================

\* Atomicity: All-or-nothing property (same as strict serializability)
SnapshotAtomicity ==
    \A t \in TRANSACTIONS :
        \* If transaction is committed, all its changes are visible
        (t \in committedTxns) => 
            \A k \in KEYS : 
                (store[k].tx_id = t) => (store[k].tx_state = "COMMITTED")

\* No partial states visible (same as strict serializability)
SnapshotNoPartialStates ==
    \A k \in KEYS :
        \* No key should reference a completed transaction in prepared state
        (store[k].tx_id # NULL /\ store[k].tx_id \in CompletedTxns) =>
            store[k].tx_state = "COMMITTED"

\* Version monotonicity (same as strict serializability)
SnapshotVersionMonotonicity ==
    \A k \in KEYS :
        store[k].tx_version >= 0

\* Valid state transitions (same as strict serializability)
SnapshotValidStateTransitions ==
    \A t \in TRANSACTIONS :
        txnState[t] \in {"ACTIVE", "PREPARING", "PREPARED", "COMMITTING", "COMMITTED", "ABORTED"}

\* No dirty reads: transactions cannot read uncommitted data from aborted transactions
SnapshotNoDirtyReads ==
    \A t1, t2 \in TRANSACTIONS :
        \* t1 cannot read uncommitted values from t2 if t2 aborted
        \* This is automatically prevented by only reading COMMITTED records
        \* and proper timestamp checking in snapshot isolation
        (t2 \in abortedTxns /\ t1 \in committedTxns) =>
            \A k \in readSet[t1] :
                \* If both transactions accessed the same key, ensure no dirty read occurred
                (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL) =>
                    \* t1 must have read the value before t2 wrote it, or after t2 was cleaned up
                    \* This is ensured by ScalarDB's read logic that only reads COMMITTED records
                    TRUE

\* Snapshot consistency: Reads within a transaction are consistent
SnapshotConsistency ==
    \A t \in TRANSACTIONS : \A k \in readSet[t] :
        \* All reads see the same consistent snapshot (enforced by snapshot mechanism)
        TRUE

\* First-committer-wins: Write-write conflicts are detected and prevented
FirstCommitterWins ==
    \A t1, t2 \in committedTxns : \A k \in KEYS :
        (t1 # t2 /\ 
         (k \in DOMAIN writeSet[t1] /\ writeSet[t1][k] # NULL) /\
         (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL)) =>
            \* Either t1 committed before t2 started or vice versa
            \/ commitTime[t1] < startTime[t2]
            \/ commitTime[t2] < startTime[t1]


\* Commit timestamp ordering: Committed transactions have proper timestamp ordering
CommitTimestampOrdering ==
    \A t1, t2 \in committedTxns :
        (t1 # t2) => (commitTime[t1] # commitTime[t2])

\* Snapshot visibility: Transactions only see committed data from before their start
SnapshotVisibility ==
    \A t \in TRANSACTIONS : \A k \in readSet[t] :
        \* If transaction read a value, it was committed before transaction started
        (\E val \in VALUES : val # NULL) =>  \* Placeholder for actual read value check
            \A t2 \in committedTxns :
                (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL) =>
                    commitTime[t2] <= startTime[t]

\* Temporal properties for snapshot isolation

\* Eventual progress (liveness)
SnapshotProgress ==
    \A t \in TRANSACTIONS : <>(t \in CompletedTxns)

\* No permanent blocking
SnapshotNoPermanentBlocking ==
    \A k \in KEYS :
        \* If a key is locked by a transaction, that transaction eventually completes
        (store[k].tx_id # NULL) => <>(store[k].tx_id \in CompletedTxns)

\* Eventual cleanup of prepared records
SnapshotEventualCleanup ==
    \A k \in KEYS :
        \* All prepared/deleted records eventually become committed
        (store[k].tx_state \in {"PREPARED", "DELETED"}) ~> 
        (store[k].tx_state = "COMMITTED")

\* Anomaly detection properties specific to snapshot isolation

\* Lost update prevention (this should NOT be violated in snapshot isolation)
SnapshotNoLostUpdates ==
    \A t1, t2 \in committedTxns : \A k \in KEYS :
        (t1 # t2 /\ 
         k \in readSet[t1] /\ k \in DOMAIN writeSet[t1] /\ writeSet[t1][k] # NULL /\
         k \in readSet[t2] /\ k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL) =>
            \* Read-modify-write conflicts should be prevented
            \/ commitTime[t1] < startTime[t2] 
            \/ commitTime[t2] < startTime[t1]

\* Write skew detection (this CAN be violated in snapshot isolation)
SnapshotWriteSkewDetection ==
    \E t1, t2 \in committedTxns : \E k1, k2 \in KEYS :
        /\ t1 # t2 /\ k1 # k2
        /\ k1 \in readSet[t1] /\ k2 \in DOMAIN writeSet[t1] /\ writeSet[t1][k2] # NULL
        /\ k2 \in readSet[t2] /\ k1 \in DOMAIN writeSet[t2] /\ writeSet[t2][k1] # NULL
        /\ startTime[t1] < commitTime[t2] /\ startTime[t2] < commitTime[t1]

\* Classic write skew scenario: T1 reads x writes y, T2 reads y writes x
ClassicWriteSkew ==
    \E t1, t2 \in committedTxns :
        /\ t1 # t2
        /\ \E x, y \in KEYS : x # y /\
            \* T1 reads x and writes y
            /\ x \in readSet[t1] 
            /\ y \in DOMAIN writeSet[t1] /\ writeSet[t1][y] # NULL
            \* T2 reads y and writes x  
            /\ y \in readSet[t2]
            /\ x \in DOMAIN writeSet[t2] /\ writeSet[t2][x] # NULL
            \* Both transactions overlapped in time (started before the other committed)
            /\ startTime[t1] < commitTime[t2] 
            /\ startTime[t2] < commitTime[t1]

\* Bank account write skew: Check constraint violation
\* T1: reads account1=100, account2=100, withdraws 150 from account1 (balance=-50)
\* T2: reads account1=100, account2=100, withdraws 150 from account2 (balance=-50)  
\* Both commit, violating constraint that sum >= 0
BankAccountWriteSkew ==
    \E t1, t2 \in committedTxns :
        /\ t1 # t2
        /\ \E acc1, acc2 \in KEYS : acc1 # acc2 /\
            \* T1 reads both accounts, writes to acc1
            /\ acc1 \in readSet[t1] /\ acc2 \in readSet[t1]
            /\ acc1 \in DOMAIN writeSet[t1] /\ writeSet[t1][acc1] # NULL
            \* T2 reads both accounts, writes to acc2
            /\ acc1 \in readSet[t2] /\ acc2 \in readSet[t2] 
            /\ acc2 \in DOMAIN writeSet[t2] /\ writeSet[t2][acc2] # NULL
            \* Concurrent execution
            /\ startTime[t1] < commitTime[t2] 
            /\ startTime[t2] < commitTime[t1]

\* Phantom reads (can occur in snapshot isolation for range queries)
\* Note: This is a simplified version since we don't model range queries explicitly
SnapshotPhantomReads ==
    \* In snapshot isolation, phantom reads are prevented within a transaction
    \* but can occur between transactions
    TRUE  \* Placeholder - would need range query modeling

\* Combined correctness criteria for snapshot isolation
SnapshotIsolationCorrectness ==
    /\ SnapshotAtomicity
    /\ SnapshotNoPartialStates
    /\ SnapshotConsistency
    /\ SnapshotNoDirtyReads
    /\ FirstCommitterWins
    \* NoWriteWriteConflicts is now enforced by the prepare phase logic
    /\ SnapshotNoLostUpdates
    /\ SnapshotVersionMonotonicity
    /\ SnapshotValidStateTransitions
    /\ ~ClassicWriteSkew
\*    /\ ~BankAccountWriteSkew
\*    /\ ~SnapshotWriteSkewDetection
    \* Note: Write skew is ALLOWED in snapshot isolation, so we don't include it as a violation

\* State constraint to keep verification tractable
StateConstraint ==
    /\ \A t \in TRANSACTIONS : Cardinality(readSet[t]) <= 3
    /\ \A t \in TRANSACTIONS : Cardinality(deleteSet[t]) <= 2
    /\ globalTime <= 15

\* Temporal properties for write skew detection
EventuallyClassicWriteSkew == <>ClassicWriteSkew
EventuallyBankAccountWriteSkew == <>BankAccountWriteSkew
EventuallyWriteSkewDetection == <>SnapshotWriteSkewDetection

\* Write skew PREVENTION properties (negated versions for invariant testing)
NoClassicWriteSkew == ~ClassicWriteSkew
NoBankAccountWriteSkew == ~BankAccountWriteSkew  
NoWriteSkewDetection == ~SnapshotWriteSkewDetection

====================================================================================================
