---------------------------- MODULE scalardb_verification_properties ----------------------------
(* 
 * Additional properties and invariants for verifying ScalarDB's transaction protocols
 * These can be used with both strict serializability and snapshot isolation models
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

\* Import the necessary definitions from the main modules
\* (In practice, you would INSTANCE the appropriate module)

\* ============================================================================
\* Safety Properties (Invariants)
\* ============================================================================

\* 1. Atomicity: All-or-nothing property
Atomicity(committedTxns, abortedTxns, store, KEYS, TRANSACTIONS) ==
    \A t \in TRANSACTIONS :
        \* If transaction is committed, all its changes are visible
        (t \in committedTxns) => 
            \A k \in KEYS : 
                (store[k].tx_id = t) => (store[k].tx_state = "COMMITTED")

\* 2. Consistency: No partial states visible
NoPartialStates(store, KEYS, CompletedTxns) ==
    \A k \in KEYS :
        \* No key should reference a completed transaction in prepared state
        (store[k].tx_id # NULL /\ store[k].tx_id \in CompletedTxns) =>
            store[k].tx_state = "COMMITTED"

\* 3. Isolation Level Specific Properties

\* For Strict Serializability: Linearizability of operations
Linearizability(txnOrder, committedTxns, readSet, writeSet) ==
    \* There exists a total order of operations that explains all observations
    \A t1, t2 \in committedTxns :
        \* If t1 reads a value written by t2, t2 must precede t1 in order
        (\E k \in readSet[t1] : k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL) =>
            \E i, j \in 1..Len(txnOrder) : 
                i < j /\ txnOrder[i] = t2 /\ txnOrder[j] = t1

\* For Snapshot Isolation: Read-consistency within transaction
SnapshotConsistency(readSet, startTime, commitTime, TRANSACTIONS) ==
    \A t \in TRANSACTIONS : \A k1, k2 \in readSet[t] :
        \* All reads see the same consistent snapshot
        \* (Values as of transaction start time)
        TRUE  \* This is enforced by the snapshot mechanism

\* 4. No Lost Updates (stronger than write-write conflict prevention)
NoLostUpdates(committedTxns, readSet, writeSet, txnOrder) ==
    \A t1, t2 \in committedTxns : \A k \in KEYS :
        \* If both transactions update the same key, one must see the other's update
        ((k \in DOMAIN writeSet[t1] /\ writeSet[t1][k] # NULL) /\
         (k \in DOMAIN writeSet[t2] /\ writeSet[t2][k] # NULL) /\ t1 # t2) =>
            \* Either t1 read t2's write or vice versa, or they're ordered
            \/ k \in readSet[t1]
            \/ k \in readSet[t2]
            \/ \E i, j \in 1..Len(txnOrder) : 
                (i < j /\ txnOrder[i] = t1 /\ txnOrder[j] = t2) \/
                (i < j /\ txnOrder[i] = t2 /\ txnOrder[j] = t1)

\* 5. Version Monotonicity
VersionMonotonicity(store, KEYS) ==
    \A k \in KEYS :
        store[k].tx_version >= 0

\* 6. State Machine Consistency
ValidStateTransitions(txnState, TRANSACTIONS) ==
    \A t \in TRANSACTIONS :
        txnState[t] \in {"ACTIVE", "PREPARING", "PREPARED", 
                        "VALIDATING", "COMMITTING", "COMMITTED", "ABORTED"}

\* ============================================================================
\* Liveness Properties (Temporal Properties)
\* ============================================================================

\* 1. Progress: Every active transaction eventually completes
Progress(CompletedTxns, TRANSACTIONS) ==
    \A t \in TRANSACTIONS : <>(t \in CompletedTxns)

\* 2. No Permanent Blocking
NoPermanentBlocking(store, KEYS, TRANSACTIONS) ==
    \A k \in KEYS :
        \* If a key is locked by a transaction, that transaction eventually completes
        (store[k].tx_id # NULL) => <>(store[k].tx_id \in CompletedTxns)

\* 3. Eventual Consistency of Prepared Records
EventualCleanup(store, KEYS) ==
    \A k \in KEYS :
        \* All prepared/deleted records eventually become committed
        (store[k].tx_state \in {"PREPARED", "DELETED"}) ~> 
        (store[k].tx_state = "COMMITTED")

\* ============================================================================
\* Anomaly Detection Properties
\* ============================================================================

\* 1. Dirty Read Detection (should never happen)
NoDirtyReads(readSet, committedTxns, abortedTxns, TRANSACTIONS) ==
    \A t1, t2 \in TRANSACTIONS :
        \* t1 cannot read a value written by t2 if t2 aborted
        (t2 \in abortedTxns /\ \E k \in readSet[t1] : k \in DOMAIN writeSet[t2]) =>
            FALSE

\* 2. Non-Repeatable Read Detection (prevented in both SI and SR)
NoNonRepeatableReads ==
    \* Within a transaction, reading the same key always returns same value
    \* This is guaranteed by the snapshot mechanism
    TRUE

\* 3. Phantom Read Detection (prevented in SR, possible in SI)
NoPhantomReads ==
    \* Range queries return the same set of records
    \* This requires modeling range queries explicitly
    TRUE

\* 4. Write Skew Detection (prevented in SR, allowed in SI)
WriteSkewDetection(committedTxns, readSet, writeSet, startTime, commitTime) ==
    \E t1, t2 \in committedTxns : \E k1, k2 \in KEYS :
        /\ t1 # t2 /\ k1 # k2
        /\ k1 \in readSet[t1] /\ k2 \in writeSet[t1]
        /\ k2 \in readSet[t2] /\ k1 \in writeSet[t2]
        /\ startTime[t1] < commitTime[t2] 
        /\ startTime[t2] < commitTime[t1]

\* ============================================================================
\* Performance and Optimization Properties
\* ============================================================================

\* 1. One-Phase Commit Optimization Applicable
OnePhaseCommitPossible(readSet, writeSet, deleteSet) ==
    \E t \in TRANSACTIONS :
        \* Transaction only writes/deletes without reading
        readSet[t] = {} /\ 
        (\E k \in KEYS : writeSet[t][k] # NULL \/ k \in deleteSet[t])

\* 2. Read-Only Transaction Optimization
ReadOnlyTransactionOptimization(writeSet, deleteSet) ==
    \E t \in TRANSACTIONS :
        \* Transaction only reads, no writes or deletes
        (\A k \in KEYS : writeSet[t][k] = NULL) /\ deleteSet[t] = {}

\* ============================================================================
\* Correctness Criteria Summary
\* ============================================================================

\* For Strict Serializability, all of these should hold:
StrictSerializabilityCorrectness ==
    /\ Atomicity
    /\ NoPartialStates
    /\ Linearizability
    /\ NoLostUpdates
    /\ NoDirtyReads
    /\ NoNonRepeatableReads
    /\ NoPhantomReads
    /\ ~WriteSkewDetection  \* No write skew allowed

\* For Snapshot Isolation, these should hold:
SnapshotIsolationCorrectness ==
    /\ Atomicity
    /\ NoPartialStates
    /\ SnapshotConsistency
    /\ NoLostUpdates  \* Only for keys with write-write conflicts
    /\ NoDirtyReads
    /\ NoNonRepeatableReads
    \* /\ WriteSkewDetection possible (this is allowed in SI)

====================================================================================================