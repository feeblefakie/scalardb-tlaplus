# TLA+ Specification Design for ScalarDB

This document explains the design and implementation details of the TLA+ formal specification for ScalarDB's Consensus Commit protocol.

## Overview

The specification models ScalarDB's Consensus Commit protocol, which provides ACID transactions with strict serializability across distributed databases. The model focuses on the core transaction processing algorithm with SERIALIZABLE isolation level, including support for read, write, and delete operations.

## Model Architecture

### State Variables

The specification uses the following state variables to model the system:

#### Storage State
- **`store`**: A mapping from keys to records, where each record contains:
  - `value`: The data value (can be NULL for deleted records)
  - `tx_id`: ID of the transaction that last modified this record
  - `tx_state`: State of the record ("COMMITTED", "PREPARED", "DELETED")
  - `tx_version`: Version number for optimistic concurrency control
  - `before_value`: Previous value, used for rollback during abort

#### Transaction Manager State
- **`txnState`**: Current state of each transaction ("ACTIVE", "PREPARING", "PREPARED", "VALIDATING", "COMMITTING", "COMMITTED", "ABORTED")
- **`readSet`**: Set of keys read by each transaction
- **`writeSet`**: Map of keys to values to be written by each transaction
- **`deleteSet`**: Set of keys to be deleted by each transaction

#### Global State
- **`committedTxns`**: Set of successfully committed transactions
- **`abortedTxns`**: Set of aborted transactions
- **`txnOrder`**: Sequence recording the commit order for serializability verification

### Transaction Lifecycle

The PlusCal algorithm models each transaction as a process with the following phases:

```
TxnStart → ReadWrite* → BeginCommit → Prepare → Validate → CommitTxn → SetCommitted → TxnDone
                ↓                         ↓          ↓           ↓
                └─────────────────────────┴──────────┴───────────┴────→ TxnAbort → TxnDone
```

#### 1. **TxnStart**
- Transaction begins in ACTIVE state
- Initializes local read/write/delete sets

#### 2. **ReadWrite** (Loop)
- Models the application logic phase where transactions perform operations
- Non-deterministically chooses between:
  - **Read**: Reads a key and adds to read set
  - **Write**: Buffers a write operation
  - **Delete**: Buffers a delete operation
  - **Proceed**: Moves to commit phase

#### 3. **BeginCommit**
- Transitions to PREPARING state
- Decides whether to proceed with commit or abort

#### 4. **Prepare**
- Core phase implementing two-phase locking
- Performs conflict detection:
  - For writes: Checks if key was read and unchanged, or is new
  - For deletes: Checks if key was read and unchanged
- If no conflicts: Writes PREPARED/DELETED records
- If conflicts detected: Aborts transaction

#### 5. **Validate**
- Implements validation for SERIALIZABLE isolation
- Re-reads all keys in read set
- Ensures no concurrent modifications
- Critical for preventing phantom reads and ensuring serializability

#### 6. **CommitTxn**
- Atomically commits the transaction
- Updates coordinator state (adds to committedTxns)
- Records in txnOrder for serializability tracking
- Converts all PREPARED records to COMMITTED
- Converts all DELETED records to NULL values

#### 7. **TxnAbort**
- Handles transaction rollback
- Restores before_value for all modified records
- Resets version numbers
- Adds transaction to abortedTxns set

## Safety Properties

### TypeInvariant
Ensures well-formedness of all state variables:
- Record fields have correct types
- Transaction states are valid
- Sets contain only valid transaction IDs

### ConsistencyInvariant
Key safety property ensuring:
- No record remains in PREPARED/DELETED state after its transaction completes
- Prevents dirty reads and inconsistent states

### NoWriteDeleteConflict
Ensures transaction consistency:
- A transaction cannot both write to and delete the same key
- Prevents logical inconsistencies in transaction operations

## Liveness Properties

### EventuallyComplete
- Specifies that all transactions eventually complete (commit or abort)
- Note: This property is expected to fail in the current model because transactions can loop indefinitely in ReadWrite phase
- In practice, applications would have finite operations

## Modeling Decisions

### Conflict Detection
The model implements ScalarDB's conflict detection logic:
1. **Write Conflicts**: Detected if a key was modified after being read
2. **Delete Conflicts**: Can only delete keys that were read and remain unchanged
3. **Phantom Prevention**: Validation phase prevents phantoms by re-checking read set

### Atomicity Guarantees
- Prepare phase uses conditional updates (modeled as atomic check-and-set)
- Commit phase atomically updates coordinator state before updating records
- Abort phase atomically rolls back all changes

### Version Management
- Each record maintains a version number
- Versions increment on each modification
- Used for optimistic concurrency control

### Delete Operation Modeling
Deletes are modeled as a two-phase process:
1. During Prepare: Record marked as "DELETED" but value preserved
2. During Commit: Value set to NULL, state set to "COMMITTED"
3. This allows proper rollback if transaction aborts

## Verification Approach

### State Space Exploration
TLC explores all possible interleavings of transaction operations to verify:
- No invariant violations in any reachable state
- Temporal properties hold across all behaviors

### Serializability Verification
The `txnOrder` sequence captures the commit order, enabling verification that:
- The concurrent execution is equivalent to some serial execution
- The serial order respects real-time ordering (strict serializability)

### Edge Cases Covered
- Concurrent transactions on same keys
- Read-write conflicts
- Write-write conflicts  
- Delete-write conflicts
- Phantom reads
- Transaction aborts and rollbacks
- Prepared records from crashed transactions

## Limitations and Assumptions

### Simplifications
1. **Fixed Database Schema**: Uses predefined KEYS constant
2. **No Network Failures**: Assumes reliable communication
3. **No Coordinator Failures**: Coordinator state updates are atomic
4. **No Timestamp Ordering**: Real-time ordering not explicitly modeled

### Finite Model
- Uses small finite sets for model checking tractability
- Results generalize to larger systems under same assumptions

### Liveness
- The model allows infinite loops in ReadWrite phase
- Real implementations would have finite operations
- Focus is on safety properties rather than liveness

## Future Extensions

Potential enhancements to the specification:

1. **Multi-Coordinator**: Model distributed coordinator with consensus
2. **Failure Scenarios**: Add node crashes and recovery
3. **Performance Metrics**: Track abort rates and contention
4. **Other Isolation Levels**: Model SNAPSHOT isolation
5. **Cross-Partition Transactions**: Model distributed transactions
6. **Timestamp Ordering**: Add real-time timestamps for strict serializability

## Usage Guidelines

### For Developers
- Use to understand transaction processing logic
- Verify protocol changes maintain safety properties
- Test edge cases before implementation

### For Testing
- Generate test scenarios from counterexamples
- Ensure implementation matches formal model
- Validate optimization correctness

### For Documentation
- Provides precise, unambiguous protocol description
- Serves as authoritative reference for behavior
- Helps onboard new team members

## Related Resources

- [ScalarDB Documentation](https://github.com/scalar-labs/scalardb/docs)
- [Consensus Commit Paper](https://dl.acm.org/doi/10.14778/3551793.3551807)
- [TLA+ Specification Language](https://lamport.azurewebsites.net/tla/tla.html)
- [PlusCal Algorithm Language](https://lamport.azurewebsites.net/tla/pluscal.html)