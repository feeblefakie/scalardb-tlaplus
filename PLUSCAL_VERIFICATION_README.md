# ScalarDB Formal Verification with PlusCal/TLA+

This directory contains PlusCal models for formally verifying the correctness of ScalarDB's distributed transaction protocols, specifically the Consensus Commit protocol with both Strict Serializability and Snapshot Isolation.

## Files Overview

1. **scalardb_strict_serializability.tla** - PlusCal model for verifying the SERIALIZABLE isolation level
2. **scalardb_snapshot_isolation.tla** - PlusCal model for verifying the SNAPSHOT isolation level  
3. **scalardb_verification_properties.tla** - Additional invariants and temporal properties
4. **scalardb_test_scenarios.cfg** - Configuration file with test scenarios
5. **scalardb_strict_serializability.cfg** - Main configuration for strict serializability testing
6. **scalardb_strict_serializability_debug.cfg** - Debug configuration for individual property testing
7. **scalardb_snapshot_isolation_debug.cfg** - Debug configuration for snapshot isolation testing

## Key Features Modeled

### Transaction Protocol
- **State Management**: ACTIVE → PREPARING → PREPARED → VALIDATING (SR only) → COMMITTING → COMMITTED/ABORTED
- **Read/Write Operations**: Buffered writes, snapshot reads
- **Delete Operations**: Proper handling of DELETED state
- **Conflict Detection**: Optimistic concurrency control with conditional updates
- **Recovery**: Lazy recovery for prepared records

### Isolation Levels

#### Strict Serializability (SERIALIZABLE)
- Validation phase after prepare
- Prevents all anomalies including write skew
- Ensures linearizability of operations

#### Snapshot Isolation (SNAPSHOT)  
- No validation phase
- Consistent snapshot reads
- Prevents dirty reads, non-repeatable reads, and lost updates
- Allows write skew anomalies

## Running the Verification

### Prerequisites
- Install TLA+ Toolbox or TLC model checker
- Basic understanding of TLA+/PlusCal syntax

### Steps

1. **Translate PlusCal to TLA+** (if modified):
   ```bash
   # Only needed if you modify the PlusCal algorithm sections
   java -cp tla2tools.jar pcal.trans scalardb_strict_serializability.tla
   java -cp tla2tools.jar pcal.trans scalardb_snapshot_isolation.tla
   ```
   
   Note: The current files are already translated (contain `\* BEGIN TRANSLATION` sections).

2. **Run Model Checking**:
   
   **Quick Test (One-liner)**:
   ```bash
   # For strict serializability
   java -jar tla2tools.jar scalardb_strict_serializability.tla -config scalardb_strict_serializability.cfg
   
   # For snapshot isolation  
   java -jar tla2tools.jar scalardb_snapshot_isolation.tla -config scalardb_snapshot_isolation.cfg
   ```
   
   **Debug Individual Properties**:
   ```bash
   # Debug strict serializability properties
   java -jar tla2tools.jar scalardb_strict_serializability.tla -config scalardb_strict_serializability_debug.cfg
   
   # Debug snapshot isolation properties
   java -jar tla2tools.jar scalardb_snapshot_isolation.tla -config scalardb_snapshot_isolation_debug.cfg
   ```
   
   **Alternative with TLC directly**:
   ```bash
   # For strict serializability
   tlc scalardb_strict_serializability.tla -config scalardb_strict_serializability.cfg
   
   # For snapshot isolation  
   tlc scalardb_snapshot_isolation.tla -config scalardb_snapshot_isolation.cfg
   ```

3. **Customize Configuration**:
   - Adjust CONSTANTS in the .cfg file
   - Start with small values (2 transactions, 2 keys)
   - Gradually increase for more thorough verification

## Properties Verified

### Safety Properties (Invariants)
- **TypeInvariant**: All variables have correct types
- **ConsistencyInvariant**: No prepared records for completed transactions
- **NoPartialStates**: Atomicity of transactions
- **VersionMonotonicity**: Versions always increase

### Liveness Properties
- **EventuallyComplete**: All transactions eventually finish
- **NoPermanentBlocking**: No deadlocks
- **EventualCleanup**: Prepared records eventually commit

### Correctness Properties
- **NoLostUpdates**: Concurrent updates don't overwrite each other
- **NoDirtyReads**: Can't read uncommitted data
- **Linearizability** (SR only): Operations appear atomic
- **NoWriteWriteConflicts** (SI): Core property of snapshot isolation
- **NoWriteSkew** (SR only): Prevents write skew anomalies in strict serializability
- **WriteSkewDetection** (SI): Write skew anomalies are allowed and detectable in snapshot isolation

## Test Scenarios

The configuration includes several test scenarios:

1. **Write-Write Conflict**: Two transactions updating same key
2. **Write Skew**: Classic bank transfer anomaly (prevented in SR, allowed in SI)
3. **Lost Update**: Concurrent updates to same record
4. **Delete Conflicts**: Concurrent delete and update operations

## Interpreting Results

### Successful Verification
- All invariants hold in all reachable states
- Temporal properties are satisfied
- No deadlocks detected

### Finding Anomalies
- For SI model: Write skew anomalies should be detectable and allowed
- For SR model: Write skew should be prevented (note: current validation algorithm has limitations)
- TLC will provide counterexamples for any violations
- Use debug configurations to test individual properties in isolation

## Extending the Models

To add new scenarios or properties:

1. Modify the PlusCal algorithm section
2. Add new invariants in the `define` block
3. Update the configuration file
4. Re-run the PlusCal translator

## Performance Tips

- Use symmetry reduction for identical transactions
- Define a VIEW to reduce state space
- Run with multiple workers: `-workers 4`
- Set appropriate depth limit: `-depth 30`
- Use profiling to identify bottlenecks: `-profile`

## Limitations

These models abstract certain implementation details:
- Network delays and failures
- Detailed storage backend behavior  
- Clock synchronization issues
- Full crash recovery scenarios

### Current Model Limitations
- **Strict Serializability**: The current validation algorithm has limitations in detecting all write skew scenarios that would violate strict serializability. The model accurately represents the current implementation but full strict serializability would require enhanced validation algorithms to detect anti-dependency cycles.
- **Snapshot Isolation**: Correctly models the expected behavior including allowed write skew anomalies.

Despite these abstractions, the models capture the core correctness properties of the Consensus Commit protocol and provide a solid foundation for verification and enhancement.