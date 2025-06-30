# Running TLA+ Specifications for ScalarDB

This guide explains how to run the TLA+ formal specifications for ScalarDB's Consensus Commit protocol.

## Prerequisites

1. **Java Runtime Environment (JRE)**
   - Java 11 or later is required
   - Verify installation: `java -version`

2. **TLA+ Tools**
   - Download the TLA+ tools JAR file:
     ```bash
     curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o tla2tools.jar
     ```

## Available Specifications

- `scalardb_strict_serializability.tla` - PlusCal model verifying strict serializability of ScalarDB's Consensus Commit protocol with SERIALIZABLE isolation

## Running the Specifications

### 1. Translate PlusCal to TLA+

If you modify the PlusCal algorithm section, you need to retranslate it:

```bash
java -cp tla2tools.jar pcal.trans scalardb_strict_serializability.tla
```

This generates the TLA+ translation between the `\* BEGIN TRANSLATION` and `\* END TRANSLATION` markers.

### 2. Run the TLC Model Checker

Basic command:
```bash
java -cp tla2tools.jar tlc2.TLC -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

With performance optimizations:
```bash
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

### 3. Configuration Options

The `.cfg` file controls the model checking parameters:

```tla
SPECIFICATION Spec
INVARIANTS 
    TypeInvariant
    ConsistencyInvariant
    NoWriteDeleteConflict
PROPERTIES
    EventuallyComplete
CONSTANTS
    KEYS = {k1, k2}
    TRANSACTIONS = {t1, t2}
    VALUES = {v1, v2}
    NULL = null
CHECK_DEADLOCK FALSE
```

You can modify these constants to test different scenarios:
- Increase the number of keys, transactions, or values for more comprehensive testing
- Add or remove invariants and properties
- Enable/disable deadlock checking

### 4. Advanced Options

Run with multiple workers (parallel model checking):
```bash
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers 4 -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

Run with more memory:
```bash
java -Xmx16G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

Generate state space visualization:
```bash
java -cp tla2tools.jar tlc2.TLC -dump dot state_space.dot -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

## Interpreting Results

### Successful Run
When all invariants and properties hold:
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states...
```

### Invariant Violation
If an invariant is violated, TLC will show:
- The invariant that was violated
- A counterexample trace showing how to reach the violating state
- The specific state that violates the invariant

### Temporal Property Violation
If a temporal property is violated, TLC will show:
- The property that was violated
- A counterexample behavior (sequence of states)
- For liveness violations, it may show a loop in the behavior

### Example Output
```
TLC2 Version 2.20 of Day Month 20??
Running breadth-first search Model-Checking...
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Model checking completed. No error has been found.
  32107 states generated, 8330 distinct states found
```

## Common Issues and Solutions

### Java Version Error
If you see: `UnsupportedClassVersionError`
- Solution: Update to Java 11 or later

### Out of Memory
If you see: `OutOfMemoryError`
- Solution: Increase heap size with `-Xmx` flag

### Model Too Large
If model checking takes too long:
- Reduce the number of constants (fewer keys, transactions, values)
- Use symmetry reduction if applicable
- Run with more workers

## Tips for Effective Model Checking

1. **Start Small**: Begin with small constants (2-3 of each) and gradually increase
2. **Check Invariants First**: Run without temporal properties initially
3. **Use Simulation Mode**: For initial debugging, use simulation mode:
   ```bash
   java -cp tla2tools.jar tlc2.TLC -simulate -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
   ```
4. **Monitor Progress**: TLC periodically reports progress - watch for state space explosion

## Additional Resources

- [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)
- [PlusCal Manual](https://lamport.azurewebsites.net/tla/p-manual.pdf)
- [TLC Model Checker Guide](https://lamport.azurewebsites.net/tla/tlc.html)
- [Learn TLA+](https://learntla.com/)