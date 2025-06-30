# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a TLA+/PlusCal formal verification project for ScalarDB's Consensus Commit distributed transaction protocol. The project uses mathematical modeling and exhaustive state space exploration to verify the correctness of ScalarDB's transaction processing, ensuring it maintains ACID properties across distributed systems.

## Key Commands

### Translate PlusCal to TLA+
Before running model checking, translate PlusCal specifications:
```bash
java -cp tla2tools.jar pcal.trans scalardb_strict_serializability.tla
```

### Run Model Checking
Basic verification:
```bash
java -cp tla2tools.jar tlc2.TLC -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

With performance optimizations (recommended for faster verification):
```bash
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers 4 -config scalardb_strict_serializability.cfg scalardb_strict_serializability.tla
```

### Run Specific Test Scenarios
To run with test scenario configurations:
```bash
java -cp tla2tools.jar tlc2.TLC -config scalardb_test_scenarios.cfg scalardb_strict_serializability.tla
```

## Architecture

### Core Specifications
- **scalardb_strict_serializability.tla**: Main PlusCal model implementing SERIALIZABLE isolation level. Contains the complete transaction lifecycle, coordinator logic, and participant behavior.
- **scalardb_snapshot_isolation.tla**: Alternative model for SNAPSHOT isolation level.
- **scalardb_verification_properties.tla**: Additional invariants and temporal properties for comprehensive verification.

### Model Structure
The specification models:
1. **Transactions**: Clients executing read/write operations
2. **Coordinator**: Central component managing 2PC (two-phase commit)
3. **Participants**: Database nodes holding actual data
4. **Network**: Message passing with potential delays/reordering

### Key Safety Properties Verified
- **Atomicity**: All-or-nothing transaction execution
- **Consistency**: Invariants like no dirty reads, no lost updates
- **Isolation**: Serializability or snapshot isolation guarantees
- **No Anomalies**: Prevention of write skew, phantom reads, etc.

### Configuration Files
- **.cfg files**: Define model parameters (number of transactions, keys, values) and specify which invariants/properties to check
- **scalardb_test_scenarios.cfg**: Contains specific anomaly scenarios to verify prevention

## Development Workflow

1. Modify the PlusCal algorithm section (between `--algorithm` and `end algorithm`)
2. Run the translation command to generate TLA+ from PlusCal
3. Run model checking to verify correctness
4. If errors found, examine the error trace to understand the violation
5. The `states/` directory contains state space from previous runs (can be deleted to start fresh)

## Important Notes

- Java 17+ required (specified in .java-version)
- Model checking can be computationally intensive - use worker threads for better performance
- TTrace files are generated error traces from failed verification runs
- The model uses bounded parameters (finite transactions, keys, values) to make verification tractable
- Focus on safety properties (what should never happen) rather than specific implementation details