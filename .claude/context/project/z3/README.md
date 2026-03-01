# Z3 Context

Domain knowledge for Z3 SMT solver development within the ModelChecker project.

## Directory Structure

```
project/z3/
├── README.md                    # This file
├── domain/                      # Core Z3 concepts
│   ├── z3-api.md               # Z3 Python API reference
│   └── smt-patterns.md         # SMT-LIB patterns
└── patterns/                    # Implementation patterns
    ├── constraint-generation.md # ModelChecker constraint building
    └── bitvector-operations.md  # BitVec patterns
```

## Loading Strategy

**Always load first**:
- This README for overview
- `domain/z3-api.md` for core Z3 API

**Load for constraint development**:
- `patterns/constraint-generation.md` for ModelChecker Z3 patterns
- `patterns/bitvector-operations.md` for BitVec state manipulation

**Load for SMT debugging**:
- `domain/smt-patterns.md` for SMT-LIB syntax and tactics

## Z3 in ModelChecker

The ModelChecker uses Z3 extensively for constraint solving in semantic evaluation.

**Key usage patterns**:
- BitVectors represent states (part-whole mereology)
- Quantifiers (ForAll, Exists) for semantic conditions
- Solver timeouts for bounded computation
- Model extraction for counterexamples

**Z3 version**: Compatible with z3-solver PyPI package (4.10+)

## Core Z3 Types Used

| Type | Purpose in ModelChecker |
|------|------------------------|
| `BitVec` | State representation (N bits = N atomic states) |
| `Bool` | Constraint results, propositional atoms |
| `BoolRef` | Z3 boolean expression type |
| `Solver` | Main solving interface |
| `Model` | Satisfying assignment extraction |

## ModelChecker Z3 Utilities

Located in `model_checker.utils`:

```python
from model_checker.utils import (
    ForAll,              # Wrapped ForAll quantifier
    Exists,              # Wrapped Exists quantifier
    bitvec_to_substates, # Convert BitVec to state set
    int_to_binary,       # Int to binary representation
    pretty_set_print,    # Format state sets
)
```

## Quick Reference

```python
import z3

# Create bitvector state
state = z3.BitVec('s', 16)

# Boolean constraints
constraint = z3.And(cond1, cond2)
constraint = z3.Or(cond1, cond2)
constraint = z3.Not(cond)
constraint = z3.Implies(premise, conclusion)

# Quantifiers
universal = z3.ForAll([x], body)
existential = z3.Exists([x], body)

# Solver usage
solver = z3.Solver()
solver.add(constraint)
solver.set('timeout', 10000)  # milliseconds
result = solver.check()  # sat, unsat, or unknown
if result == z3.sat:
    model = solver.model()
```

## MCP Integration (Optional)

When configured in user scope (`~/.claude.json`), z3_mcp provides:
- Direct Z3 constraint solving
- Relationship analysis
- Constraint satisfaction checking

See research report for MCP configuration details.

## Agent Context Loading

Agents should load context based on task type:

| Task Type | Required Context |
|-----------|-----------------|
| Constraint building | constraint-generation.md |
| State manipulation | bitvector-operations.md |
| SMT debugging | smt-patterns.md |
| General Z3 | z3-api.md |
