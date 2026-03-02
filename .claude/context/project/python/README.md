# Python Context

Domain knowledge for Python development within the ModelChecker project.

## Directory Structure

```
project/python/
├── README.md              # This file
├── domain/                # Core ModelChecker concepts
│   ├── model-checker-api.md
│   └── theory-lib-patterns.md
├── patterns/              # Common implementation patterns
│   └── semantic-evaluation.md
└── standards/             # Coding conventions
    └── code-style.md
```

## Loading Strategy

**Always load first**:
- This README for overview
- `domain/model-checker-api.md` for package structure

**Load for theory library work**:
- `domain/theory-lib-patterns.md` for standard theory file patterns
- `patterns/semantic-evaluation.md` for truthmaker semantic evaluation

**Load for general Python work**:
- `standards/code-style.md` for Python conventions

## Project Context

The ModelChecker is a Python framework for developing and exploring modular semantic theories using Z3 SMT solver.

**Key dependencies**:
- Python 3.10+
- z3-solver (Z3 SMT solver Python bindings)
- pytest (testing)

**Running commands**:
```bash
# Tests require PYTHONPATH set
PYTHONPATH=code/src pytest code/tests/ -v

# Development CLI
cd Code && ./dev_cli.py examples/my_example.py

# Run model checker
model-checker examples.py
```

## Package Structure Overview

```
code/src/model_checker/
├── theory_lib/          # Semantic theories
│   ├── logos/           # Logos theory (truthmaker semantics)
│   ├── exclusion/       # Exclusion theory
│   ├── imposition/      # Imposition theory
│   └── bimodal/         # Bimodal theory
├── builder/             # Project generation
├── iterate/             # Model iteration engine
├── models/              # Core model structures
├── syntactic/           # Formula parsing
├── output/              # Result formatting
└── utils/               # Utility functions (Z3 helpers)
```

## Z3 Integration

ModelChecker uses Z3 extensively for constraint solving. Key utilities in `model_checker.utils`:
- `ForAll`, `Exists` - Quantifier wrappers
- `bitvec_to_substates` - BitVec state manipulation
- `int_to_binary` - State representation conversion

See `@.claude/context/project/z3/` for Z3-specific patterns.

## Agent Context Loading

Agents should load context based on task type:

| Task Type | Required Context |
|-----------|-----------------|
| New theory | theory-lib-patterns.md, semantic-evaluation.md |
| Operator | theory-lib-patterns.md, operators from logos |
| Testing | code-style.md, existing test patterns |
| General Python | model-checker-api.md, code-style.md |
