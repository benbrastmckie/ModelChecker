# Solver Abstraction Layer

This package provides a unified interface for SMT solvers, enabling ModelChecker to use Z3, cvc5, or other compatible backends.

## Architecture

```
solver/
  __init__.py           # Public API exports
  protocols.py          # Protocol classes for duck typing
  types.py              # Type aliases with TYPE_CHECKING guards
  registry.py           # Backend selection and factory
  compat.py             # Cross-solver helper functions
  expressions.py        # Formula construction re-exports
  z3_adapter.py         # Z3 backend (thin passthrough)
  cvc5_adapter.py       # cvc5 backend (pythonic API)
  tests/                # Test suite
```

## Usage

### Basic Solver Usage

```python
from model_checker.solver import create_solver, SolverResult
from model_checker.z3_shim import BitVec, And

# Create solver (uses configured backend)
solver = create_solver()

# Add constraints
x = BitVec("x", 8)
y = BitVec("y", 8)
solver.add(And(x + y == 10, x > 0, y > 0))

# Check satisfiability
result = solver.check()
if SolverResult.is_sat(result):
    model = solver.model()
    print(f"x = {model.eval(x)}")
    print(f"y = {model.eval(y)}")
```

### Backend Selection

The solver backend can be selected via (in priority order):

1. **CLI flag**: `model-checker --z3 example.py` or `model-checker --cvc5 example.py`
2. **Environment variable**: `MODEL_CHECKER_SOLVER=cvc5`
3. **Per-example settings**: `example_settings["solver"] = "cvc5"`
4. **Default**: `z3`

#### Per-Example Solver Selection

Each example can specify its preferred solver backend:

```python
EXT_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'max_time': 1,
    'solver': 'z3',  # Use z3 for this example
}

# Or specify cvc5 for specific examples
COMPLEX_EXAMPLE_settings = {
    'N': 5,
    'solver': 'cvc5',  # Use cvc5 for this example
}
```

This allows mixing solvers within the same test suite based on each example's needs.

### Programmatic Selection

```python
from model_checker.solver import set_cli_backend, validate_backend

# Set backend explicitly
set_cli_backend("cvc5")

# Validate backend is available
try:
    validate_backend("cvc5")
except ImportError as e:
    print(f"cvc5 not available: {e}")
```

## Protocols

The package uses Python Protocols for duck typing:

- `SolverProtocol`: Basic solver interface (add, check, model, push, pop)
- `TrackedSolverProtocol`: Extended with assert_tracked and unsat_core
- `ModelProtocol`: Model evaluation interface

## Migration from Direct Z3 Imports

Replace direct z3 imports with the shim for backend-agnostic code:

```python
# Before
from z3 import And, Or, BitVec

# After
from model_checker.z3_shim import And, Or, BitVec
```

The shim automatically uses the active backend (z3 or cvc5.pythonic).

## Compatibility Helpers

For operations that differ between backends:

```python
from model_checker.solver import is_true, is_false, simplify, eval_model

# Check boolean values (handles z3.BoolRef vs cvc5 values)
if is_true(model.eval(expr), backend="z3"):
    ...

# Evaluate expressions in model
value = eval_model(model, expr, backend="z3")
```

## Testing

Run solver tests:

```bash
pytest src/model_checker/solver/tests/ -v
```

When cvc5 is installed, equivalence tests verify both backends produce identical results.

## Optional Dependencies

cvc5 is an optional dependency:

```bash
pip install model-checker[cvc5]
# or
pip install cvc5
```

## Known Differences

| Feature | Z3 | cvc5 |
|---------|-----|------|
| Unsat core | Labels via assert_and_track | Terms mapped to labels |
| Model eval | `model.eval(expr, model_completion=True)` | `model.evaluate(expr)` |
| Timeout | `solver.set("timeout", ms)` | `solver.set("tlimit-per", ms)` |
| Context | Global context reset needed | Fresh solver per instance |
