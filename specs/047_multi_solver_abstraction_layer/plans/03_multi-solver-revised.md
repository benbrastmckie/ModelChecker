# Implementation Plan: Multi-Solver Abstraction Layer (Revised)

- **Task**: 47 - Implement multi-solver abstraction layer for z3, cvc5, and future constraint solvers
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None
- **Research Inputs**:
  - specs/047_multi_solver_abstraction_layer/reports/01_team-research.md
  - specs/047_multi_solver_abstraction_layer/reports/03_plan-review.md
- **Artifacts**: plans/03_multi-solver-revised.md (this file)
- **Previous Plan**: plans/02_multi-solver-plan.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This revised plan incorporates critical findings from the plan review:

1. **Critical fix**: cvc5.pythonic does NOT support unsat cores - solver control must use cvc5 base API
2. **Simplified migration**: Use `__getattr__` import shim to reduce 74-file changes to single regex
3. **Type safety**: Protocol classes instead of `Any` types
4. **No overengineering**: Skip plugin architecture, entry points, and dependency injection patterns

### Key Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Import migration | `__getattr__` shim | Single regex vs 74 manual edits |
| Type system | Protocol classes | Duck typing with static checking |
| cvc5 adapter | Split (pythonic + base API) | Pythonic lacks unsat cores |
| Architecture | Simple module structure | Avoid overkill for 2 backends |

## Goals & Non-Goals

**Goals**:
- Create `model_checker/solver/` package with clean abstraction
- Enable solver selection: settings default + `--z3`/`--cvc5` CLI flags
- Maintain zero-overhead Z3 path (no regression)
- Support cvc5 with full feature parity including unsat cores

**Non-Goals**:
- Plugin architecture (overkill for 2-3 backends)
- Dependency injection (unnecessary restructuring)
- Entry points discovery (complexity without benefit)
- Bitwuzla/Yices2 support (deferred)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| cvc5 base API complexity | High | High | Split adapter; pythonic for formulas, base for solver |
| Import shim edge cases | Medium | Low | Comprehensive test coverage |
| Protocol typing gaps | Medium | Low | Use TYPE_CHECKING guards |
| Performance regression | Low | Low | Benchmark Z3 passthrough |

## Implementation Phases

### Phase 1: Create Solver Package with Protocols [NOT STARTED]

**Goal**: Establish solver abstraction with Protocol-based interface (not ABC)

**Tasks**:
- [ ] Create `code/src/model_checker/solver/__init__.py` with public API
- [ ] Create `code/src/model_checker/solver/protocols.py` with:
  ```python
  from typing import Protocol, runtime_checkable, Sequence, Any

  @runtime_checkable
  class SolverProtocol(Protocol):
      def add(self, constraint: Any) -> None: ...
      def check(self) -> Any: ...
      def model(self) -> "ModelProtocol": ...
      def push(self) -> None: ...
      def pop(self, n: int = 1) -> None: ...

  @runtime_checkable
  class ModelProtocol(Protocol):
      def eval(self, expr: Any, model_completion: bool = False) -> Any: ...

  class SolverResult:
      SAT = "sat"
      UNSAT = "unsat"
      UNKNOWN = "unknown"
  ```
- [ ] Create `code/src/model_checker/solver/types.py` with TYPE_CHECKING guards:
  ```python
  from typing import TYPE_CHECKING, Union

  if TYPE_CHECKING:
      import z3
      SolverExpr = Union[z3.BoolRef, z3.BitVecRef, z3.ArithRef]
      SolverModel = z3.ModelRef
  else:
      SolverExpr = object
      SolverModel = object
  ```
- [ ] Create `code/src/model_checker/solver/registry.py` for solver selection
- [ ] Create `code/src/model_checker/solver/compat.py` for cross-solver helpers:
  ```python
  def is_true(val: Any, backend: str) -> bool:
      if backend == "z3":
          import z3
          return z3.is_true(val)
      elif backend == "cvc5":
          return bool(val)  # or cvc5-specific check
  ```

**Timing**: 1.5 hours

**Verification**:
- Package imports without errors
- Protocol classes can be used for type hints
- `isinstance(z3.Solver(), SolverProtocol)` returns True

---

### Phase 2: Create Import Shim and Z3 Adapter [NOT STARTED]

**Goal**: Z3 passthrough with `__getattr__` shim for gradual migration

**Tasks**:
- [ ] Create `code/src/model_checker/solver/z3_adapter.py`:
  ```python
  """Z3 adapter - thin passthrough for zero overhead."""
  import z3

  class Z3SolverAdapter:
      """Wraps z3.Solver with protocol-compatible interface."""
      def __init__(self):
          self._solver = z3.Solver()
          self._tracked: dict[str, Any] = {}

      def add(self, constraint):
          self._solver.add(constraint)

      def assert_tracked(self, constraint, label: str):
          self._solver.assert_and_track(constraint, label)
          self._tracked[label] = constraint

      def check(self) -> str:
          result = self._solver.check()
          return str(result)

      def model(self):
          return self._solver.model()

      def unsat_core(self) -> list:
          return list(self._solver.unsat_core())

      # ... other methods passthrough
  ```
- [ ] Create `code/src/model_checker/solver/expressions.py` re-exporting from active backend
- [ ] Create `code/src/model_checker/z3_shim.py` with `__getattr__`:
  ```python
  """Transitional import shim. Replace 'from z3 import' with 'from model_checker.z3_shim import'."""
  from model_checker.solver import get_active_backend
  import importlib

  _backend_module = None

  def __getattr__(name: str):
      global _backend_module
      if _backend_module is None:
          backend = get_active_backend()
          if backend == "z3":
              _backend_module = importlib.import_module("z3")
          elif backend == "cvc5":
              _backend_module = importlib.import_module("cvc5.pythonic")
      return getattr(_backend_module, name)

  def __dir__():
      import z3
      return dir(z3)
  ```

**Timing**: 1.5 hours

**Verification**:
- `from model_checker.z3_shim import And, Or, BitVec` works identically to z3
- Z3SolverAdapter satisfies SolverProtocol
- All existing tests pass with z3_shim

---

### Phase 3: Migrate Imports via Regex [NOT STARTED]

**Goal**: Change all Z3 imports to use shim with single regex operation

**Tasks**:
- [ ] Run regex replacement across codebase:
  ```bash
  find code/src/model_checker -name "*.py" -not -path "*/solver/*" \
    -exec sed -i 's/from z3 import/from model_checker.z3_shim import/g' {} \;
  find code/src/model_checker -name "*.py" -not -path "*/solver/*" \
    -exec sed -i 's/import z3$/from model_checker import z3_shim as z3/g' {} \;
  ```
- [ ] Handle edge cases manually:
  - `syntactic/atoms.py` - AtomSort global declaration
  - `utils/context.py` - Z3 context management (skip for now, z3-specific)
  - Type annotations with `z3.` prefix
- [ ] Verify no direct z3 imports remain:
  ```bash
  grep -r "from z3 import\|import z3" code/src/model_checker --include="*.py" | \
    grep -v solver/ | grep -v z3_shim | grep -v "# keep"
  ```

**Timing**: 1 hour

**Verification**:
- Zero direct z3 imports outside solver/ and z3_shim.py
- All 334 tests pass
- No import errors at runtime

---

### Phase 4: Implement cvc5 Adapter (Split Architecture) [NOT STARTED]

**Goal**: cvc5 adapter with pythonic API for formulas, base API for solver control

**Critical**: cvc5.pythonic does NOT support unsat cores. Must use base API for solver operations.

**Tasks**:
- [ ] Create `code/src/model_checker/solver/cvc5_adapter.py`:
  ```python
  """cvc5 adapter - pythonic for formulas, base API for solver control."""

  class CVC5SolverAdapter:
      """cvc5 solver with manual unsat core tracking."""

      def __init__(self):
          import cvc5
          self._solver = cvc5.Solver()
          self._solver.setOption("produce-unsat-cores", "true")
          self._tracked: dict[str, Any] = {}
          self._labels: dict[int, str] = {}  # expr_id -> label

      def add(self, constraint):
          # Use base API for adding
          self._solver.assertFormula(constraint)

      def assert_tracked(self, constraint, label: str):
          """Manual tracking since pythonic lacks assert_and_track."""
          self._tracked[label] = constraint
          self._labels[id(constraint)] = label
          self._solver.assertFormula(constraint)

      def check(self) -> str:
          result = self._solver.checkSat()
          if result.isSat():
              return "sat"
          elif result.isUnsat():
              return "unsat"
          return "unknown"

      def model(self):
          return CVC5ModelAdapter(self._solver)

      def unsat_core(self) -> list:
          """Return labels of core constraints."""
          core_terms = self._solver.getUnsatCore()
          return [self._labels.get(id(t), str(t)) for t in core_terms]

      def set_timeout(self, ms: int):
          self._solver.setOption("tlimit-per", str(ms))
  ```
- [ ] Create `CVC5ModelAdapter` for model evaluation:
  ```python
  class CVC5ModelAdapter:
      def __init__(self, solver):
          self._solver = solver

      def eval(self, expr, model_completion: bool = False):
          return self._solver.getValue(expr)
  ```
- [ ] Add cvc5 to registry with detection:
  ```python
  def detect_cvc5() -> bool:
      try:
          import cvc5
          return True
      except ImportError:
          return False
  ```
- [ ] Update expressions.py to support cvc5 backend switching

**Timing**: 2.5 hours

**Verification**:
- CVC5SolverAdapter satisfies SolverProtocol
- Manual unsat core tracking works correctly
- Simple solve operations produce equivalent results to Z3

---

### Phase 5: Add Solver Selection Configuration [NOT STARTED]

**Goal**: Settings default + CLI flag override + fallback to z3

**Tasks**:
- [ ] Add `solver` setting to `DEFAULT_GENERAL_SETTINGS`:
  ```python
  DEFAULT_GENERAL_SETTINGS = {
      "solver": "z3",  # default solver backend
      # ... existing settings
  }
  ```
- [ ] Add CLI flags to `__main__.py`:
  ```python
  parser.add_argument("--z3", action="store_true", help="Use Z3 solver")
  parser.add_argument("--cvc5", action="store_true", help="Use cvc5 solver")
  ```
- [ ] Implement selection priority in registry.py:
  ```python
  def get_active_backend() -> str:
      """Priority: CLI flag > env var > settings > 'z3'"""
      # 1. Check CLI flags (passed via settings)
      if settings.get("_cli_solver"):
          return settings["_cli_solver"]
      # 2. Check environment variable
      if env := os.environ.get("MODEL_CHECKER_SOLVER"):
          return env
      # 3. Check settings
      if solver := settings.get("solver"):
          return solver
      # 4. Default to z3
      return "z3"
  ```
- [ ] Add error handling for unavailable solver:
  ```python
  def validate_backend(backend: str) -> None:
      if backend == "cvc5" and not detect_cvc5():
          raise ImportError("cvc5 not installed. Install with: pip install cvc5")
  ```

**Timing**: 1 hour

**Verification**:
- `model-checker --z3 example.py` uses Z3
- `model-checker --cvc5 example.py` uses cvc5 (if installed)
- Without flags, uses settings default ("z3")
- Clear error message when requested solver not installed

---

### Phase 6: Testing and Equivalence Verification [NOT STARTED]

**Goal**: Ensure solver equivalence with robust testing

**Tasks**:
- [ ] Create `code/src/model_checker/solver/tests/test_equivalence.py`:
  ```python
  import pytest
  from hypothesis import given, strategies as st

  @pytest.mark.skipif(not cvc5_available(), reason="cvc5 not installed")
  def test_basic_sat_equivalence():
      """Same constraints produce same sat/unsat result."""
      z3_result = solve_with_z3(constraints)
      cvc5_result = solve_with_cvc5(constraints)
      assert z3_result.status == cvc5_result.status

  @pytest.mark.skipif(not cvc5_available(), reason="cvc5 not installed")
  @given(st.integers(0, 15), st.integers(0, 15))
  def test_bitvec_arithmetic(a, b):
      """Property-based test for bitvector operations."""
      # Test addition, subtraction, bitwise ops
  ```
- [ ] Create golden test suite with expected results:
  ```
  tests/solver_equivalence/
    logos_validity.json      # sat
    logos_contradiction.json # unsat
    bimodal_temporal.json    # sat
  ```
- [ ] Add solver backend to pytest markers:
  ```python
  @pytest.fixture(params=["z3", "cvc5"])
  def solver_backend(request):
      if request.param == "cvc5" and not cvc5_available():
          pytest.skip("cvc5 not installed")
      return request.param
  ```

**Timing**: 1.5 hours

**Verification**:
- All equivalence tests pass when cvc5 installed
- Tests skip gracefully when cvc5 not installed
- No regressions in existing test suite

---

### Phase 7: Documentation and Cleanup [NOT STARTED]

**Goal**: Document architecture, add optional dependency, clean up

**Tasks**:
- [ ] Create `code/src/model_checker/solver/README.md`:
  ```markdown
  # Solver Abstraction Layer

  Enables ModelChecker to use Z3, cvc5, or other SMT solvers.

  ## Architecture
  - `protocols.py` - Protocol classes for duck typing
  - `expressions.py` - Formula construction (And, Or, BitVec, etc.)
  - `z3_adapter.py` - Z3 backend (passthrough)
  - `cvc5_adapter.py` - cvc5 backend (pythonic + base API)
  - `registry.py` - Backend selection

  ## Usage
  model-checker --z3 example.py   # Use Z3 (default)
  model-checker --cvc5 example.py # Use cvc5
  ```
- [ ] Add cvc5 as optional dependency in `pyproject.toml`:
  ```toml
  [project.optional-dependencies]
  cvc5 = ["cvc5>=1.1.0"]
  ```
- [ ] Deprecate z3_shim.py with warning (keep for compatibility):
  ```python
  import warnings
  warnings.warn(
      "z3_shim is deprecated. Import from model_checker.solver.expressions",
      DeprecationWarning
  )
  ```
- [ ] Clean up TYPE_CHECKING imports throughout

**Timing**: 1 hour

**Verification**:
- Documentation complete and accurate
- `pip install model-checker[cvc5]` works
- Deprecation warning shows when using z3_shim

## Testing & Validation

- [ ] All 334 existing tests pass unchanged
- [ ] New solver equivalence tests pass
- [ ] `model-checker --z3 examples/default.py` produces expected output
- [ ] `model-checker --cvc5 examples/default.py` produces equivalent output
- [ ] Performance: Z3 path shows no measurable regression
- [ ] Pyright/mypy: No new type errors introduced

## Artifacts & Outputs

```
code/src/model_checker/
  solver/
    __init__.py
    protocols.py        # Protocol classes
    types.py            # Type aliases
    registry.py         # Backend selection
    compat.py           # Cross-solver helpers
    expressions.py      # Formula construction re-exports
    z3_adapter.py       # Z3 backend
    cvc5_adapter.py     # cvc5 backend (split architecture)
    README.md
    tests/
      __init__.py
      test_equivalence.py
      test_registry.py
  z3_shim.py            # Transitional (deprecated after migration)
```

## Migration Summary

| Before | After |
|--------|-------|
| `from z3 import And, Or` | `from model_checker.z3_shim import And, Or` |
| Direct `z3.Solver()` | `from model_checker.solver import create_solver` |
| `z3.is_true(val)` | `from model_checker.solver.compat import is_true` |

## Rollback/Contingency

1. Phase 1-3 fully reversible by removing solver/ and reverting regex changes
2. Git commits at phase boundaries enable targeted rollback
3. Z3 passthrough ensures no behavioral changes until cvc5 explicitly selected
4. If cvc5 adapter proves problematic, keep as experimental with warnings
