# Teammate B Research Findings: Alternative Patterns and Prior Art

**Task**: 47 - Multi-Solver Abstraction Layer
**Focus**: Existing libraries, API abstraction patterns, integration challenges, Python-specific considerations
**Date**: 2026-03-29

---

## Key Findings

### 1. Existing Multi-Solver Libraries Assessment

#### pySMT (v0.9.6, released June 2024)

**Architecture**: pySMT introduces its own solver-agnostic formula representation using `FNode` objects, with bidirectional converters (walker-based) that translate between pySMT's internal AST and each backend solver's native objects. Supported solvers: MathSAT, Z3, cvc5, Yices2, CUDD, PicoSAT, Boolector. Also supports any SMT-LIB 2 compliant solver through a generic interface.

**Verdict for ModelChecker: UNSUITABLE as a direct abstraction layer.**

Critical incompatibilities:
1. pySMT does not support Z3's `DeclareSort` for uninterpreted sorts. ModelChecker uses `DeclareSort("AtomSort")` at module import time to create the global sort for all sentence letters. This is the deepest architectural coupling and pySMT has no equivalent.
2. pySMT's `FNode` objects are immutable and cannot represent Z3-style `Function` declarations (`z3.Function("verify", BitVecSort(N), AtomSort, BoolSort())`). Adopting pySMT would require rewriting all theory semantics classes.
3. pySMT's walker/converter pattern introduces significant overhead for the tight feedback loop between formula construction and model evaluation that ModelChecker uses.
4. Maintenance concern: last major release was June 2024, activity appears to have slowed.

**Lesson from pySMT**: The right abstraction is NOT a new formula representation language. The right abstraction is a thin interface layer over solver-specific objects, keeping native solver objects intact.

#### smt-switch (v1.1.0, March 2026)

**Architecture**: C++ framework providing abstract base classes (`AbsSmtSolver`, `AbsSort`, `AbsTerm`) accessed via smart pointers. Python bindings exist but are built on top of C++ infrastructure.

**Verdict for ModelChecker: UNSUITABLE as primary abstraction.**

- Primarily C++-centric; Python bindings are secondary and less documented
- Installation requires building C++ shared libraries per solver
- Not idiomatic Python; does not leverage Python's type system
- The C++ abstraction does not match the Python-native development patterns used in ModelChecker

**Lesson from smt-switch**: The abstract base class pattern (AbsSort, AbsTerm, AbsSmtSolver) is the right structural approach. A Python-native version of this pattern would serve ModelChecker well.

#### pysmtlib (cnheitman/pysmtlib)

**Architecture**: Subprocess-based: serializes constraints to SMT-LIB v2 format, calls external solver binaries, parses output. Very simple.

**Verdict for ModelChecker: UNSUITABLE.**

SMT-LIB text serialization would eliminate incremental solving (`push`/`pop`), unsat core extraction, and direct model evaluation -- all of which ModelChecker depends on heavily. Performance would be unacceptable for iteration over multiple models.

---

### 2. The cvc5 Pythonic API: Key Prior Art

The most relevant existing work is the `cvc5_pythonic_api`, which is a Z3Py-compatible interface to cvc5 (`cvc5/cvc5_pythonic_api` on GitHub). As of cvc5 1.1+, the pythonic API is included in the main `cvc5` pip package (imported as `from cvc5.pythonic import ...`).

**Critical finding**: The function names are nearly identical to z3. The following functions exist with the same name and semantics in both `z3` and `cvc5.pythonic`:

| Function | z3 | cvc5.pythonic |
|----------|-----|---------------|
| `DeclareSort(name)` | yes | yes |
| `Const(name, sort)` | yes | yes |
| `Function(name, *sorts)` | yes | yes |
| `BitVec(name, size)` | yes | yes |
| `BitVecs(names, size)` | yes | yes |
| `BitVecSort(size)` | yes | yes |
| `BitVecVal(val, size)` | yes | yes |
| `BoolSort()` | yes | yes |
| `IntSort()` | yes | yes |
| `ArraySort(idx, elem)` | yes | yes |
| `And(*args)` | yes | yes |
| `Or(*args)` | yes | yes |
| `Not(arg)` | yes | yes |
| `Implies(a, b)` | yes | yes |
| `ForAll(bvs, formula)` | yes | yes |
| `Exists(bvs, formula)` | yes | yes |
| `substitute(e, pairs)` | yes | yes (confirmed in docs) |
| `simplify(e)` | yes | yes |
| `BoolVal(b)` | yes | yes |
| `IntVal(n)` | yes | yes |
| `EmptySet(sort)` | yes | yes |
| `SetAdd(s, e)` | yes | yes |
| `IsMember(e, s)` | yes | yes |
| `sat`, `unsat`, `unknown` | yes | yes |
| `Solver()` | yes | yes |

**Known divergences** (where cvc5.pythonic differs from z3):
- `assert_and_track(constraint, label)` - present in z3, **absent in cvc5.pythonic**. This is used in ModelChecker's `ModelDefaults._setup_solver()` for unsat core tracking. cvc5 does provide unsat core support but via a different mechanism (proof infrastructure, must be enabled via solver options before asserting).
- `solver.unsat_core()` - z3 returns `AstVector`, cvc5 equivalent is `solver.getUnsatCore()` (base API) or different call in pythonic.
- `solver.reason_unknown()` - z3-specific method. cvc5 equivalent exists but may require the base API.
- `solver.set("timeout", milliseconds)` - z3 uses string option name. cvc5 equivalent is `solver.setOption("tlimit-per", str(ms))` or similar.
- `z3.is_true(val)` / `z3.is_false(val)` - module-level functions in z3. Not confirmed as module-level in cvc5.pythonic (may be method-based or use Python bool coercion).
- `z3.is_const(expr)` - used in `syntactic/formulas.py` and `sentence.py` for formula analysis. cvc5 equivalent is `expr.is_const()` (method-based).
- `model.eval(expr, model_completion=True)` - z3 ModelRef method. cvc5 equivalent is `model.evaluate(expr, True)` (different name, same semantics).

**Important**: The cvc5.pythonic project README acknowledges: "This API is missing some features from cvc5 and Z3Py." The precise incomplete features are not enumerated but include at minimum `assert_and_track`.

---

### 3. API Abstraction Patterns: Strategy Pattern Analysis

The established patterns for Python plugin/backend abstraction are:

**Pattern A: Module-level import alias (cheapest, highest risk)**
```python
# solver/__init__.py
import os
_backend = os.environ.get("MODEL_CHECKER_SOLVER", "z3")
if _backend == "z3":
    from z3 import *
elif _backend == "cvc5":
    from cvc5.pythonic import *
```
Pro: zero overhead, existing code needs no changes for the common subset.
Con: only works for functions with identical signatures; divergences (assert_and_track, is_true, etc.) remain unhandled.

**Pattern B: Protocol-based thin adapter (recommended)**
```python
# solver/interface.py
from typing import Protocol, runtime_checkable, List, Any, Tuple

@runtime_checkable
class SolverInterface(Protocol):
    def add(self, constraint: Any) -> None: ...
    def assert_and_track(self, constraint: Any, label: str) -> None: ...
    def check(self) -> Any: ...
    def model(self) -> Any: ...
    def unsat_core(self) -> List[Any]: ...
    def reason_unknown(self) -> str: ...
    def push(self) -> None: ...
    def pop(self, n: int = 1) -> None: ...
    def set(self, option: str, value: Any) -> None: ...
```

The adapter for Z3 is a transparent passthrough. The adapter for cvc5 translates the divergent methods (`assert_and_track`, `reason_unknown`, `set("timeout", ...)`).

**Pattern C: ABC-based concrete adapter classes**
```python
from abc import ABC, abstractmethod

class AbstractSolver(ABC):
    @abstractmethod
    def assert_tracked(self, constraint, label: str) -> None: ...
    @abstractmethod
    def check_sat(self) -> str: ...  # returns "sat", "unsat", or "unknown"
    @abstractmethod
    def get_model(self) -> Any: ...
    @abstractmethod
    def get_unsat_core(self) -> list: ...
    @abstractmethod
    def set_timeout(self, ms: int) -> None: ...

class Z3SolverAdapter(AbstractSolver):
    def __init__(self):
        import z3
        self._solver = z3.Solver()
    def assert_tracked(self, constraint, label):
        self._solver.assert_and_track(constraint, label)
    def check_sat(self):
        import z3
        return str(self._solver.check())  # "sat", "unsat", "unknown"
    ...

class CVC5SolverAdapter(AbstractSolver):
    def __init__(self):
        from cvc5.pythonic import Solver
        self._solver = Solver()
        self._tracked = {}
    def assert_tracked(self, constraint, label):
        # cvc5 unsat core: enable proof tracking before first assertion
        self._solver.add(constraint)
        self._tracked[label] = constraint
    ...
```

This is the pattern used by pySMT and smt-switch conceptually, but applied only to the Solver control interface (not to formula construction). Formula construction stays native.

---

### 4. Integration Challenges Inventory

#### Challenge 1: The AtomSort global declaration (CRITICAL)

`syntactic/atoms.py` declares `AtomSort = DeclareSort("AtomSort")` at module level. This creates a Z3 sort object in Z3's global context at import time. Every sentence letter (`AtomVal(i)`) is a `Const` of this sort.

For a multi-solver design, this must become context-aware:
- Option A: Make `AtomSort` a lazy property initialized against the active solver backend
- Option B: Move `AtomSort` creation into `SemanticDefaults.__init__()` where `N` and solver context are known, passing it through the theory initialization chain
- Option C: Since `DeclareSort` is supported identically in cvc5.pythonic, defer this problem: for the Z3/cvc5 case it works without changes. Only becomes an issue for solvers that don't support uninterpreted sorts (like Bitwuzla).

#### Challenge 2: The Z3 context reset mechanism (MEDIUM)

`utils/context.py`'s `reset_z3_context()` function directly manipulates Z3's internal `_main_ctx` attribute. This mechanism is Z3-specific and fragile. Each solver backend handles context isolation differently:
- Z3: explicit context object (`z3.Context()`) or reset `_main_ctx`
- cvc5: no global context; each `Solver()` instance is isolated by default (no context sharing between solver instances)

For cvc5, the entire `Z3ContextManager` and `reset_z3_context()` would be no-ops (or simply absent), because cvc5 does not share state between solver instances.

#### Challenge 3: `assert_and_track` and unsat core (MEDIUM)

`ModelDefaults._setup_solver()` uses `solver.assert_and_track(constraint, c_id)` for every constraint to enable unsat core generation. cvc5 requires unsat core tracking to be enabled BEFORE adding assertions, via solver options:
```python
solver.setOption("produce-unsat-cores", "true")
```
The constraint labeling mechanism also differs: cvc5 uses named assumptions or assertion ids rather than explicit labels.

**Mitigation**: The unsat core feature is used for diagnostic display (`print_constraints=True`). It is not required for correct solving. The cvc5 adapter can implement `assert_tracked(c, label)` as a simple `add(c)` initially, with unsat core support added as a follow-on enhancement.

#### Challenge 4: `z3.is_true(val)` / `z3.is_false(val)` (LOW-MEDIUM)

These module-level functions in z3 check whether a Z3 expression evaluates to a concrete boolean. They are used heavily in model evaluation loops:
- `iterate/constraints.py`: lines 188, 235
- `iterate/models.py`: lines 91, 100, 114, 122, 288, 569, 571
- `models/structure.py`: lines 903-904

In cvc5.pythonic, the equivalent might be a method call (`val.is_true()`) or Python bool coercion (`bool(val)`). This is a localized substitution but appears in many places.

#### Challenge 5: `model.eval(expr, model_completion=True)` (LOW-MEDIUM)

Used in `builder/z3_utils.py`, `iterate/constraints.py`, and `models/structure.py`. In cvc5, the equivalent is `model.evaluate(expr, True)` (method named differently). A simple wrapper `def eval_in_model(model, expr, completion=True)` in the adapter layer handles this.

#### Challenge 6: z3 Set Theory operations (LOW for z3/cvc5 pair)

`models/semantic.py` uses `EmptySet`, `SetAdd`, `IsMember` from z3. cvc5.pythonic documents the same names with identical semantics. No changes needed for z3/cvc5 portability.

**However**: Bitwuzla does NOT support set theory. If Bitwuzla is a target, all set operations in `SemanticDefaults.python_set_to_z3()` and `z3_set_to_python_set()` would need pure-Python replacements. Since these are used only for display/debugging (total_fusion works on plain Python sets), this is manageable.

#### Challenge 7: `z3.is_const(expr)` in syntactic parsing (LOW)

Used in `syntactic/formulas.py` and `sentence.py` to detect atomic constants in prefix formula lists. In cvc5.pythonic, this would be `expr.is_const()` (method-based). Trivially wrapped.

#### Challenge 8: Custom ForAll/Exists via substitution (LOW for z3/cvc5 pair)

`utils/z3_helpers.py` implements `ForAll`/`Exists` by explicit enumeration using `z3.substitute`. Since `substitute` is available in cvc5.pythonic, this code works as-is for cvc5. Bitwuzla has no `substitute` function equivalent; this would require a different implementation path.

---

### 5. Python-Specific Considerations

#### Runtime Solver Detection

The recommended pattern is:
```python
# solver/_registry.py
import importlib
import os
from typing import Optional

_AVAILABLE_BACKENDS: dict[str, bool] = {}

def detect_solver(name: str) -> bool:
    """Check if a solver backend is available without importing it."""
    if name in _AVAILABLE_BACKENDS:
        return _AVAILABLE_BACKENDS[name]
    try:
        importlib.import_module(name)
        _AVAILABLE_BACKENDS[name] = True
    except ImportError:
        _AVAILABLE_BACKENDS[name] = False
    return _AVAILABLE_BACKENDS[name]

def get_default_solver() -> str:
    """Return the best available solver name."""
    preference_order = ["z3", "cvc5.pythonic", "bitwuzla"]
    for name in preference_order:
        if detect_solver(name):
            return name
    raise ImportError("No supported SMT solver found. Install z3-solver or cvc5.")
```

This pattern is lazy (no import at module load time), gracefully degrades, and can be extended with new backends.

#### Type Annotations for Solver-Agnostic Code

The ModelChecker already has a `models/types.py` and `utils/types.py` with Z3-specific type aliases:
```python
Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.BitVecRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver
```

For solver-agnostic code, these should be renamed with a neutral naming convention and made into `TypeAlias` entries that resolve to the active backend's types:
```python
# solver/types.py
from typing import Any
SolverExpr = Any        # solver-specific expression object
SolverModel = Any       # solver-specific model object
SolverInstance = Any    # solver-specific solver instance
SolverStatus = Any      # "sat" | "unsat" | "unknown" (solver-native constant)
```

This is pragmatic: since all solver expression objects are opaque to the theory layer anyway (they're only passed between API calls), `Any` is accurate. Precise types can be provided via `TYPE_CHECKING` guards:
```python
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    import z3
    SolverExpr = Union[z3.BoolRef, z3.ArithRef, z3.BitVecRef]
```

#### Package Dependencies and Installation

Currently ModelChecker depends on `z3-solver` from PyPI. The solver abstraction layer should:
1. Keep `z3-solver` as the default/required dependency (backward compatible)
2. Make `cvc5` an optional dependency with a clear install extra: `pip install model-checker[cvc5]`
3. The solver selection can be via environment variable (`MODEL_CHECKER_SOLVER=cvc5`) or settings dict key (`"solver": "cvc5"`)

---

### 6. Recommended Approach

**Protocol-Based Thin Solver Adapter with Module-Level Expression Aliases**

The design splits the problem into two layers with different strategies:

**Layer 1 - Solver Control (requires actual translation code)**:
Create a `model_checker/solver/` package with:
- `interface.py`: `AbstractSolver` ABC with methods: `add()`, `assert_tracked()`, `check_sat()`, `get_model()`, `get_unsat_core()`, `set_timeout()`, `push()`, `pop()`
- `z3_adapter.py`: Direct passthrough (thin wrapper, adds no overhead for the current z3 path)
- `cvc5_adapter.py`: Translates the 4-6 divergent method calls
- `registry.py`: Runtime detection, default selection

**Layer 2 - Formula Construction (nearly free for z3/cvc5)**:
Since `z3` and `cvc5.pythonic` share the same function names for all formula construction operations (`Function`, `BitVec`, `BitVecSort`, `And`, `Or`, `Not`, etc.), formula-level portability is achieved by:
- Centralizing imports in `solver/expressions.py` that re-exports from the active backend
- All theory files import from `model_checker.solver.expressions` instead of directly from `z3`

This approach has a critical advantage: the formula construction code in the 30+ operator files does not need to be rewritten. Only the import path changes.

**Phased implementation**:
1. Create `model_checker/solver/` package with Z3 adapter (behavior-identical to current code)
2. Change all `import z3` / `from z3 import ...` in non-test source to use `solver/expressions.py`
3. Implement cvc5 adapter
4. Add solver selection via settings
5. Run test suite equivalence checks

**What this does NOT require**:
- Rewriting any theory operator (`true_at`, `false_at`, `extended_verify`, etc.)
- Rewriting `SemanticDefaults` set operations (same names in z3 and cvc5.pythonic)
- Rewriting `utils/z3_helpers.py` ForAll/Exists logic
- Introducing a new formula representation language

**The only non-trivial rewrite** is `models/structure.py`'s `_setup_solver()` and `solve()` methods, which use `assert_and_track`, `unsat_core`, and `reason_unknown` -- all of which are encapsulated in one class and can be replaced by delegation to the solver adapter.

---

## Evidence and Examples

### Concrete API Comparison: Solver Control Interface

```python
# CURRENT (z3-specific, models/structure.py)
def _setup_solver(self, model_constraints):
    from z3 import Solver
    solver = Solver()
    for constraints, group_name in constraint_groups:
        for ix, constraint in enumerate(constraints):
            c_id = f"{group_name}{ix+1}"
            solver.assert_and_track(constraint, c_id)
    return solver

def solve(self, model_constraints, max_time):
    import z3
    self.solver = z3.Solver()
    self.solver.set("timeout", int(max_time * 1000))
    result = self.solver.check()
    if result == z3.sat:
        return ..., self.solver.model(), True, ...
    if self.solver.reason_unknown() == "timeout":
        return ..., None, False, ...
    return ..., self.solver.unsat_core(), False, ...

# PROPOSED (solver-agnostic, via adapter)
def _setup_solver(self, model_constraints):
    from model_checker.solver import create_solver
    solver = create_solver()  # returns Z3Adapter or CVC5Adapter based on settings
    for constraints, group_name in constraint_groups:
        for ix, constraint in enumerate(constraints):
            c_id = f"{group_name}{ix+1}"
            solver.assert_tracked(constraint, c_id)
    return solver

def solve(self, model_constraints, max_time):
    from model_checker.solver import create_solver, SAT, UNSAT
    self.solver = create_solver()
    self.solver.set_timeout(int(max_time * 1000))
    status = self.solver.check_sat()
    if status == SAT:
        return ..., self.solver.get_model(), True, ...
    if self.solver.is_timeout():
        return ..., None, False, ...
    return ..., self.solver.get_unsat_core(), False, ...
```

### Concrete API Comparison: Formula Construction (z3 vs cvc5.pythonic)

```python
# CURRENT logos/semantic.py
import z3
self.verify = z3.Function("verify", z3.BitVecSort(self.N), AtomSort, z3.BoolSort())
self.main_world = z3.BitVec("w", self.N)
x = z3.BitVec("frame_x", self.N)
frame_constraint = z3.Implies(self.possible(y), ...)

# PROPOSED logos/semantic.py (solver-agnostic)
from model_checker.solver.expressions import Function, BitVecSort, BitVec, BoolSort, Implies
# identical code, different import path
self.verify = Function("verify", BitVecSort(self.N), AtomSort, BoolSort())
self.main_world = BitVec("w", self.N)
x = BitVec("frame_x", self.N)
frame_constraint = Implies(self.possible(y), ...)
```

The formula construction code is **completely unchanged** -- only the import statement changes. This is the key advantage over pySMT's approach.

### The AtomSort Problem: Deferred for z3/cvc5 Case

For the immediate z3/cvc5 abstraction, `DeclareSort` works identically in both backends. The current code:
```python
# syntactic/atoms.py
from z3 import DeclareSort, Const
AtomSort = DeclareSort("AtomSort")
```
Becomes:
```python
# syntactic/atoms.py
from model_checker.solver.expressions import DeclareSort, Const
AtomSort = DeclareSort("AtomSort")
```
No semantic change. The `AtomSort` global initialization problem only arises for backends that don't support uninterpreted sorts (Bitwuzla).

---

## Confidence Level

**High confidence**:
- pySMT, smt-switch, and pysmtlib are all UNSUITABLE as abstraction layers for ModelChecker's architecture
- cvc5.pythonic has identical function names to z3 for all formula construction operations used in ModelChecker
- The set theory operations (`EmptySet`, `SetAdd`, `IsMember`) are identical in cvc5.pythonic
- `substitute()` is available in cvc5.pythonic (confirmed in documentation)
- The solver control layer (4-6 divergent methods) is the only place requiring actual translation code
- Protocol/ABC-based thin adapter with import aliasing is the right architectural approach
- z3 context reset mechanism (`context.py`) would be unnecessary for cvc5

**Medium confidence**:
- `z3.is_true()` / `z3.is_false()` equivalence in cvc5.pythonic (documented but exact call signature not verified against installed version)
- cvc5.pythonic `assert_and_track` absence is confirmed; the unsat core workaround for cvc5 is viable but requires testing
- `solver.set("timeout", ...)` vs cvc5 option-setting mechanism (cvc5 uses string options differently)
- cvc5 version 1.3.3 (Feb 2026) is the latest release; the pythonic API is included in the main `cvc5` pip package

**Low confidence**:
- Whether cvc5 produces equivalent results for the specific theory shapes used in ModelChecker (small N, BitVector-heavy, custom substitution-based quantification). Performance comparisons are untested.
- Exact feature parity of `is_const()` equivalence between z3 module-level function and cvc5 method-based equivalent
- Whether the Bitwuzla backend is worth targeting (missing arithmetic needed by bimodal theory's IntSort/IntVal usage)

---

## Appendix: Summary of z3 API Usage by Category

### Category 1: Formula Construction (identical in cvc5.pythonic)
`Function`, `BitVec`, `BitVecs`, `BitVecSort`, `BitVecVal`, `BoolSort`, `IntSort`, `IntVal`, `ArraySort`, `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists`, `substitute`, `simplify`, `BoolVal`, `EmptySet`, `SetAdd`, `IsMember`, `DeclareSort`, `Const`

All of these have identical names and semantics in `cvc5.pythonic`. The import path changes; the code does not.

### Category 2: Solver Control (requires adapter translation)
`z3.Solver()`, `solver.assert_and_track(c, label)`, `solver.check()`, `z3.sat`, `solver.model()`, `solver.unsat_core()`, `solver.reason_unknown()`, `solver.set("timeout", ms)`, `solver.push()`, `solver.pop()`, `solver.assertions()`

Concentrated in `models/structure.py` and `iterate/constraints.py`. The solver adapter handles this layer.

### Category 3: Model Evaluation (minor method-name differences)
`model.eval(expr, model_completion=True)` -> cvc5: `model.evaluate(expr, True)`
`z3.is_true(val)` -> cvc5: equivalent available (exact form needs verification)
`z3.is_false(val)` -> cvc5: equivalent available (exact form needs verification)
`z3.is_const(expr)` -> cvc5: `expr.is_const()` (method-based)

### Category 4: Type References (rename only)
`z3.BoolRef`, `z3.BitVecRef`, `z3.ModelRef`, `z3.ArithRef`, `z3.ExprRef`, `z3.FuncDeclRef`, `z3.CheckSatResult`, `z3.DatatypeRef`

These are used in type annotations. They can be replaced with `Any` in the generic layer, or with backend-specific imports under `TYPE_CHECKING` guards.

### Category 5: Z3-Context-Specific (to be replaced)
`z3._main_ctx`, `z3.clear_parser_cache()` in `utils/context.py`

This entire mechanism is unnecessary for cvc5. The adapter layer simply omits it.
