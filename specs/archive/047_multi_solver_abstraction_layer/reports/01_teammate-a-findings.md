# Teammate A Research Findings: State of the Art and Implementation Approaches

**Task**: 47 - Multi-Solver Abstraction Layer
**Focus**: 2026 SMT solver landscape, API design patterns, ModelChecker Z3 coupling
**Date**: 2026-03-29

---

## Key Findings

### 1. SMT Solver Landscape (2026)

The major SMT solvers in active use as of 2026, ranked by relevance to this project:

#### Z3 (Microsoft Research)
- **Version**: 4.15.8 (installed on this system)
- **Strengths**: Widest Python API, extensive theory support, dominant in academic/industrial use
- **Theories**: BitVectors, Arrays, Uninterpreted Functions (UF), Quantifiers, Arithmetic, Strings
- **Python API**: Native (`z3` module), most mature, uses operator overloading
- **Weakness**: Single-threaded per context, context management required for isolation between problems

#### cvc5
- **Version**: 1.2.0
- **Strengths**: Strongest quantifier reasoning, SyGuS synthesis, excellent SMT-COMP performance
- **Theories**: All Z3 theories plus bags, sequences, floating-point
- **Python API**: Two APIs available:
  1. **Base API** (`cvc5`): Lower-level, explicit `TermManager`, verbose
  2. **Pythonic API** (`cvc5.pythonic`): Intentionally mirrors Z3Py, drop-in-like compatibility
- **Critical finding**: cvc5's Pythonic API uses nearly identical function names to Z3: `DeclareSort`, `Const`, `Consts`, `Function`, `BitVec`, `BitVecs`, `Solver`, `sat`, `BoolSort`, `And`, `Or`, `Implies`, `Not`, `ForAll`, `Exists`

#### Bitwuzla
- **Strengths**: Fastest for pure BitVector + floating-point problems, multiple SMT-COMP division wins (43/71 in 2020, 32/48 in 2022, 26/56 in 2023)
- **Theories**: BitVectors, floating-point, Arrays, UF - **NOT** arithmetic
- **Python API**: Available but less mature than Z3/cvc5
- **Relevance**: High for the current project (which uses BitVectors heavily), but missing arithmetic theory

#### Yices2 (SRI International)
- **Version**: 2.6.4 (last released 2021)
- **Strengths**: Excellent linear/nonlinear arithmetic, highly optimized for certain theories
- **Theories**: UF, arithmetic (linear/nonlinear), BitVectors, scalars, tuples
- **Python API**: Limited, less maintained
- **Status concern**: No major release since October 2021 suggests lower priority for integration

---

### 2. Multi-Solver Abstraction Framework: pySMT

**pySMT** (v0.9.6, released June 2024) is the principal existing multi-solver Python abstraction:

**Architecture**:
- Solver-agnostic internal formula representation using `FNode`/`FNodeContent` trees
- Bidirectional converters per solver (pySMT formula <-> solver AST)
- Standard interface: `Symbol()`, `And()`, `is_sat()`, `get_model()`
- Portfolio solving: parallel execution across multiple solvers

**Supported solvers**: MathSAT, Z3, cvc5, Yices2, CUDD, PicoSAT, Boolector

**Critical limitations for ModelChecker**:
1. pySMT formulas are **immutable objects** - they don't support the dynamic Z3-style function construction that ModelChecker uses heavily (`z3.Function("verify", BitVecSort(N), AtomSort, BoolSort())`)
2. pySMT does not support Z3's `DeclareSort` for uninterpreted sorts, which is used for `AtomSort`
3. No support for Z3's explicit quantifier-by-substitution pattern (used in `ForAll`/`Exists` in `z3_helpers.py`)
4. pySMT's canonical internal representation would require rewriting all semantic theories

**Verdict**: pySMT is unsuitable as a direct abstraction layer for ModelChecker without a major rewrite of theory semantics. The ModelChecker's architecture is too deeply coupled to Z3's object model.

---

### 3. The cvc5 Pythonic API Opportunity

The cvc5 Pythonic API deserves special attention because it **deliberately mirrors Z3's Python API**:

```python
# Z3 code:
from z3 import DeclareSort, Const, Function, BitVecSort, BoolSort, Solver
U = DeclareSort("U")
x = Const("x", U)
f = Function("f", U, U)

# cvc5 Pythonic code (nearly identical):
from cvc5.pythonic import DeclareSort, Const, Function, BitVecSort, BoolSort, Solver
U = DeclareSort("U")
x = Const("x", U)
f = Function("f", U, U)
```

Both use identical function names for: `DeclareSort`, `Const`, `Consts`, `BitVec`, `BitVecs`, `BitVecSort`, `BoolSort`, `Function`, `Solver`, `sat`, `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists`.

**What cvc5 Pythonic does NOT support** (vs Z3):
- Quantifier instantiation patterns
- Pseudo-boolean constraints (AtMost, AtLeast)
- Unsatisfiable cores (critical for ModelChecker's `unsat_core` feature)
- Custom propagation hooks
- HTML integration
- `assert_and_track()` equivalent

---

### 4. Current ModelChecker Z3 Coupling Analysis

The Z3 API surface used in ModelChecker falls into distinct coupling categories:

#### Category A: Core Constraint Expression (Most Pervasive)
Z3 types and expressions appear throughout the codebase as function argument and return types. Over **422 Z3 API call sites** exist in non-test source files.

**Key files with heavy Z3 coupling**:
- `/code/src/model_checker/models/semantic.py` - Base `SemanticDefaults` uses `BitVecSort`, `BitVecVal`, `EmptySet`, `SetAdd`, `IsMember`, `simplify`, `BitVecRef`, `BoolRef` at top-level import
- `/code/src/model_checker/models/structure.py` - `ModelDefaults.solve()` uses `z3.Solver`, `z3.sat`, `solver.assert_and_track()`, `solver.unsat_core()`
- `/code/src/model_checker/syntactic/atoms.py` - `DeclareSort("AtomSort")` and `Const()` used to define the global `AtomSort` and `AtomVal()` - **this is the most fundamental coupling point**
- `/code/src/model_checker/utils/z3_helpers.py` - Custom `ForAll`/`Exists` implemented via `z3.substitute` and `z3.BitVecVal` enumeration

#### Category B: Theory-Level Z3 Usage
Each theory's semantics class directly constructs Z3 expressions:

**logos/semantic.py** `LogosSemantics.__init__()`:
```python
self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
self.falsify = z3.Function("falsify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
self.possible = z3.Function("possible", z3.BitVecSort(self.N), z3.BoolSort())
self.main_world = z3.BitVec("w", self.N)
```

**bimodal/semantic.py**: Similar pattern with additional `IntVal` for time points (`M`).

#### Category C: Solver Control Flow
- `structure.py`: `solver.check()`, `z3.sat`, `solver.model()`, `solver.unsat_core()`, `solver.assert_and_track()`, `solver.set("timeout", ...)`, `solver.push()`, `solver.pop()`
- `iterate/constraints.py`: Clones solver assertions, `solver.assertions()`

#### Category D: Model Evaluation
- `structure.py` `extract_verify_falsify_state()`: `z3_model.eval(expr, model_completion=True)`, `z3.is_true(val)`
- `builder/z3_utils.py`: `old_model.eval(var, model_completion=True)`, `var != old_value`

#### Category E: Custom Quantification via Substitution
`utils/z3_helpers.py` implements `ForAll`/`Exists` by enumerating all possible `BitVecVal` values and using `z3.substitute`. This is a Z3-specific technique that avoids native Z3 quantifiers for performance reasons. **This pattern is deeply solver-specific**.

---

### 5. Coupling Points That Would Need Abstraction

In priority order (hardest to easiest):

1. **AtomSort** (`syntactic/atoms.py`): Global `DeclareSort("AtomSort")` used throughout. Every sentence letter is a `Const` of this sort. This is the **deepest coupling point** - it permeates the type system.

2. **ForAll/Exists substitution** (`utils/z3_helpers.py`): The custom quantification approach using `z3.substitute` has no direct equivalent in other solver APIs. Would need solver-specific implementations.

3. **SemanticDefaults bit vector operations** (`models/semantic.py`): Top-level imports of `BitVecSort`, `BitVecVal`, `EmptySet`, `SetAdd`, `IsMember`, `simplify`, `BitVecRef`, `BoolRef` - used in the base class for all theories.

4. **Theory Function Declarations**: `z3.Function("verify", ...)`, `z3.Function("falsify", ...)`, `z3.BitVec("w", N)` in every theory's `__init__`.

5. **Solver control**: `z3.Solver()`, `solver.assert_and_track()`, `solver.check()`, `z3.sat`, `solver.model()`, `solver.unsat_core()` - concentrated in `models/structure.py`.

6. **Model evaluation**: `z3_model.eval()`, `z3.is_true()` - used in structure.py and iterate/.

---

## Recommended Approach

### Option 1: Thin Solver Adapter Layer (Recommended)

Create a `solver_interface` module that provides a **thin adapter** specifically mapping the Z3-compatible subset used by ModelChecker to equivalent calls for other solvers. This is different from pySMT's approach of building a new formula language.

**Key insight**: cvc5's Pythonic API already mirrors Z3's API so closely that the adapter for cvc5 would be nearly trivial for expression-building functions. The main divergence points are:
1. The `AtomSort` / `DeclareSort` pattern (cvc5 supports this identically)
2. `assert_and_track()` - unique to Z3 (cvc5 has `getUnsatCore()` but different setup)
3. The custom `ForAll`/`Exists` via substitution (solver-independent Python code, already works for both)

**Architecture**:
```
model_checker/
  solver/
    interface.py      # Abstract solver interface (Protocol class)
    z3_adapter.py     # Z3 backend (current behavior, thin wrapper)
    cvc5_adapter.py   # cvc5 backend (cvc5.pythonic, minimal translation)
    types.py          # Solver-agnostic type aliases
```

**Phased approach**:
- Phase 1: Introduce `solver/interface.py` with Protocol defining the interface
- Phase 2: Move Z3 import consolidation (all `import z3` -> through interface)
- Phase 3: Implement cvc5 adapter for the used subset
- Phase 4: Test equivalence on existing theories

### Option 2: SMT-LIB Text Layer

Generate SMT-LIB v2.7 text from constraints and invoke any solver via subprocess. Pros: maximum portability. Cons: loses incremental solving, requires serialization/deserialization, likely 10-100x slower for iterative model finding.

### Option 3: pySMT Integration

Rewrite all theory semantics using pySMT's formula language. Pros: solver-agnostic. Cons: massive rewrite (all theory operators, all semantic classes), pySMT lacks `DeclareSort`, loses unsat_core tracking, loses current performance characteristics. **Not recommended**.

---

## Evidence / Examples

### Concrete API Comparison for ModelChecker's Core Pattern

**Current Z3 code** (in `LogosSemantics.__init__`):
```python
import z3
self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
self.main_world = z3.BitVec("w", self.N)
x = z3.BitVec("frame_x", self.N)
self.frame_constraints = [z3.Implies(self.possible(y), ...)]
```

**Equivalent cvc5 Pythonic code**:
```python
from cvc5.pythonic import Function, BitVecSort, BoolSort, BitVec, DeclareSort, Const
AtomSort_cvc5 = DeclareSort("AtomSort")
verify = Function("verify", BitVecSort(N), AtomSort_cvc5, BoolSort())
main_world = BitVec("w", N)
x = BitVec("frame_x", N)
# And, Or, Implies, Not all work identically
```

The API calls are **identical** except for the import path.

**The adapter for cvc5 would be essentially a module alias** for the expression-building API. The main divergence requiring actual translation code is:
1. `solver.assert_and_track(constraint, label)` -> cvc5 equivalent requires different unsat core setup
2. `solver.unsat_core()` -> `solver.getUnsatCore()` in cvc5
3. `solver.reason_unknown()` -> cvc5 equivalent via `solver.getResult().isUnknown()`

### The AtomSort Problem

The most fundamental coupling is in `syntactic/atoms.py`:
```python
from z3 import DeclareSort, Const
AtomSort = DeclareSort("AtomSort")  # global module-level declaration

def AtomVal(i):
    return Const(f"AtomSort!val!{i}", AtomSort)
```

This creates a Z3 sort at module import time. Every sentence letter is an instance of this sort. To abstract over solvers, this must become solver-context-aware: each solver backend creates its own `AtomSort` equivalent, and the `AtomVal` function must dispatch to the active solver.

---

## Confidence Level

**High confidence**:
- The 422+ Z3 API call sites indicate deep, pervasive coupling that cannot be abstracted by a small shim
- cvc5's Pythonic API is the most compatible alternative, sharing most function names
- The `AtomSort` global declaration is the most fundamental architectural coupling point
- `assert_and_track()` + unsat cores is a Z3-specific feature that would require feature negotiation or degradation for other solvers

**Medium confidence**:
- The custom `ForAll`/`Exists` substitution approach in `z3_helpers.py` could work with cvc5 since it uses pure Python enumeration with Z3 formula objects - but cvc5's Pythonic `substitute()` function availability needs verification
- A thin adapter layer is implementable within a few hundred lines of code
- Feature parity for the subset used by ModelChecker is achievable for Z3 and cvc5

**Low confidence**:
- Whether performance (solving time) would be equivalent or better with cvc5 for the specific problem shapes ModelChecker generates (small N, BitVector-heavy, custom quantification by substitution)
- Whether Bitwuzla's lack of arithmetic theory matters (the current theories use only BitVectors, not arithmetic - but bimodal uses `IntVal` for time points)

---

## Appendix: Z3 Usage Inventory by File

| File | Z3 Usage Type | Abstraction Difficulty |
|------|--------------|----------------------|
| `syntactic/atoms.py` | DeclareSort, Const (global) | HIGH - fundamental type |
| `models/semantic.py` | BitVecSort, BitVecVal, Set ops, BoolRef | MEDIUM - concentrated |
| `models/structure.py` | Solver, sat, assert_and_track, unsat_core | MEDIUM - concentrated |
| `models/constraints.py` | ExprRef isinstance check | LOW - type check only |
| `models/types.py` | z3.BoolRef, z3.BitVecRef type aliases | LOW - types only |
| `utils/z3_helpers.py` | substitute, BitVecVal enumeration | MEDIUM - solver-specific |
| `utils/bitvector.py` | BitVecRef, BitVecVal | LOW - display only |
| `iterate/constraints.py` | z3.Solver, z3.BoolRef, z3.ModelRef | MEDIUM - concentrated |
| `iterate/base.py` | z3.ModelRef, z3.BoolRef | LOW - type annotations |
| `theory_lib/logos/semantic.py` | z3.Function, z3.BitVec, z3.BitVecs | MEDIUM - per-theory |
| `theory_lib/bimodal/semantic.py` | z3.Function, z3.IntVal | MEDIUM - per-theory |
| `theory_lib/*/operators.py` | z3.BitVec, z3.And, z3.Implies, z3.Not | LOW - mostly combinators |
