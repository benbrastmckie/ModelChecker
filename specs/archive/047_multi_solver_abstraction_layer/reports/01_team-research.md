# Research Report: Task #47

**Task**: Implement multi-solver abstraction layer for z3, cvc5, and future constraint solvers
**Date**: 2026-03-29
**Mode**: Team Research (2 teammates)

## Summary

Both teammates converge strongly on the same recommendation: a **thin protocol-based solver adapter** with **module-level expression aliasing**, leveraging cvc5's Pythonic API which deliberately mirrors Z3's Python API. Existing multi-solver frameworks (pySMT, smt-switch, pysmtlib) are all unsuitable for ModelChecker's architecture. The key insight is that formula construction code (30+ operator files) needs only import path changes, while actual translation code is needed only for the solver control layer (4-6 divergent methods concentrated in 2-3 files).

## Key Findings

### SMT Solver Landscape (2026)

| Solver | Version | Python API | Strengths | Limitations |
|--------|---------|------------|-----------|-------------|
| Z3 | 4.15.8 | Native, most mature | Widest theory support, dominant ecosystem | Single-threaded per context |
| cvc5 | 1.3.3 | Base + Pythonic (Z3-compatible) | Strongest quantifier reasoning, SMT-COMP performance | Pythonic API missing `assert_and_track` |
| Bitwuzla | Latest | Available but less mature | Fastest for pure BitVector problems | No arithmetic theory, no set theory |
| Yices2 | 2.6.4 | Limited | Good arithmetic | No major release since 2021 |

### Existing Multi-Solver Libraries: All Unsuitable

| Library | Why Unsuitable |
|---------|---------------|
| **pySMT** (v0.9.6) | Introduces own `FNode` formula representation; no `DeclareSort` support; would require rewriting all theory semantics |
| **smt-switch** | C++-centric; Python bindings are secondary; installation requires building C++ per solver |
| **pysmtlib** | Subprocess-based SMT-LIB text; eliminates incremental solving and unsat cores |

**Lesson**: The right abstraction is NOT a new formula representation. It is a thin interface over solver-specific objects, keeping native solver objects intact.

### The cvc5 Pythonic API Opportunity (Critical Finding)

The `cvc5.pythonic` module (included in `cvc5` pip package since v1.1+) deliberately mirrors Z3's Python API. ALL formula construction functions used in ModelChecker have **identical names and semantics**:

`DeclareSort`, `Const`, `Function`, `BitVec`, `BitVecs`, `BitVecSort`, `BitVecVal`, `BoolSort`, `IntSort`, `IntVal`, `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists`, `substitute`, `simplify`, `EmptySet`, `SetAdd`, `IsMember`, `Solver`, `sat`, `unsat`, `unknown`

This means formula construction code in 30+ operator files needs only an import path change.

### Current Z3 Coupling Analysis

Over **422 Z3 API call sites** exist in non-test source files, categorized into 5 layers:

**Layer 1 - Formula Construction (identical in cvc5.pythonic)**:
All `Function`, `BitVec`, `And`, `Or`, `Not`, `Implies`, etc. used in theory semantics and operators. **No code changes needed** -- only import path changes.

**Layer 2 - Solver Control (4-6 divergent methods)**:
Concentrated in `models/structure.py` and `iterate/constraints.py`:

| Z3 Method | cvc5 Equivalent | Notes |
|-----------|-----------------|-------|
| `solver.assert_and_track(c, label)` | Absent in cvc5.pythonic | Need manual tracking |
| `solver.unsat_core()` | `solver.getUnsatCore()` (base API) | Different setup |
| `solver.reason_unknown()` | Different API | Different name |
| `solver.set("timeout", ms)` | `solver.setOption("tlimit-per", str(ms))` | Different syntax |
| `model.eval(expr, model_completion=True)` | `model.evaluate(expr, True)` | Method rename |
| `z3.is_true(val)` / `z3.is_false(val)` | Potentially method-based | Needs verification |

**Layer 3 - AtomSort Global Declaration**:
`syntactic/atoms.py` declares `AtomSort = DeclareSort("AtomSort")` at module level. Since `DeclareSort` is identical in cvc5.pythonic, this works for the z3/cvc5 case with just an import change. Only becomes problematic for solvers lacking uninterpreted sorts (Bitwuzla).

**Layer 4 - Custom ForAll/Exists via Substitution**:
`utils/z3_helpers.py` implements quantification by enumerating `BitVecVal` values and using `z3.substitute`. Since `substitute` is available in cvc5.pythonic, this works as-is. Only problematic for Bitwuzla (no `substitute`).

**Layer 5 - Z3 Context Management**:
`utils/context.py` manipulates Z3's internal `_main_ctx`. This is entirely Z3-specific. cvc5 has per-instance isolation by default -- no context management needed.

### Coupling Points by File (Priority Order)

| File | Z3 Usage | Abstraction Difficulty |
|------|----------|----------------------|
| `syntactic/atoms.py` | DeclareSort, Const (global) | HIGH - fundamental type |
| `models/semantic.py` | BitVecSort, BitVecVal, Set ops, BoolRef | MEDIUM - concentrated |
| `models/structure.py` | Solver, sat, assert_and_track, unsat_core | MEDIUM - concentrated |
| `utils/z3_helpers.py` | substitute, BitVecVal enumeration | MEDIUM - solver-specific |
| `iterate/constraints.py` | z3.Solver, z3.BoolRef, z3.ModelRef | MEDIUM - concentrated |
| `models/types.py` | z3.BoolRef, z3.BitVecRef type aliases | LOW - types only |
| `theory_lib/logos/semantic.py` | z3.Function, z3.BitVec, z3.BitVecs | MEDIUM - per-theory |
| `theory_lib/bimodal/semantic.py` | z3.Function, z3.IntVal | MEDIUM - per-theory |
| `theory_lib/*/operators.py` | z3.BitVec, z3.And, z3.Implies, z3.Not | LOW - mostly combinators |
| `utils/bitvector.py` | BitVecRef, BitVecVal | LOW - display only |

## Synthesis

### Conflicts Resolved

**No significant conflicts** between teammates. Both independently concluded:
1. pySMT, smt-switch, pysmtlib are unsuitable
2. cvc5.pythonic is the natural fit due to API mirroring
3. Protocol/ABC thin adapter is the right pattern
4. Formula construction code needs only import changes
5. Solver control layer is the only substantive adapter work

Minor divergence: Teammate A suggested Protocol class, Teammate B explored both Protocol and ABC. **Resolution**: ABC is slightly preferred for the solver control interface (concrete method stubs, more explicit), while formula construction uses module-level import aliasing (zero overhead).

### Gaps Identified

1. **Performance comparison**: Neither teammate verified whether cvc5 produces equivalent performance for ModelChecker's specific problem shapes (small N, BitVector-heavy, custom substitution-based quantification)
2. **cvc5.pythonic exact API verification**: Some functions (`is_true`, `is_false`, `is_const`) need verification against installed cvc5 version
3. **Bitwuzla feasibility**: Missing arithmetic (needed by bimodal's `IntVal`), set theory, and `substitute` make it a poor fit without significant additional work -- likely not worth targeting initially

### Recommendations

1. **Target z3 + cvc5 initially**. Bitwuzla and Yices2 can be added later but have significant API gaps.

2. **Architecture**: Create `model_checker/solver/` package with:
   - `interface.py` - ABC defining solver control interface
   - `expressions.py` - Re-exports formula construction functions from active backend
   - `z3_adapter.py` - Transparent passthrough (zero overhead for current z3 path)
   - `cvc5_adapter.py` - Translates 4-6 divergent solver control methods
   - `registry.py` - Runtime detection, default selection, configuration
   - `types.py` - Solver-agnostic type aliases

3. **Phased approach**:
   - Phase 1: Create `solver/` package, Z3 adapter, expressions module (behavior-identical)
   - Phase 2: Change all `import z3` to `from model_checker.solver.expressions import ...`
   - Phase 3: Implement cvc5 adapter for solver control layer
   - Phase 4: Add solver selection via settings/env var
   - Phase 5: Test equivalence on existing theories

4. **What does NOT change**:
   - No theory operator rewrites needed
   - No `SemanticDefaults` set operation rewrites
   - No `z3_helpers.py` ForAll/Exists rewrites
   - No new formula representation language

5. **Dependencies**:
   - Keep `z3-solver` as required dependency
   - Make `cvc5` optional: `pip install model-checker[cvc5]`
   - Solver selection via `MODEL_CHECKER_SOLVER=cvc5` env var or settings dict

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | State of the art, implementation approaches, codebase coupling analysis | completed | high |
| B | Alternative patterns, prior art libraries, integration challenges | completed | high |

## References

- Z3 Python API: z3-prover/z3 on GitHub
- cvc5 Pythonic API: cvc5/cvc5_pythonic_api on GitHub, included in `cvc5` pip package since v1.1+
- pySMT: pysmt/pysmt on GitHub (v0.9.6, June 2024)
- smt-switch: stanford-centaur/smt-switch on GitHub
- SMT-LIB v2.7 standard: smtlib.cs.uiowa.edu
