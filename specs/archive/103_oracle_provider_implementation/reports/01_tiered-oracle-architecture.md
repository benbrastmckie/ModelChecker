# Tiered Oracle Architecture for Task 103

- **Task**: 103 - OracleProvider implementation with tiered countermodel search
- **Type**: Cross-repository architecture analysis
- **Date**: 2026-06-01
- **Sources**: BimodalLogic task 226 (z3_oracle/ implementation), ModelChecker task 106 ADR, BimodalHarness tasks 19/28 (OracleProvider/VerifierProvider protocols)

## Executive Summary

BimodalLogic task 226 built a standalone quantifier-free Z3 countermodel generator (`z3_oracle/`, 1349 lines, phases 1-3 complete) that was intended to bypass the ModelChecker refactoring dependency. This report proposes absorbing that work into ModelChecker task 103 as a fast Tier 1 alongside the existing quantified solver as Tier 2, restoring the original three-repo signal architecture (BimodalLogic = positive signal, ModelChecker = negative signal, BimodalHarness = consumer).

## Problem: Duplicated Negative Signal Infrastructure

The original cross-repository architecture assigns clear roles:

| Repository | Signal | Mechanism |
|------------|--------|-----------|
| BimodalLogic | Positive (proofs) | Lean tableau proof search |
| ModelChecker | Negative (countermodels) | Z3-based countermodel generation |
| BimodalHarness | Consumer | OracleProvider/VerifierProvider protocols |

BimodalLogic task 226 broke this separation by building a second Z3 countermodel generator inside BimodalLogic. The motivation was pragmatic: ModelChecker tasks 100-105 (the refactoring pipeline) were all NOT STARTED, creating a hard dependency block. Task 226's plan states explicitly: "external dependency on ModelChecker creates a hard block — the standalone approach avoids this."

The result is two independent Z3 oracle implementations:

| Implementation | Location | Encoding | Speed | Completeness |
|---------------|----------|----------|-------|-------------|
| ModelChecker existing | `theory_lib/bimodal/semantic.py` (3038 lines) | Quantified (ForAll/Exists) | 2-30s per formula | More thorough |
| BimodalLogic task 226 | `z3_oracle/src/bmlogic_oracle/` (1349 lines) | Quantifier-free finite instantiation | 1-50ms per formula | Bounded-incomplete |

These are complementary, not competing. Moving task 226's code into ModelChecker and structuring `find_countermodel()` as a tiered dispatch gives a single package that is both fast and thorough.

## BimodalLogic Task 226: What Exists

Task 226 completed phases 1-3. The `z3_oracle/` package at `/home/benjamin/Projects/BimodalLogic/z3_oracle/` contains:

```
z3_oracle/
├── pyproject.toml          # Package: bmlogic-z3-oracle, entry point registered
├── src/bmlogic_oracle/
│   ├── __init__.py         #  58 lines
│   ├── formula.py          # 400 lines — Formula AST, JSON parser (6 tags + derived)
│   ├── encoding.py         # 320 lines — FrameEncoder: QF frame axioms + truth conditions
│   ├── oracle.py           # 207 lines — Progressive deepening driver
│   ├── countermodel.py     # 248 lines — StructuredCountermodel + Z3 model extraction
│   └── provider.py         # 116 lines — OracleProvider protocol wrapper
└── tests/                  # (present but not inventoried)
```

### Quantifier-Free Encoding Approach

Where ModelChecker's `BimodalSemantics` uses Z3 `ForAll`/`Exists` quantifiers (30+ quantifier calls in `semantic.py`), task 226's `FrameEncoder` replaces every quantifier with explicit finite conjunction/disjunction over bounded domains:

**Frame axioms** (finite conjunction over N worlds, M time steps):
- `nullity_identity`: `task_rel(w, 0, u) <-> (w == u)` for all w, u in {0..N-1}
- `forward_comp`: `task_rel(w, d1+d2, u) <-> Or_v[task_rel(w,d1,v) ∧ task_rel(v,d2,u)]` for all w, u, d1, d2
- `converse`: `task_rel(w, -d, u) <-> task_rel(u, d, w)` for all w, u, d

**Truth conditions** (finite expansion):
- `box(φ)`: `And` over all N^M histories σ of `truth(φ, σ, t)`
- `until(φ, ψ)`: `Or` over t' >= t of `[truth(ψ, σ, t') ∧ And over t'' in [t,t') of truth(φ, σ, t'')]`
- `since(φ, ψ)`: symmetric past version

This eliminates quantifier instantiation overhead — the dominant cost in ModelChecker's solver. The tradeoff is that the encoding size grows as O(N^M) in the number of histories, but at small bounds (N=2, M=3 → 8 histories) this is trivial for Z3's SAT solver.

### Progressive Deepening Schedule

```python
DEEPENING_SCHEDULE = [
    (2, 3),   # 8 histories, fast
    (3, 3),   # 27 histories
    (3, 4),   # 81 histories
    (4, 4),   # 256 histories, still SAT-tractable
]
```

The schedule starts at M=3, not M=2. Task 226 discovered that M=2 produces false countermodels for Since/Until formulas: evaluating at t=0 makes Since vacuously true (no past exists) and evaluating at t=1 makes Until vacuously true (no future exists). The fix is to evaluate at the middle time step (t = M//2) with M >= 3, ensuring both past and future time points exist.

### Shift-Closure Enforcement

The bimodal TM semantics requires the history set Ω to be shift-closed: if σ ∈ Ω and d >= 0, then time_shift(σ, d) ∈ Ω. Task 226 enforces this as a Z3 constraint: for every history σ, if σ is valid (respects task_rel), then its cyclic 1-shift (σ[1], σ[2], ..., σ[M-1], σ[0]) must also be valid. Without this constraint, the solver finds spurious countermodels that exploit non-shift-closed history sets.

### StructuredCountermodel Output

Task 226's `StructuredCountermodel` dataclass captures:
- `n_worlds`, `m_steps`: frame dimensions
- `task_rel`: dict mapping (w, d, u) → bool (ternary, matching ADR Decision 6)
- `histories`: list of valid histories (respecting task_rel)
- `valuation`: dict mapping (w, t, atom_name) → bool
- `falsifying_history`, `falsifying_time`: the specific point where the formula is false
- `validate()`: post-hoc frame axiom checking (nullity, composition, converse, history validity)

This aligns with the StructuredCountermodel schema specified in the task 106 ADR pipeline diagram (lines 296-309 of `04_architectural-decisions.md`). The main difference: task 226 uses Python dict keys `(w, d, u)` while the ADR specifies JSON triples `{"source": s, "duration": d, "target": u}`. The serialization adapter is straightforward.

### OracleProvider Conformance

Task 226's `provider.py` already implements:
- `find_countermodel(formula_json, timeout_ms)` → `StructuredCountermodel | None`
- `is_valid(formula_json)` → `bool | None` (False if countermodel found, None if unknown)
- `find_countermodels_batch(formulas_json, timeout_ms)` → batch variant
- Entry point registration: `bimodal_harness.oracle_providers` → `z3_oracle = "bmlogic_oracle.provider:Z3OracleProvider"`

This is close to BimodalHarness's `OracleProvider` protocol but not fully conformant — it's missing `provider_id`, `provider_version`, `semantics_version`, `supported_frame_classes`, `capabilities`, and `validate_self()`. These would be added during the port.

## ModelChecker Existing Infrastructure

The quantified solver in `theory_lib/bimodal/semantic.py` (3038 lines) provides:

- **`BimodalSemantics`** (line 49): All Z3 constraint builders. Uses `ForAll`/`Exists` for frame axioms (nullity, forward composition, converse) and truth conditions. Includes sophisticated features not in the QF encoding: capped Skolem abundance constraints, convex world ordering, world interval constraints, domain enumeration.
- **`BimodalProposition`** (line ~1913): `find_extension()` for truth profiles.
- **`BimodalStructure`** (line 2222): `extract_model_elements()` for model extraction. Z3 solving happens in `__init__`.
- **`extract_model_elements()`** (line 1587): Extracts world histories, task relations, truth valuations from Z3 models.

The existing solver handles edge cases the QF encoding may not: arbitrary frame sizes, complex operator interactions at deep nesting, the full Skolem abundance machinery. It is slower because Z3's quantifier instantiation engine must find the right ground instances, but it is more thorough — it can find countermodels at frame sizes where exhaustive QF enumeration would be impractical.

### Key ADR Decisions Already Made (Task 106)

The following decisions from `04_architectural-decisions.md` apply directly to the tiered design:

1. **Decision 3** (two-layer package): thin OracleProvider skin over preserved Z3 core — the `fast/` QF module is a natural third layer
2. **Decision 5** (boundary buffer): `M = max(temporal_depth + 2, 3)` — applies to Tier 2; task 226 already uses M >= 3 minimum for Tier 1
3. **Decision 6** (ternary task_rel): both implementations already use (source, duration, target) triples
4. **Decision 9** (Z3 isolation): fresh instance per call — Tier 1 already creates fresh `FrameEncoder`/`Solver` per deepening step; Tier 2 creates fresh `BimodalSemantics`

## Proposed Tiered Architecture

### Dispatch Flow

```
find_countermodel(formula_json, frame_class, timeout_ms)
    │
    │  Parse formula, compute temporal_depth
    │
    ├── Tier 1: QF finite instantiation (budget: 80% of timeout_ms)
    │   │
    │   │  Progressive deepening: (N=2,M=3) → (N=3,M=3) → (N=3,M=4) → (N=4,M=4)
    │   │  Each step: fresh FrameEncoder + z3.Solver, QF constraints, SAT check
    │   │
    │   ├── SAT → extract StructuredCountermodel, return immediately
    │   │         (tag: tier_used="fast", search_time_ms=<elapsed>)
    │   │
    │   └── All bounds UNSAT or timeout → fall through to Tier 2
    │
    ├── Tier 2: Quantified BimodalSemantics (budget: remaining timeout_ms)
    │   │
    │   │  json_to_prefix() → Sentence.from_prefix() → Syntax → BimodalSemantics(N, M)
    │   │  M = max(temporal_depth + 2, 3) per ADR Decision 5
    │   │  Fresh BimodalSemantics instance per ADR Decision 9
    │   │
    │   ├── SAT → extract via extract_model_elements(), serialize, return
    │   │         (tag: tier_used="thorough", search_time_ms=<elapsed>)
    │   │
    │   └── UNSAT or timeout → return None
    │
    └── None (formula may be valid, or both tiers insufficient)
```

### Package Layout

```
bmlogic_oracle/
├── __init__.py               # Public: Z3OracleProvider
├── provider.py               # OracleProvider: tiered dispatch, protocol conformance
├── translation.py            # json_to_prefix(), temporal_depth() (from task 102)
├── serialization.py          # StructuredCountermodel → JSON serialization
├── fast/                     # Tier 1: ported from BimodalLogic z3_oracle/
│   ├── __init__.py
│   ├── encoding.py           # FrameEncoder (QF frame axioms + truth conditions)
│   ├── formula.py            # Formula AST + JSON parser
│   ├── oracle.py             # Progressive deepening driver
│   └── countermodel.py       # StructuredCountermodel extraction from QF solver
└── theory_lib/bimodal/       # Tier 2: existing quantified Z3 core (preserved)
    ├── semantic.py           # BimodalSemantics, BimodalProposition, BimodalStructure
    ├── operators.py          # Operator definitions
    ├── examples.py           # 43-example evaluation suite
    └── tests/                # Full test suite
```

### What the Port Requires

The BimodalLogic `z3_oracle/` code is self-contained Python with a single external dependency (`z3-solver`). Porting involves:

1. **Move 5 files** from `BimodalLogic/z3_oracle/src/bmlogic_oracle/` to `ModelChecker/bmlogic_oracle/fast/`:
   - `encoding.py` (320 lines) → `fast/encoding.py`
   - `formula.py` (400 lines) → `fast/formula.py`
   - `oracle.py` (207 lines) → `fast/oracle.py`
   - `countermodel.py` (248 lines) → `fast/countermodel.py`
   - `provider.py` (116 lines) → absorbed into top-level `provider.py` as Tier 1 dispatch

2. **Adjust imports**: change `from .formula import ...` to `from .fast.formula import ...` in the dispatch layer. Internal imports within `fast/` stay unchanged.

3. **Unify StructuredCountermodel**: task 226's `StructuredCountermodel` and the ADR's serialization format are close but not identical. The top-level `serialization.py` should normalize both Tier 1 and Tier 2 outputs to the same JSON schema.

4. **Add protocol conformance**: `provider_id`, `provider_version`, `semantics_version`, `supported_frame_classes`, `capabilities`, `validate_self()` — not present in task 226's provider.

### Formula Parser Divergence

Task 226's `formula.py` handles 11 JSON tags (6 primitive + 5 derived: imp, iff, dia, top, bot) and reduces derived tags to primitives during parsing. Task 102's `json_to_prefix()` maps 6 JSON tags to ModelChecker's prefix-list format for `Sentence.from_prefix()`.

These are two different formula entry points for two different solvers:
- **Tier 1** uses task 226's `parse_formula_json()` → `Formula` AST → `FrameEncoder.truth()`
- **Tier 2** uses task 102's `json_to_prefix()` → `Sentence.from_prefix()` → `Syntax` → `BimodalSemantics`

Both must handle the same input JSON, but they parse into different internal representations. This is fine — the dispatch layer passes `formula_json` to whichever tier runs next; each tier owns its own parsing.

The one requirement is that both parsers agree on derived-operator expansion. Task 226 expands: `imp(A,B)` → `or(neg(A), B)`, `bot` → `and(atom("__bot_p"), neg(atom("__bot_p")))`, `dia(φ)` → `neg(box(neg(φ)))`. Task 102's `json_to_prefix()` maps to ModelChecker's internal operator names and relies on `update_types()`/`derive_type()` for expansion. The semantic result must be equivalent — this is testable by running both tiers on the same formula set and comparing countermodel validity.

## Impact on BimodalLogic Task 226

If this approach is adopted:

- **Task 226 phases 1-3** (formula parser, encoding, oracle API, countermodel extraction, provider): absorbed into ModelChecker task 103. The code moves; the work is not lost.
- **Task 226 phases 4-5** (cross-validation against bmlogic-bench, enriched JSONL export): become acceptance criteria for ModelChecker task 103/105 instead.
- **Task 226 deferred work** (Lean metalogic soundness formalization): remains a BimodalLogic task, independent of where the Python code lives. The `FiniteTaskFrame` in `TaskFrame.lean:284-300` provides the Lean-side anchor for future formalization.
- **BimodalLogic's `z3_oracle/` directory**: can be archived or removed once the port to ModelChecker is verified.

BimodalLogic returns to providing only the positive signal (proofs via tableau). ModelChecker owns all negative signal infrastructure (countermodels via Z3, both fast and thorough).

## Impact on BimodalHarness

No changes required. BimodalHarness's OracleProvider protocol, OracleRegistry, SoundnessGateway, and CompatibilityMatrix are provider-agnostic. The tiered oracle registers as a single entry point (`bimodal_harness.oracle_providers`). BimodalHarness doesn't know or care whether the countermodel came from the fast tier or the thorough tier — it receives a StructuredCountermodel either way.

The `tier_used` metadata field in the countermodel output is informational. BimodalHarness can log it for diagnostics but doesn't need to act on it.

## Open Questions for Further Research

1. **Timeout budget split**: The 80/20 split (80% to Tier 1, 20% to Tier 2) is a starting heuristic. Should this be configurable? Should it adapt based on formula complexity (e.g., high temporal depth → more budget to Tier 2)?

2. **Tier 2 frame size selection**: Tier 1 uses progressive deepening from (2,3) to (4,4). What N and M should Tier 2 use? The existing solver defaults to N=2 with dynamic M. Should Tier 2 try larger N if Tier 1 already exhausted N=4?

3. **Countermodel equivalence verification**: When both tiers find countermodels for the same formula, do the countermodels satisfy the same frame axioms? The QF encoding and the quantified encoding express the same axioms differently — a regression test comparing countermodel validity across tiers would catch encoding divergences.

4. **Performance on ModelChecker's 43-example suite**: How fast does Tier 1 resolve the existing test cases? If Tier 1 handles all 43 examples in under 1 second total, Tier 2 is purely a fallback for harder formulas encountered during training.

5. **Shared formula parser**: Task 226's `formula.py` (400 lines) and task 102's `json_to_prefix()` both parse the same JSON format. Should there be one parser producing an intermediate AST that both tiers consume? Or is the current design (each tier owns its parser) simpler and less coupled?

6. **Entry point naming**: The ADR specifies `z3_base` as the entry point key. With tiered search, `z3_tiered` is more descriptive. Does BimodalHarness care about the entry point key name, or only the provider_id?

## Revised Task 103 Description

See the companion task description update in TODO.md. The key changes from the original task 103:

- **Tier 1 addition**: Port BimodalLogic `z3_oracle/` as `fast/` subpackage
- **Tiered dispatch**: `find_countermodel()` tries Tier 1 first, falls back to Tier 2
- **Package layout**: adds `fast/` alongside existing `theory_lib/bimodal/`
- **provider_id**: changed from `bmlogic_z3_base_v1` to `bmlogic_z3_tiered_v1`
- **Acceptance criteria**: added Tier 1 latency benchmark (<50ms median), cross-tier validation, and Tier 2 fallback verification
