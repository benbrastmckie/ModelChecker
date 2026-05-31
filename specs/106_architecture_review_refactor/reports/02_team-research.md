# Research Report: Task #106

**Task**: Architecture review of bimodal refactor plan (tasks 99-105)
**Date**: 2026-05-30
**Mode**: Team Research (4 teammates)
**Session**: sess_1780190833_53f47b

## Summary

This second research round focused specifically on how to refactor ModelChecker to maintain perfect alignment with BimodalLogic as single source of truth while allowing Z3 implementation divergence, contingent on provable soundness. The team identified substantial existing alignment between the Z3 encoding and BimodalLogic's formal semantics, but uncovered critical soundness gaps at the boundary of the finite time domain that must be addressed before any soundness claim holds. The consensus architecture keeps BimodalLogic as the legislative branch (definitions), ModelChecker as the executive branch (pure Python Z3 oracle), and BimodalHarness as the judicial branch (integration + Lean soundness bridge).

## Key Findings

### 1. The Z3 Encoding Is Substantially Aligned — With Critical Caveats

Teammate A mapped every BimodalLogic concept to its Z3 counterpart and found exact matches for all three frame axioms (nullity_identity, forward_comp, converse) and structural alignment for truth_at across atom, bot, imp, and box constructors. The atom domain guard, Until/Since operators, and lawful evolution constraints all have clear BimodalLogic counterparts.

However, Teammate C identified critical divergences that A treated as benign but which threaten soundness:

**CRITICAL — Boundary Effects**: Z3 uses bounded time `(-M, M)` with M typically 2-3. At the domain boundary (e.g., time = M-1), `G(phi)` is vacuously true because no future times exist. In BimodalLogic's infinite domains (with `NoMaxOrder`/`NoMinOrder` seriality requirements), this never happens. A Z3 countermodel exploiting boundary vacuity has no BimodalLogic analog — this is a concrete unsoundness risk.

**HIGH — Incomplete Shift Closure**: Z3's `capped_skolem_abundance_constraint` only provides shifts within `(-M, M)`. BimodalLogic's `ShiftClosed` requires closure under ALL shifts. The `time_shift_preserves_truth` theorem (needed for box soundness) requires true shift closure.

**HIGH — Guarded Compositionality**: Z3's `build_forward_comp_constraint` and `build_converse_constraint` add `is_valid_duration` guards absent from the Lean definitions, preventing derivation of task relations for durations near the boundary.

### 2. The Soundness Bridge Architecture

All four teammates converge on the same three-repo architecture:

```
BimodalLogic (Lean 4)  ─── SPECIFICATION ───  source of truth
       │
       │  require BimodalLogic (Lake dependency)
       ▼
BimodalHarness (Python + Lean)  ─── JUDICIAL ───  soundness bridge
       ▲
       │  implements OracleProvider (JSON contract)
       │
ModelChecker (Python only)  ─── EXECUTIVE ───  Z3 oracle
```

**Key principle**: ModelChecker and BimodalLogic have ZERO code-level dependency on each other. Coupling is through JSON schema contracts only. BimodalHarness owns the soundness bridge.

**Rejected alternatives**:
- Lean files in ModelChecker (adds Lean build complexity to a Python package; Teammate B)
- Separate verification repo (unnecessary fourth repo; Teammate B)
- Code generation from Lean to Python (no mature facility; Teammate D)
- Lean FFI to Z3 (research project, not practical; Teammate D)

### 3. Recommended Soundness Proof Strategy: Direct Embedding Theorem

Teammate B evaluated three strategies and recommends **Direct Embedding** (Strategy A):

1. Define a Lean function `fromStructuredCountermodel : Json -> Option (FiniteTaskFrame Int x TaskModel x WorldHistory x Int)` in BimodalHarness
2. Prove: if parsing succeeds, the formula is false at the evaluation point under BimodalLogic semantics
3. The trusted code is ~200 lines of JSON parser — everything else is formally verified

**Why this wins**: Directly uses existing BimodalLogic types, can be built incrementally (start with frame axiom checking, add truth evaluation), and aligns with the existing `dataset_validator` subprocess pattern.

**Rejected**: Bisimulation (over-engineered, no BimodalLogic infrastructure for it), Verified Extractor (ideal long-term but requires formalizing Z3 encoding in Lean — 12+ months).

### 4. The Boundary Problem Requires a New Task

Teammate C's critical finding demands resolution before any soundness claim:

**The problem**: Z3 models with evaluation at time t=0 and M=3 have only 5 time points (-2,-1,0,1,2). At t=2, `G(phi)` is vacuously true. If a countermodel uses this, it has no BimodalLogic counterpart.

**Proposed resolution** (synthesized from all teammates):
1. **Temporal depth analysis**: For formula `phi` with temporal depth `d`, require `M > d` so the evaluation point (t=0) is always far enough from boundaries that no temporal operator can "see" the edge
2. **Boundary buffer constraint**: Add Z3 constraints that prevent the evaluation point from being within `d` steps of the boundary
3. **Formal argument**: Prove that for `M > temporal_depth(phi)`, boundary effects cannot create spurious countermodels — i.e., the restriction to `(-M, M)` doesn't affect truth at t=0 for formulas of depth ≤ d

This is the **key open question** the refactoring must address and should be a dedicated task.

### 5. Countermodel Serialization Gap

Teammate B identified that the current `StructuredCountermodel` in BimodalHarness uses binary `(from, to)` pairs for the task relation, but both the Z3 encoding and BimodalLogic use ternary `(source, duration, target)`. The duration is essential for the soundness bridge. The serialization format must be extended to ternary triples.

### 6. Strategic Vision: Empirical Soundness First, Formal Proofs Later

All teammates converge on an incremental approach:

**Tier 1 — Available now**:
- Cross-oracle differential testing (Z3 vs BimodalLogic's `findCountermodel`)
- Frame axiom checking on extracted countermodels (Python assertions)
- Property-based testing with BimodalLogic's `FormulaEnumerator` (formulas up to complexity 7)
- The SoundnessGateway already exists in BimodalHarness

**Tier 2 — 3-6 months**:
- Lean function in BimodalHarness that parses StructuredCountermodel JSON and constructs BimodalLogic types
- `validateCountermodel` correctness theorem
- CI cross-validation on every change to any repo
- Boundary buffer implementation and temporal depth analysis

**Tier 3 — 12+ months (research goal)**:
- Full Oracle Soundness theorem in Lean
- Specification compiler (BimodalLogic truth_at -> Z3 constraints mechanically)

### 7. Missing Tasks for Tasks 99-105

Teammate C identified 5 missing tasks not covered by the current 99-105 plan:

1. **Soundness bridge proof** (CRITICAL): No task for formally or even semi-formally establishing the soundness claim
2. **Boundary effect mitigation**: No task for analyzing and mitigating the finite domain boundary problem
3. **Lean infrastructure for handshake**: No task for setting up BimodalHarness to import BimodalLogic and build verification modules
4. **Frame class validation**: No task to validate that "Base" frame class in Z3 actually matches BimodalLogic's base frame class
5. **Soundness regression tests**: No task for a test suite specifically probing boundary effects and shift closure edge cases

## Synthesis

### Conflicts Resolved

1. **Where should Lean code live?** Teammate A proposed a `lean/` directory in ModelChecker; Teammates B and D recommended BimodalHarness. **Resolution**: BimodalHarness is correct — it is already the integration layer, has `lean-interact` as a dependency, and keeping ModelChecker as pure Python avoids Lean build complexity (Mathlib alone takes ~30 min).

2. **Is the Z3 encoding sound?** Teammate A argues divergences are sound; Teammate C identifies concrete unsoundness risks from boundary effects. **Resolution**: A is correct that the *structure* is aligned, but C is correct that boundary effects create a real gap. The soundness claim requires an explicit boundary buffer mechanism or temporal depth argument — it cannot be assumed.

3. **Is G/H equivalence trivial?** Teammate A says cite `future_iff`/`past_iff`; Teammate C says the deeper issue is whether Z3's temporal quantifiers match BimodalLogic's under finite domains. **Resolution**: C is right — the simp lemmas confirm equivalence over infinite domains, but Z3's `ForAllTime` guard with `is_valid_time` creates a different quantification range at boundaries. G/H equivalence holds only if the boundary buffer is sufficient.

4. **How urgent are formal proofs?** All agree empirical testing comes first. The disagreement is on whether boundary effects are blocking (C) or manageable (A, D). **Resolution**: Boundary effects are blocking for the soundness *claim* but not for practical oracle use. They should be addressed as a task before the soundness bridge is formalized, but the Z3 oracle can continue operating with the understanding that countermodels at boundary positions require extra validation.

### Gaps Identified

1. **Semantics version ownership**: No mechanism for BimodalLogic to export a version tag that the Python oracle can read at build time (Teammates C, D)
2. **"Base" frame class undefined**: Z3 oracle supports only "Base" but BimodalLogic has a frame hierarchy (LinearTemporalFrame < SerialFrame < Dense/Discrete). What does "Base" map to? (Teammate C)
3. **Disabled task_restriction constraint**: Z3's constraint 10 (`task_restriction`) is commented out, allowing task_rel entries not realized in any world history (Teammate C)
4. **Until/Since line-by-line verification**: Not yet done — Z3's `UntilOperator`/`SinceOperator` implementations need comparison against `Truth.lean:122-131` (Teammate A)
5. **FMP structural compatibility**: Are BimodalLogic's FiniteTaskFrame countermodels structurally compatible with Z3's BitVec-encoded world states? (Teammate C)

### Recommendations

**Immediate** (before or alongside tasks 99-105):
1. Add a new task: "Boundary effect analysis and mitigation for Z3 bimodal oracle"
2. Add a new task: "Cross-oracle differential testing infrastructure" (leveraging BimodalLogic's FormulaEnumerator)
3. Extend StructuredCountermodel serialization to ternary task relation triples
4. Line-by-line Until/Since verification against Truth.lean

**During refactoring** (tasks 100-105):
5. Ensure the oracle reports temporal_depth alongside countermodels
6. Add boundary buffer constraints to Z3 encoding (M > temporal_depth + margin)
7. Implement frame axiom checking as a post-extraction validation in Python
8. Pin `semantics_version` to a BimodalLogic git tag

**After refactoring**:
9. Build the Lean soundness bridge in BimodalHarness (fromStructuredCountermodel parser + frame axiom checker)
10. Set up cross-repo CI triggering
11. Comprehensive property-based testing with formula enumeration up to complexity 7

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary approach | completed | high | Alignment mapping table, Lean infrastructure skeleton |
| B | Alternative approaches | completed | high | Direct Embedding strategy, serialization gap, testing roadmap |
| C | Critic | completed | high | Boundary effects (critical), 5 missing tasks, 6 unanswered questions |
| D | Horizons | completed | high | Three-repo vision, CI/CD strategy, specification compiler idea |

## References

- `BimodalLogic/Theories/Bimodal/Semantics/TaskFrame.lean:93-122` — TaskFrame structure
- `BimodalLogic/Theories/Bimodal/Semantics/Truth.lean:122-131` — truth_at definition
- `BimodalLogic/Theories/Bimodal/Semantics/Truth.lean:295` — ShiftClosed definition
- `BimodalLogic/Theories/Bimodal/Semantics/Validity.lean:73` — validity definition
- `BimodalLogic/Theories/Bimodal/Metalogic/Soundness.lean` — Soundness theorem (sorry-free)
- `BimodalHarness/src/bimodal_harness/oracle/protocol.py:72-206` — OracleProvider protocol
- `BimodalHarness/src/bimodal_harness/oracle/gateway.py:219-508` — SoundnessGateway
- `BimodalHarness/src/bimodal_harness/schema/records.py:269-348` — StructuredCountermodel
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:179-185` — Z3 task_rel
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:274-388` — Frame axiom constraints
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:1275` — capped_skolem_abundance
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:1438` — true_at
