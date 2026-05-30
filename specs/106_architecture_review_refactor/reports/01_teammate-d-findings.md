# Teammate D — Horizons: Strategic Alignment Review

**Task**: 106 — Architecture review of bimodal refactor plan (tasks 99-105)
**Date**: 2026-05-30
**Angle**: Long-term alignment, ecosystem fit, strategic direction
**Confidence**: High

---

## Key Findings

### 1. Ecosystem Naming: Package Should Be `bmlogic-oracle`

The BimodalHarness `pyproject.toml` already declares the expected package name in its optional dependencies:

```toml
[project.optional-dependencies]
oracle = [
  "bmlogic-oracle>=0.1.0",
]
```

The mock oracle uses `provider_id = "bmlogic_z3_base_v1"`. The entry point group is `bimodal_harness.oracle_providers`. The package name **must** be `bmlogic-oracle` to align with the Harness expectation. Tasks 101 and 103 should use this name explicitly.

### 2. Formula Constructor Alignment: Critical Mismatch Between G/H Primitives

**BimodalLogic (Lean)** has exactly 6 primitive constructors: `atom`, `bot`, `imp`, `box`, `untl`, `snce`. The operators G (all_future) and H (all_past) are **derived**:

```lean
def all_future (φ) := (some_future φ.neg).neg  -- G(φ) = ¬U(¬φ, ⊤)
def all_past (φ) := (some_past φ.neg).neg      -- H(φ) = ¬S(¬φ, ⊤)
```

**ModelChecker (Python)** has `FutureOperator` (G) and `PastOperator` (H) as **primitive operators** with their own `true_at`/`false_at` methods. These are independent implementations, not derived from Until/Since.

The 6-tag JSON formula format only contains `untl` and `snce` — there are **no G or H tags**. The formula translation (Task 102) must:
1. Accept only 6 tags from JSON
2. Derive G and H via negation when constructing internal sentences: `G(φ) = ¬F(¬φ)` where `F(φ) = U(φ, ⊤)`, and similarly for H
3. Verify semantic equivalence: confirm that `FutureOperator.true_at(φ)` produces identical Z3 constraints to `¬UntilOperator.true_at(¬φ, ⊤)`

If the semantics don't align, this is a soundness bug in the oracle. Task 102 should explicitly verify this.

### 3. Dual-Signal Cross-Validation Architecture

The BimodalHarness has a mature cross-signal consistency checking infrastructure (`CrossSignalConsistencyChecker`). When the oracle finds a countermodel and the verifier finds a proof for the *same* formula, that's an inconsistency. This means:

- **Correctness is paramount**: A single false countermodel (invalid formula judged valid) or missed countermodel (valid formula given a spurious countermodel) would be detected by cross-signal checks and flagged as an oracle failure.
- **The soundness gateway** runs a 3-phase check: self-check (validate_self), cross-validation, compatibility matrix recording.
- **Implication for testing (Task 105)**: Integration tests should include cross-signal scenarios. The harness's `SPOT_CHECK_FORMULAS` (10 known-invalid formulas in `_mock.py`) provide the ground-truth for validation.

### 4. Frame Class: Only "Base" Is Implementable Now

The OracleProvider protocol supports `{"Base", "Dense", "Discrete"}` frame classes, but the mock oracle and harness documentation both note "Only `Base` is implementable today." The ModelChecker has no frame class concept at all — it implicitly implements what would be "Base".

**Recommendation**: Start with `supported_frame_classes = frozenset({"Base"})` and document Dense/Discrete as future extensions. Don't over-engineer extensibility for frame classes that don't exist yet.

### 5. StructuredCountermodel Provides Richer Training Signal

The OracleProvider protocol supports both `SimpleCountermodel` (minimal: trueAtoms/falseAtoms/formula) and `StructuredCountermodel` (rich: world_histories, task_relation, truth_valuation, evaluation_world/time, world_count, time_bound).

The ModelChecker's `BimodalStructure` already has `extract_model_elements()` that produces world histories, task relations, and truth conditions — this maps directly to the structured format. The expert iteration training loop in `bimodal_harness/training/loop.py` currently only uses formulas for search and training, but the structured countermodel data could eventually feed into value network features or richer corrective signals.

**Recommendation**: Implement StructuredCountermodel from the start. The mapping is natural and the BimodalStructure already has the extraction logic. Deferring it would mean reworking the serialization layer later.

### 6. Version Pinning: semantics_version Tracks BimodalLogic

The `semantics_version` property on OracleProvider tracks which version of BimodalLogic's semantics (frame axioms, truth_at definition) the oracle was validated against. The mock uses `"2.1.0"`. A major bump indicates breaking changes to TaskFrame axioms.

**This means**: Every time BimodalLogic changes its semantics (adds frame conditions, modifies truth_at), the oracle must re-validate. The `bmlogic-oracle` package should pin to a specific BimodalLogic semantics version in its metadata and the harness checks this at preflight.

### 7. Extensibility vs. Bimodal-Only: Go Fully Bimodal-Only

The technical memo is clear: the full Logos system "will not be made public." The bimodal fragment is the open-source component. The multi-theory architecture in the current ModelChecker (logos, exclusion, imposition) was for the private Logos development.

**Recommendation**: Go fully bimodal-only. No theory registry, no pluggable theories, no extensibility for future theories. The `bmlogic-oracle` package is purpose-built for one job: producing Z3 countermodels for bimodal formulas. Simplicity increases correctness confidence, which is critical for the training pipeline.

### 8. CLI Preservation: Keep a Thin CLI

The existing CLI (`model-checker examples.py`) is useful for standalone countermodel checking during development. While the primary consumption path is programmatic (via OracleProvider), preserving a thin CLI for ad-hoc formula checking would be valuable:

```bash
bmlogic-oracle check '{"tag": "imp", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "box", "child": {"tag": "atom", "name": "p"}}}'
```

This aids debugging and development without requiring the full harness setup.

### 9. Training Pipeline Integration: The Oracle's Role Is Narrow

The expert iteration loop (`ExpertIterationLoop.run()`) has 5 phases: SEARCH → EXTRACT → ACCUMULATE → RETRAIN → EVALUATE. The oracle is used during SEARCH (to generate training signals) and indirectly during EVALUATE. The oracle call path is:

```
ExpertIterationLoop 
  → search phase (BFS or MCTS)
  → proof search uses axiom matching and action selection
  → oracle consulted for countermodel generation
```

The oracle's interface is narrow: `find_countermodel(formula_json, frame_class, timeout_ms) -> dict | None`. Everything else (model training, replay buffer, difficulty tracking) is the harness's responsibility. This confirms the refactored package should be lean — just the Z3 encoding, constraint solving, and model extraction.

### 10. Task 99 (Audit) Should Be Merged with Task 100 (Strip)

The audit (Task 99) produces a report listing what to keep/modify/remove. Task 100 then executes that report. Given that we already have the research from the three initial agents identifying exactly which modules to keep/remove, a separate audit task is redundant. The audit findings are already captured and should be folded into the research for Task 106 itself. Task 100 can directly use these findings.

---

## Recommended Approach

### Task Revisions

1. **Merge Task 99 into Task 106's output** — the audit is effectively done. Task 99 should be eliminated or absorbed.

2. **Task 100 (Strip)**: Execute directly from the audit findings. Focus on preserving the bimodal test suite (43 examples).

3. **Task 101 (Package)**: Name the package `bmlogic-oracle`. Use `hatchling` as the build backend (matching BimodalHarness convention). Entry point: `[project.entry-points.'bimodal_harness.oracle_providers']`.

4. **Task 102 (Formula Translation)**: Add explicit verification that G/H derived from U/S produce semantically identical Z3 constraints to the direct G/H implementations. This is the highest-risk task — a soundness bug here propagates false training signals.

5. **Task 103 (OracleProvider)**: Implement StructuredCountermodel from the start, not as optional. Map `BimodalStructure.extract_model_elements()` directly to the structured JSON format.

6. **Task 104 (Cleanup)**: Keep a thin CLI for standalone countermodel checking. Strip everything else.

7. **Task 105 (Testing)**: Include cross-signal test scenarios using the harness's `SPOT_CHECK_FORMULAS` as ground truth. Verify countermodels against known-invalid formulas from BimodalLogic.

### Missing Task: Semantics Version Alignment

Add a task (or fold into Task 103) for establishing the `semantics_version` contract:
- Pin to a specific BimodalLogic semantics version
- Document what constitutes a breaking change
- Create a validation script that cross-checks the oracle against BimodalLogic's known theorems/counterexamples

---

## Evidence/Examples

- BimodalHarness `pyproject.toml` declares `bmlogic-oracle>=0.1.0` as optional dependency
- BimodalLogic Lean `Formula` type has exactly 6 constructors matching the JSON tags
- BimodalLogic derives G/H from U/S: `G(φ) = ¬U(¬φ, ⊤)`, `H(φ) = ¬S(¬φ, ⊤)`
- ModelChecker has G/H as independent primitive operators
- Cross-signal consistency checker in `bimodal_harness/signal/consistency.py` catches oracle/verifier conflicts
- Expert iteration training loop in `bimodal_harness/training/loop.py` consumes oracle via narrow `find_countermodel` interface
- Mock oracle `_mock.py` provides 10 spot-check formulas as ground truth

---

## Confidence Level

**High** — based on direct reading of BimodalHarness source, BimodalLogic Lean source, ModelChecker source, and the technical memo. The G/H mismatch and package naming findings are concrete and verifiable.
