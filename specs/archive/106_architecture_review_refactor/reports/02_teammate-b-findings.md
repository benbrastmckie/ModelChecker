# Teammate B Findings: Alternative Soundness Architectures

**Task**: 106 - Architecture review of bimodal refactor plan
**Angle**: Alternative patterns, soundness proof strategies, and Lean handshake architectures
**Date**: 2026-05-30

## Summary

The three-repo ecosystem (BimodalLogic, BimodalHarness, ModelChecker) already has significant infrastructure for oracle validation, but the soundness bridge between Z3 countermodels and Lean-verified semantics has a critical gap: the current validation only checks *atoms* (SimpleCountermodel), not the full frame structure that the Z3 oracle actually constructs. This report evaluates alternative architectures for closing that gap formally while keeping BimodalLogic as single source of truth.

## Key Findings

### 1. Current Soundness Architecture Already Has the Right Shape

The existing infrastructure is remarkably well-positioned:

- **BimodalLogic** has a complete `Soundness.lean` proving `(Γ ⊢ φ) → (Γ ⊨ φ)` (sorry-free for all frame classes)
- **BimodalLogic** has `DatasetValidator.lean` and `BenchmarkOracle.lean` executables for subprocess validation
- **BimodalHarness** has `SoundnessGateway` with three-phase validation (self-check → cross-validation → matrix recording)
- **BimodalHarness** has `LeanSubprocessValidator` calling `lake exe dataset_validator --mode validate-countermodel`

The gap: **the dataset_validator can only validate `SimpleCountermodel` (atom-level)**, not `StructuredCountermodel` (full frame). The Z3 oracle returns structured data with `world_histories`, `task_relation`, `truth_valuation`, `evaluation_world`, `evaluation_time` — but Lean only checks whether the listed atoms form a consistent assignment.

**Confidence**: High

### 2. Three Soundness Proof Strategies Evaluated

#### Strategy A: Direct Embedding Theorem (Recommended)

**Statement**: For any Z3 model M_z3 that satisfies the ModelChecker's frame constraints, there exists a BimodalLogic `TaskFrame Int` + `TaskModel` + `WorldHistory` that falsifies the same formula.

**Approach**:
1. Define a Lean function `fromStructuredCountermodel : Json → Option (FiniteTaskFrame Int × TaskModel × WorldHistory × Int)` that reads the StructuredCountermodel JSON and builds actual Lean structures
2. Prove a theorem: `fromStructuredCountermodel_sound : ∀ j cm, fromStructuredCountermodel j = some cm → ¬ truth_at cm.model cm.history cm.time φ`
3. The proof relies on:
   - Z3's `TaskRel` constraints map to `TaskFrame.nullity_identity`, `forward_comp`, `converse`
   - Z3's `world_function` maps to `WorldHistory.states`
   - Z3's `truth_condition` maps to `TaskModel.valuation`

**Pros**:
- Directly uses existing BimodalLogic types (no new mathematical machinery)
- The function `fromStructuredCountermodel` is the only trusted code — it's a parser, easy to audit
- Can be incrementally verified: start with just frame axiom checking, then add truth evaluation
- Aligns with existing `dataset_validator` pattern (subprocess call)

**Cons**:
- Requires implementing JSON parsing in Lean for the structured format (significant boilerplate)
- The proof must handle finite domain restrictions (Z3 uses bounded ints, Lean uses arbitrary `D`)

**Confidence**: High — this is the most pragmatic path

#### Strategy B: Bisimulation Approach

**Statement**: The finite Z3 model bisimulates a fragment of the BimodalLogic semantics over `Int`.

**Approach**:
1. Define a bisimulation relation between Z3 BitVec worlds and BimodalLogic WorldStates
2. Prove that bisimulating models agree on formula truth
3. Show that any Z3 model satisfying frame constraints is bisimilar to a BimodalLogic model

**Pros**:
- Mathematically elegant
- Handles the finite/infinite gap cleanly (bisimulation respects truth of modal-temporal formulas)

**Cons**:
- Bisimulation for tense logic with Until/Since is technically more complex than for basic modal logic
- Requires defining the bisimulation relation carefully for the task-frame structure (not standard Kripke)
- Significant proof overhead for marginal benefit over Strategy A
- No existing BimodalLogic infrastructure for bisimulations

**Confidence**: Medium — correct but over-engineered for the current need

#### Strategy C: Reflection/Extraction with Verified Extractor

**Statement**: Write a verified Lean program that reads Z3 output, builds a Lean model, and produces a machine-checked proof that the formula is false in that model.

**Approach**:
1. Write a `decide_with_oracle` function in Lean that:
   a. Calls the Z3 oracle (via subprocess or FFI)
   b. Parses the StructuredCountermodel
   c. Constructs a `FiniteTaskFrame Int` + `TaskModel`
   d. Uses decidability to check `¬ truth_at M τ t φ` computationally
   e. Returns `Decidable (valid φ)` with a proof certificate
2. The `decide` tactic on the finite model serves as the verification

**Pros**:
- Minimizes trusted computing base (only Lean's kernel is trusted)
- Produces actual proof terms
- Can leverage BimodalLogic's existing `Decidability` module

**Cons**:
- Decidability module currently uses tableau (internal), not oracle (external)
- Computational verification of truth on a finite model requires implementing `truth_at` as a decision procedure on concrete data — the current `truth_at` uses quantifiers over arbitrary `D`
- Performance concern: verifying a Z3 model in Lean's kernel may be slow for large models

**Confidence**: Medium — ideal long-term but heavy initial investment

### 3. Alternative Architectures for the Lean Handshake

#### Architecture 1: All Soundness in BimodalHarness (Recommended)

```
BimodalLogic/          (pure math, no oracle knowledge)
  ├── Theories/Bimodal/
  │   ├── Semantics/   (TaskFrame, truth_at, validity)
  │   ├── Metalogic/   (Soundness, Decidability)
  │   └── Automation/  (DataExport, DatasetValidator — current tools)
  └── lakefile.lean

BimodalHarness/        (integration layer — owns the soundness bridge)
  ├── lean/            (NEW: Lean sources for verification)
  │   ├── OracleSoundness/
  │   │   ├── StructuredCountermodelParser.lean
  │   │   ├── FrameAxiomChecker.lean
  │   │   └── TruthEvaluator.lean
  │   └── lakefile.lean  (requires BimodalLogic as dependency)
  ├── src/bimodal_harness/
  │   ├── oracle/      (protocol, gateway, registry)
  │   └── lean/        (bridge.py — subprocess calls)
  └── pyproject.toml

ModelChecker/          (Z3 oracle implementation — pure Python)
  ├── code/src/model_checker/
  │   └── theory_lib/bimodal/  (Z3 encoding)
  └── (NO Lean files)
```

**Why this is best**:
- BimodalLogic stays pure mathematics (no oracle concerns pollute the formalization)
- BimodalHarness is *already* the integration layer — it owns `SoundnessGateway`, `LeanSubprocessValidator`, the oracle protocol
- ModelChecker stays a pure Python package — no Lean dependency, no build complexity
- The `lakefile.lean` in BimodalHarness imports BimodalLogic as a Lake dependency, which is the natural Lean package composition pattern

**Confidence**: High

#### Architecture 2: Lean Files in ModelChecker

ModelChecker would contain Lean files that import BimodalLogic.

**Why rejected**:
- ModelChecker is a Python package with no Lean infrastructure (`lakefile.lean`, Mathlib dependency, etc.)
- Adding Lean to ModelChecker would massively increase its build complexity (Mathlib alone takes ~30 min to build)
- The oracle provider is a Python Protocol implementation — mixing Lean into it creates a confusing dual-language package
- ModelChecker should be a pure Python implementation of `OracleProvider`

#### Architecture 3: Separate Verification Repo

A standalone `BimodalVerification/` repo.

**Why suboptimal**:
- Creates a fourth repo to coordinate, increasing maintenance burden
- BimodalHarness already has the right shape (integration layer between BimodalLogic and oracle providers)
- No clear benefit over putting verification in BimodalHarness

#### Architecture 4: Hybrid (Statements in Harness, Proofs Incremental)

Same as Architecture 1, but with `sorry`-based scaffolding.

**How it works**: Define the `OracleSoundness` typeclass (or structure) in BimodalHarness with sorry'd proofs initially. Fill in proofs incrementally as the system matures.

**This is actually the recommended approach within Architecture 1** — start with computational checking (decidability on finite models) and add formal proofs over time.

### 4. Countermodel Serialization for the Soundness Bridge

The current format gap:

| Level | BimodalLogic | ModelChecker Z3 | BimodalHarness |
|-------|-------------|-----------------|----------------|
| Minimal | `SimpleCountermodel` (atoms only) | Not produced | Validated via `dataset_validator` |
| Structured | None in Lean | `StructuredCountermodel` (full frame) | Schema in `records.py`, encoding in `countermodel.py` |

**Recommended serialization path**:

1. **ModelChecker → JSON**: Already done. The Z3 oracle extracts `world_histories`, `task_relation`, `truth_valuation`, `evaluation_world`, `evaluation_time` from Z3 models.

2. **JSON → Lean**: Needs a `fromJson` parser in Lean (in BimodalHarness's Lean component) that constructs:
   ```lean
   structure OracleCountermodel where
     frame : FiniteTaskFrame Int
     model : TaskModel frame.toTaskFrame
     history : WorldHistory frame.toTaskFrame
     time : Int
     formula : Formula
   ```

3. **JSON format** (extending current `SimpleCountermodel.toJson`):
   ```json
   {
     "trueAtoms": [{"base": "p"}, ...],
     "falseAtoms": [{"base": "q"}, ...],
     "formula": {"tag": "imp", "left": ..., "right": ...},
     "world_count": 2,
     "time_bound": 3,
     "world_states": [[0, 1, 0, 1], [1, 0, 1, 0]],
     "world_histories": [
       {"world_id": 0, "states": {"0": 0, "1": 1, "2": 0}},
       {"world_id": 1, "states": {"0": 1, "1": 0, "2": 1}}
     ],
     "task_relation": [
       {"source": 0, "duration": 1, "target": 1},
       {"source": 1, "duration": -1, "target": 0}
     ],
     "truth_valuation": {"p": [[0, 0], [1, 2]], "q": [[1, 1]]},
     "evaluation_world": 0,
     "evaluation_time": 0
   }
   ```

4. **Key insight**: The `task_relation` field should use `(source_state, duration, target_state)` triples (matching the ternary `task_rel` in both Lean and Z3), not just `(from, to)` pairs. The current `StructuredCountermodel` in BimodalHarness uses `(from, to)` which loses the duration information critical for the soundness proof.

**Confidence**: High

### 5. Intermediate Testing Before Formal Verification

Before investing in full Lean proofs, these testing strategies give high confidence:

#### A. Cross-Oracle Differential Testing (Highest ROI)

BimodalLogic already has a Lean decision procedure (`findCountermodel` in `CountermodelExtraction.lean`) that produces `SimpleCountermodel`s independently. Run both:
1. Z3 oracle: `formula → StructuredCountermodel | None`
2. Lean tableau: `formula → SimpleCountermodel | None` (via `lake exe benchmark_oracle`)

Verify agreement on every formula in a large corpus. **Disagreements surface bugs in either oracle.**

The BimodalHarness cross-validation already does this (gateway.py:439-496) but only for a limited benchmark set.

#### B. Property-Based Testing via the Formal Spec

Generate random formulas, run the Z3 oracle, then:
1. Parse the StructuredCountermodel into a Python representation of the BimodalLogic semantics
2. Evaluate `truth_at` in Python using the *exact* recursive definition from `Truth.lean`
3. Verify the formula is indeed false at the evaluation point

This is a "reference implementation" approach — the Python evaluator is a direct port of the Lean `truth_at`, and disagreements indicate encoding bugs.

**File reference**: The `truth_at` definition in `Truth.lean:122-131` has exactly 6 cases (atom, bot, imp, box, untl, snce). A Python port is ~50 lines.

#### C. Frame Axiom Checking (Quick Win)

For every Z3 countermodel, verify the three frame axioms hold:
1. **Nullity identity**: `task_rel(w, 0, u) ↔ w == u` for all states
2. **Converse**: `task_rel(w, d, u) ↔ task_rel(u, -d, w)` for all states and durations
3. **Forward compositionality**: `task_rel(w, d1, v) ∧ task_rel(v, d2, u) → task_rel(w, d1+d2, u)` for non-negative durations

These are finite checks on the concrete model — no Lean needed, just Python assertions.

**File reference**: The Z3 constraints for these are at `semantic.py:274-388`. The check would verify the *extracted* model (after Z3 solving) satisfies them, catching any extraction bugs.

#### D. Shift-Closure Checking

Verify that the set of world histories in the Z3 model is shift-closed (for every history τ and shift Δ, τ shifted by Δ is also in the model). This matches `ShiftClosed` at `Truth.lean:295`.

**Confidence**: High — these are all implementable in days, not weeks

## Synthesis: Recommended Architecture

```
                    BimodalLogic (Lean 4)
                    ├── Semantics: TaskFrame, truth_at, validity
                    ├── Metalogic: Soundness (⊢ → ⊨), Decidability
                    └── Automation: DataExport, DatasetValidator
                            │
                            │ `require BimodalLogic` (Lake dependency)
                            ▼
                    BimodalHarness (Python + Lean 4)
                    ├── lean/OracleSoundness/
                    │   ├── Parser.lean (fromJson → FiniteTaskFrame)
                    │   ├── Checker.lean (verify frame axioms + truth)
                    │   └── lakefile.lean (imports BimodalLogic)
                    ├── oracle/protocol.py (OracleProvider interface)
                    ├── oracle/gateway.py (SoundnessGateway)
                    └── lean/bridge.py (subprocess: lake exe)
                            ▲
                            │ implements OracleProvider
                            │
                    ModelChecker (Python only)
                    ├── theory_lib/bimodal/ (Z3 encoding)
                    └── OracleProvider implementation
                        (produces StructuredCountermodel JSON)
```

**The soundness claim**: "Every StructuredCountermodel produced by ModelChecker's Z3 oracle, when parsed by BimodalHarness's Lean checker, yields a valid BimodalLogic countermodel that falsifies the formula."

**The minimal trusted base**: The JSON parser + frame axiom checker in Lean (~200 lines). Everything else is either formally verified (BimodalLogic soundness) or executable checked (Python oracle protocol).

## Teammate Contributions

| Aspect | Finding | Confidence |
|--------|---------|------------|
| Best proof strategy | Direct embedding (Strategy A) | High |
| Best repo architecture | All soundness in BimodalHarness (Architecture 1) | High |
| Serialization format | Ternary task_rel JSON, extend StructuredCountermodel | High |
| Immediate testing | Cross-oracle differential + frame axiom checking | High |
| Bisimulation approach | Correct but over-engineered | Medium |
| Verified extractor | Ideal long-term, heavy initial investment | Medium |

## References

- `BimodalLogic/Theories/Bimodal/Semantics/Truth.lean:122-131` — `truth_at` definition (6 constructors)
- `BimodalLogic/Theories/Bimodal/Semantics/TaskFrame.lean:93-122` — `TaskFrame` structure with 3 axioms
- `BimodalLogic/Theories/Bimodal/Metalogic/Soundness.lean:60-61` — Soundness theorem
- `BimodalLogic/Theories/Bimodal/Automation/DataExport.lean:104-116` — `Formula.toJson` schema
- `BimodalHarness/src/bimodal_harness/oracle/protocol.py:72-206` — `OracleProvider` protocol
- `BimodalHarness/src/bimodal_harness/oracle/gateway.py:219-508` — `SoundnessGateway`
- `BimodalHarness/src/bimodal_harness/schema/records.py:269-348` — `StructuredCountermodel`
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:179-185` — Z3 `task_rel` definition
- `ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py:274-388` — Frame axiom constraints
