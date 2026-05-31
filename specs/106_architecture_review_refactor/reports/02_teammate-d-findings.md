# Teammate D (Horizons): Strategic Architecture for Three-Repo Bimodal Ecosystem

**Task**: 106 — Architecture review of bimodal refactor plan
**Date**: 2026-05-30
**Angle**: Long-term architecture, Lean infrastructure, single-source-of-truth alignment

## Key Findings

### 1. Three-Repo Dependency Graph: The Ideal Architecture

The three repos have a clear ideal dependency direction:

```
BimodalLogic (Lean 4)          — SPECIFICATION (source of truth)
    ↓ defines semantics             ↓ exports: Formula.toJson, SimpleCountermodel.toJson,
    ↓ proves soundness              ↓          dataset_validator, EnrichedCountermodel
    ↓ exports JSON schemas          ↓
    ↓                               ↓
ModelChecker/bmlogic-oracle     — IMPLEMENTATION (Z3 oracle)
    ↓ implements OracleProvider     ↓ consumes: Formula.toJson schema
    ↓ returns countermodels         ↓ produces: SimpleCountermodel.toJson-conformant output
    ↓                               ↓
BimodalHarness (Python)         — INTEGRATION (training harness)
    ↑ imports both                  ↑ validates: oracle output against Lean via subprocess
    ↑ cross-checks signals          ↑ trains: ML models on oracle/verifier dual signal
```

**Who owns what:**
- **BimodalLogic**: Owns the formal semantics (TaskFrame, truth_at, Formula), the proof system, all metalogical results (soundness, completeness, decidability, FMP), and the JSON serialization schemas (Formula.toJson, SimpleCountermodel.toJson). This is the *legislative* branch.
- **ModelChecker/bmlogic-oracle**: Owns the Z3 encoding, the finite model search, the countermodel extraction from Z3 models, and the OracleProvider implementation. This is the *executive* branch — it implements the specification using a different mechanism (SMT solving vs. tableau).
- **BimodalHarness**: Owns the training pipeline, the OracleProvider/VerifierProvider protocols, the SoundnessGateway, the CrossSignalConsistencyChecker, and the compatibility matrix. This is the *judicial* branch — it checks that the executive's outputs are consistent with the legislative's rulings.

**Critical insight**: The dependency is not a DAG in the code-import sense. BimodalHarness depends on both (via pip for oracle, via subprocess for BimodalLogic). But BimodalLogic and ModelChecker should have ZERO code-level dependency on each other. Their only coupling is through the JSON schema contracts and the BimodalHarness validation pipeline.

### 2. What "Single Source of Truth" Means in Practice

This is the most important strategic question. After studying all three codebases, I see three possible interpretations, each with different implications:

**Option A: Schema Alignment (Recommended)**
- BimodalLogic defines the JSON schemas (Formula.toJson, SimpleCountermodel.toJson)
- ModelChecker implements a Z3 oracle that consumes/produces these schemas
- Alignment is verified empirically: BimodalHarness runs `lake exe dataset_validator` to check that every countermodel the Z3 oracle produces actually falsifies the formula under BimodalLogic's truth_at
- No code generation, no import dependency
- Sync mechanism: semantics_version field in OracleProvider, compatibility matrix

**Option B: Code Generation from Lean**
- Generate Python Z3 constraints directly from BimodalLogic's Lean definitions
- Tight coupling, guaranteed alignment, but fragile and complex
- Lean 4 has no mature Lean→Python codegen facility
- Would require a custom metaprogram that walks BimodalLogic's `truth_at` definition and emits Z3 constraints

**Option C: Lean FFI to Z3**
- Call Z3 directly from Lean 4 via FFI
- Eliminates ModelChecker entirely — BimodalLogic becomes both spec and implementation
- Technically possible (Z3 has a C API, Lean 4 supports C FFI) but enormous engineering effort
- Loses the separation of concerns that makes the architecture clean

**Recommendation: Option A with a formal soundness bridge.** The Z3 oracle is allowed to diverge in implementation (different encoding, different search strategy) as long as every countermodel it produces can be validated against BimodalLogic's semantics. This is already exactly what the SoundnessGateway does.

### 3. The Soundness Bridge: What Lean Infrastructure Is Needed

The key theorem to prove is:

> **Oracle Soundness**: If the Z3 oracle returns a countermodel `cm` for formula `φ`, then there exists a BimodalLogic `TaskFrame`/`TaskModel` and world history `τ` such that `¬ truth_at M τ t φ`.

This can be decomposed into:

#### 3a. Already Exists in BimodalLogic (high confidence)

- **`SimpleCountermodel` type** (`Metalogic/Decidability/CountermodelExtraction.lean:47`): Already defined with `trueAtoms`, `falseAtoms`, `formula` fields
- **`SimpleCountermodel.toJson`** (`Automation/DataExport.lean:269`): JSON serialization already matches the OracleProvider output format
- **`EnrichedCountermodel`** (`Automation/EnrichedCountermodel.lean:63`): Extended version with branch formulas
- **`findCountermodel`** (`Metalogic/Decidability/CountermodelExtraction.lean:174`): Lean-native countermodel extraction from tableau
- **Soundness theorem** (`Metalogic/Soundness.lean`): `soundness : (Γ ⊢ φ) → (Γ ⊨ φ)` — fully proved, sorry-free
- **`dataset_validator` executable** (`lakefile.lean`): Already exists and is called by BimodalHarness's `LeanSubprocessValidator`

#### 3b. Needs to Be Built (WHERE: BimodalHarness or a new bridge module)

1. **`validateCountermodel` function in BimodalLogic** — Given a formula JSON and countermodel JSON, construct a concrete TaskFrame/TaskModel and verify that the formula is false at the evaluation point. The `dataset_validator` exe already does this, but the internal validation logic should be a proper Lean function, not just a wrapper.

2. **`Z3CountermodelToTaskModel` extraction** — This is the critical missing piece. The Z3 oracle produces countermodels with `world_histories`, `task_relation`, `truth_valuation`, `evaluation_world`, `evaluation_time` fields. These need to be mapped to BimodalLogic's `TaskFrame D` (with `D = Int` for the discrete case) and `TaskModel`. This mapping should be a Lean function so the validation is machine-checkable.

3. **Round-trip property test** — For every formula in the benchmark set: if Z3 oracle says invalid (returns countermodel), then `dataset_validator` confirms the countermodel is valid. If Z3 oracle says valid (returns None), then the Lean decision procedure (`findCountermodel`) should also report `.valid`. This is the cross-signal consistency check but at the Lean level.

#### 3c. Where These Should Live

| Component | Location | Rationale |
|-----------|----------|-----------|
| `SimpleCountermodel`, `EnrichedCountermodel`, `toJson` | BimodalLogic | Already there, source of truth |
| `validateCountermodel` (internal Lean function) | BimodalLogic | Operates on BimodalLogic types |
| `dataset_validator` (subprocess exe) | BimodalLogic | Already there, used by BimodalHarness |
| `Z3CountermodelToTaskModel` | BimodalHarness (Lean module) or BimodalLogic | Requires both BimodalLogic types and JSON parsing |
| `OracleSoundnessTheorem` (formal statement) | BimodalHarness (Lean pkg) | Bridges both repos |
| `SoundnessGateway` (Python runtime check) | BimodalHarness | Already there |
| Z3 oracle implementation | ModelChecker/bmlogic-oracle | The thing being validated |

**The BimodalHarness is the right home for the Lean bridge module** because:
- It already has `lean-interact` as an optional dependency
- It already calls `lake exe dataset_validator` via subprocess
- It owns the soundness gateway and compatibility matrix
- It can import BimodalLogic as a Lake dependency for its own Lean code

### 4. The Soundness Theorem: What's Provable Now vs. Later

**Provable now (empirical, via testing):**
- For any specific countermodel, run `dataset_validator` and check the result
- This is what the SoundnessGateway already does
- Gives high confidence but not formal proof

**Provable with moderate effort (6-12 months):**
- **Countermodel validation theorem**: If `validateCountermodel` returns `true`, then the formula is indeed false in some BimodalLogic model. This is essentially proving the `dataset_validator` correct.
- **JSON round-trip**: `Formula.toJson` ∘ `parseJsonFormula` = id (syntactic round-trip)

**Requires significant research (12+ months):**
- **Full Oracle Soundness**: Proving that the Z3 encoding is a sound abstraction of BimodalLogic's semantics. This would require formalizing the Z3 encoding in Lean and proving it preserves (non-)satisfiability. This is essentially a verified model checker — a major research contribution.

**Strategic recommendation**: Start with the empirical testing (already in place), formalize `validateCountermodel` correctness, and leave full Z3 encoding soundness as a long-term research goal. The empirical approach gives 99.9% confidence for practical purposes.

### 5. Beyond Bimodal: Should Other Theories Get This Treatment?

**Short answer: Not yet, and the architecture should not try to support it.**

The current ModelChecker supports logos, exclusion, and imposition theories alongside bimodal. The refactor (tasks 99-105) strips these to make a bimodal-only oracle. This is correct for several reasons:

1. **Only bimodal has a formal specification** — BimodalLogic is a sophisticated Lean formalization. The other theories don't have equivalent Lean libraries.
2. **The OracleProvider protocol is theory-specific** — `formula_json` uses bimodal's 6-tag JSON schema. Other theories would need different schemas.
3. **Premature generalization is the enemy of correctness** — The goal is a provably-sound oracle. Abstraction layers add complexity that makes soundness harder to establish.

However, the **pattern** is reusable:
- Define semantics in Lean → export JSON schemas → implement Z3 oracle in Python → validate via Lean subprocess
- If logos or exclusion theories ever get Lean formalizations, the same architecture applies
- The OracleProvider/VerifierProvider protocol pattern in BimodalHarness is already generic enough

**The ModelChecker repo itself could retain the multi-theory capability for standalone use** (it's still useful as a CLI tool for exploring logics). The bmlogic-oracle would be a focused extraction. But per the research focus, the refactored repo should be bimodal-only.

### 6. CI/CD and Continuous Verification

**Current state**: The three repos are fully independent. No cross-repo CI exists.

**Recommended CI architecture:**

```
BimodalLogic change → triggers:
  1. lake build (existing)
  2. lake test (existing)
  3. Webhook to BimodalHarness CI:
     a. pip install bmlogic-oracle (latest)
     b. Run SoundnessGateway preflight
     c. Run CrossSignalConsistencyChecker on benchmark
     d. If semantics_version bumped → FAIL unless bmlogic-oracle also bumps

bmlogic-oracle change → triggers:
  1. pytest (existing bimodal tests)
  2. pip install + entry_point discovery test
  3. Run SoundnessGateway preflight against BimodalLogic (pinned version)
  4. If OracleProvider.semantics_version doesn't match pinned BimodalLogic → FAIL

BimodalHarness change → triggers:
  1. pytest (existing)
  2. Integration test with MockOracleProvider
  3. Optional: integration test with real bmlogic-oracle if installed
```

**Version pinning strategy:**
- bmlogic-oracle declares `semantics_version` matching the BimodalLogic commit/tag it was validated against
- BimodalHarness's compatibility matrix tracks which (oracle_version, semantics_version) pairs are validated
- Breaking semantic changes (new axioms, changed truth conditions) require major semantics_version bump
- Non-breaking changes (performance, new frame classes) are minor/patch

**Practical implementation**: Use git submodules or version tags, not monorepo. The repos serve different audiences and have different release cadences.

### 7. Creative/Unconventional Ideas

#### 7a. Specification Compiler (Medium-term, High Impact)

Instead of manually implementing Z3 constraints that mirror BimodalLogic's truth_at, build a **specification compiler** that takes the Lean definition of `truth_at` and mechanically generates Z3 constraints.

**How it would work:**
1. Parse BimodalLogic's `truth_at` function (it's a structural recursion on 6 constructors)
2. For each case, generate the corresponding Z3 constraint pattern
3. Output a Python module with the Z3 encoding

**Why this is feasible:**
- `truth_at` is a well-structured recursive function with clear cases
- Each case maps naturally to Z3: atom → lookup, bot → False, imp → Implies, box → ForAll worlds, untl/snce → Exists witness
- The finite model bound (N worlds, M times) is already handled by ModelChecker
- The specification is stable (6 constructors, unlikely to change)

**Why this helps soundness:**
- The generated code is mechanically derived from the Lean spec, not hand-written
- Changes to BimodalLogic's semantics automatically propagate
- Reduces the trusted computing base to the compiler itself

#### 7b. Lean 4 Z3 Binding (Long-term, Speculative)

Lean 4 can call C libraries via FFI. Z3 has a C API. A Lean 4 Z3 binding would allow:
- Running the Z3 oracle entirely within Lean
- The countermodel extraction happens in the same trusted environment as the spec
- Eliminates the Python layer entirely for the oracle

**Blockers:**
- No maintained Lean 4 Z3 binding exists
- Z3's C API is extensive (~500 functions)
- Performance concerns: Lean 4's FFI has overhead
- The Python ecosystem (BimodalHarness, training) still needs Python

**Verdict: Interesting for a research paper but not practical for the current project.**

#### 7c. Bidirectional Oracle: Use BimodalLogic's Decision Procedure as Second Oracle

BimodalLogic already has `findCountermodel` (via tableau) in `Metalogic/Decidability/CountermodelExtraction.lean`. This could serve as a **second oracle** for cross-validation:

- Z3 oracle finds countermodel → check against BimodalLogic's `findCountermodel`
- If both agree on invalidity: high confidence
- If Z3 says invalid but Lean says valid: BUG in Z3 encoding
- If Lean says invalid but Z3 says valid (timeout): Z3 is incomplete, not unsound

**This is essentially what `dataset_validator` already supports.** The recommendation is to make this a first-class feature of the CI pipeline, not just an optional cross-validation step.

#### 7d. Property-Based Testing with Formula Generators

BimodalLogic has `FormulaEnumerator.lean` and `FormulaMutator.lean` that can generate formulas systematically. Use these to:

1. Generate formulas up to complexity 5-7
2. Run BimodalLogic's decision procedure (ground truth)
3. Run Z3 oracle
4. Compare results for every formula

This is a much stronger soundness test than spot-checking 10 formulas. BimodalLogic already has the infrastructure (EnumBenchmark, BenchmarkOracle executables).

## Strategic Vision

The ideal end state is a **verified oracle ecosystem** where:

1. BimodalLogic defines the semantics and proves theorems (✅ exists)
2. bmlogic-oracle implements a fast Z3 oracle (tasks 100-105)
3. BimodalHarness validates every oracle output against BimodalLogic's decision procedure
4. CI ensures continuous cross-validation on every change to any repo
5. The compatibility matrix provides a machine-readable audit trail of what was validated when
6. Eventually, a specification compiler generates the Z3 encoding from the Lean spec, reducing the trusted code to a small compiler

The key insight is that **soundness doesn't require proving the Z3 encoding correct in Lean** (that's a research project). It requires:
- A correct Lean decision procedure (exists: `findCountermodel`)
- A correct Lean countermodel validator (exists: `dataset_validator`)
- Comprehensive empirical testing (partially exists, needs CI integration)
- Version tracking to detect when specs change (exists: `semantics_version`, compatibility matrix)

## Long-term Architecture Recommendations

1. **Keep the three repos separate** — they serve different functions and audiences
2. **BimodalLogic is the legislative branch** — it defines truth; everything else follows
3. **bmlogic-oracle is allowed to diverge in implementation** — different encoding, heuristics, optimizations are fine as long as every countermodel validates
4. **BimodalHarness is the judge** — it cross-checks oracle outputs against Lean truth
5. **Invest in CI cross-validation** before investing in formal Lean proofs of Z3 soundness
6. **Property-based testing** (formula enumeration up to complexity 7) provides near-exhaustive coverage without requiring formal proofs
7. **The specification compiler is the medium-term force multiplier** — it eliminates the manual Z3 encoding as a source of unsoundness

## Confidence Level

- Three-repo architecture vision: **high** (already largely in place)
- Lean infrastructure needed: **high** (based on detailed analysis of existing code)
- Single-source-of-truth interpretation: **high** (Option A is clearly superior)
- Beyond bimodal assessment: **medium** (depends on whether other theories get Lean formalizations)
- CI/CD recommendations: **medium** (implementation depends on infrastructure choices)
- Creative ideas: **medium** (specification compiler is feasible; Z3 FFI is speculative)
