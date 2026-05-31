# Teammate A Findings: Primary Implementation Approach

## Artifact Metadata
- **Task**: 106 - Architecture review of bimodal refactor plan
- **Teammate**: A (Primary Angle)
- **Focus**: Concrete refactoring strategy for BimodalLogic alignment with soundness bridge
- **Date**: 2026-05-30

## Key Findings

### 1. BimodalLogic Formal Structure (Source of Truth)

The BimodalLogic Lean project provides a complete formalization at `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/`. The canonical semantic definitions are:

**TaskFrame** (`Semantics/TaskFrame.lean:93`):
```lean
structure TaskFrame (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] where
  WorldState : Type
  task_rel : WorldState → D → WorldState → Prop
  nullity_identity : ∀ w u, task_rel w 0 u ↔ w = u
  forward_comp : ∀ w u v x y, 0 ≤ x → 0 ≤ y → task_rel w x u → task_rel u y v → task_rel w (x + y) v
  converse : ∀ w d u, task_rel w d u ↔ task_rel u (-d) w
```

**WorldHistory** (`Semantics/WorldHistory.lean:69`):
```lean
structure WorldHistory {D : Type*} [...] (F : TaskFrame D) where
  domain : D → Prop
  convex : ∀ (x z : D), domain x → domain z → ∀ (y : D), x ≤ y → y ≤ z → domain y
  states : (t : D) → domain t → F.WorldState
  respects_task : ∀ (s t : D) (hs : domain s) (ht : domain t),
    s ≤ t → F.task_rel (states s hs) (t - s) (states t ht)
```

**truth_at** (`Semantics/Truth.lean:122`):
```lean
def truth_at (M : TaskModel F) (Omega : Set (WorldHistory F))
    (τ : WorldHistory F) (t : D) : Formula → Prop
  | Formula.atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => truth_at M Omega τ t φ → truth_at M Omega τ t ψ
  | Formula.box φ => ∀ (σ : WorldHistory F), σ ∈ Omega → truth_at M Omega σ t φ
  | Formula.untl φ ψ => ∃ s : D, t < s ∧ truth_at M Omega τ s φ ∧
      ∀ r : D, t < r → r < s → truth_at M Omega τ r ψ
  | Formula.snce φ ψ => ∃ s : D, s < t ∧ truth_at M Omega τ s φ ∧
      ∀ r : D, s < r → r < t → truth_at M Omega τ r ψ
```

**Validity** (`Semantics/Validity.lean:73`):
```lean
def valid (φ : Formula) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]
    (F : TaskFrame D) (M : TaskModel F)
    (Omega : Set (WorldHistory F)) (h_sc : ShiftClosed Omega)
    (τ : WorldHistory F) (h_mem : τ ∈ Omega) (t : D),
    truth_at M Omega τ t φ
```

**ShiftClosed** (`Semantics/Truth.lean:295`):
```lean
def ShiftClosed (Omega : Set (WorldHistory F)) : Prop :=
  ∀ σ ∈ Omega, ∀ (Δ : D), WorldHistory.time_shift σ Δ ∈ Omega
```

**Metalogic status**: Soundness is sorry-free. Completeness has sorries (chronicle construction). Decidability (tableau) is sorry-free.

**Key formula constructors**: 6 primitives — `atom`, `bot`, `imp`, `box`, `untl` (until), `snce` (since). G, H, F, P are `def` abbreviations with `@[simp]` theorems.

### 2. ModelChecker Z3 Implementation (Current State)

The Z3 bimodal semantics at `code/src/model_checker/theory_lib/bimodal/semantic.py` already shows substantial alignment with BimodalLogic:

**Matching frame axioms**:
- `build_nullity_identity_constraint()` (line 274): `task_rel(w, 0, u) ↔ w = u` — matches `nullity_identity` exactly
- `build_converse_constraint()` (line 299): `task_rel(w, d, u) ↔ task_rel(u, -d, w)` — matches `converse`
- `build_forward_comp_constraint()` (line 338): compositionality with multi-pattern — matches `forward_comp`

**Key divergences**:
1. **Finite domain**: Z3 uses `BitVecSort(N)` for world states and bounded integer time `(-M, M)`, vs BimodalLogic's arbitrary types. This is an inherent encoding difference.
2. **World histories as arrays**: Z3 represents histories as `Array(TimeSort, WorldStateSort)` with interval bounds, vs BimodalLogic's dependent functions with convex domain proofs.
3. **ShiftClosed via Skolem**: `capped_skolem_abundance_constraint()` (line 1275) uses a Skolem function `shift_of_capped(world, delta)` to provide shifted worlds, implementing shift closure finitely.
4. **Atom domain guard**: `true_at()` (line 1438) guards atoms with `is_valid_time_for_world()`, matching BimodalLogic's `∃ (ht : τ.domain t)` domain check.
5. **Lawful evolution**: constraint at line 556 requires `task_rel(state_at_t, 1, state_at_t+1)` for consecutive times — this is a *strengthening* of `respects_task` (which requires the relation for all `s ≤ t`, not just unit steps). Combined with compositionality, unit-step lawfulness implies general lawfulness for integer time.
6. **G/H as primitive operators**: `FutureOperator` and `PastOperator` in `operators.py` are implemented as primitive operators with direct ForAll quantification, whereas BimodalLogic derives them from Until/Since. Previous research (task 106 round 1) identified this as requiring semantic equivalence verification.

### 3. BimodalHarness OracleProvider Protocol

The protocol at `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/protocol.py` defines:

- **5 properties**: `provider_id`, `provider_version`, `semantics_version`, `supported_frame_classes`, `capabilities`
- **2 methods**: `find_countermodel(formula_json, frame_class, timeout_ms) → dict | None`, `validate_self(spot_check_formulas) → bool`
- **Formula JSON schema**: 6 tags (`atom`, `bot`, `imp`, `box`, `untl`, `snce`) matching BimodalLogic's 6 primitive constructors
- **Return schema**: `trueAtoms`, `falseAtoms`, `formula` (required); `world_histories`, `task_relation`, `truth_valuation`, `evaluation_world`, `evaluation_time`, `world_count`, `time_bound` (optional structured fields)

**OracleSoundness typeclass** (from `docs/oracle-interface-standards.md:298`):
```lean
class OracleSoundness (M : Type) where
  sound : forall (phi : Formula) (m : M),
    IsCountermodelFor m phi ->
    exists (F : TaskFrame Int) (TM : TaskModel F) (Omega : Set (WorldHistory F))
      (tau : WorldHistory F) (t : Int), not (truth_at TM Omega tau t phi)
```

**Lean bridge** (`BimodalHarness/src/bimodal_harness/lean/bridge.py`): Uses `lean-interact` for REPL and `lake exe` subprocess calls. The `LeanSubprocessValidator` calls `lake exe dataset_validator --mode validate-countermodel` for cross-validation.

### 4. Alignment Mapping

| BimodalLogic Concept | Lean Definition | Z3 Implementation | Alignment |
|---|---|---|---|
| TaskFrame.WorldState | `Type` | `BitVecSort(N)` | **Divergent** (finite encoding) |
| TaskFrame.task_rel | `WorldState → D → WorldState → Prop` | `Function("TaskRel", BVS, IntSort, BVS, BoolSort)` | **Aligned** (ternary) |
| nullity_identity | `task_rel w 0 u ↔ w = u` | `build_nullity_identity_constraint()` | **Exact match** |
| forward_comp | restricted to `0 ≤ x, 0 ≤ y` | `build_forward_comp_constraint()` | **Aligned** (duration validity guards) |
| converse | `task_rel w d u ↔ task_rel u (-d) w` | `build_converse_constraint()` | **Aligned** (duration validity guards) |
| WorldHistory.domain | `D → Prop` (convex) | `world_interval_start/end` (bounded integer interval) | **Divergent** (finite interval) |
| WorldHistory.states | dependent function | `Array(TimeSort, WorldStateSort)` | **Divergent** (Z3 array) |
| WorldHistory.respects_task | `s ≤ t → task_rel (states s) (t-s) (states t)` | `lawful` constraint (unit-step) | **Sound** (unit + comp = general) |
| ShiftClosed | `∀ σ ∈ Omega, ∀ Δ, time_shift σ Δ ∈ Omega` | `capped_skolem_abundance_constraint()` | **Sound** (bounded shifts) |
| truth_at atom | `∃ (ht : domain t), valuation (states t ht) p` | `And(in_domain, truth_condition(state, atom))` | **Aligned** |
| truth_at box | `∀ σ ∈ Omega, truth_at M Omega σ t φ` | ForAll over world IDs with `is_world` guard | **Aligned** |
| truth_at untl | strict witness, open guard | `UntilOperator.true_at()` | **Needs verification** |
| truth_at snce | strict witness, open guard | `SinceOperator.true_at()` | **Needs verification** |
| G (all_future) | `def` via `¬F(¬φ)` where `F(φ) = U(φ, ⊤)` | Primitive `FutureOperator` with direct ForAll | **Needs equivalence proof** |
| H (all_past) | `def` via `¬P(¬φ)` where `P(φ) = S(φ, ⊤)` | Primitive `PastOperator` with direct ForAll | **Needs equivalence proof** |

### 5. The Soundness Claim

The precise soundness statement should be:

> **Theorem (Z3 Oracle Soundness)**: If the Z3 BimodalOracle returns a countermodel `m` for formula `φ`, then there exists a TaskFrame over `Int`, a TaskModel, a shift-closed set Omega of world histories, a history `τ ∈ Omega`, and a time `t : Int` such that `¬(truth_at TM Omega τ t φ)`.

This is exactly the `OracleSoundness` typeclass from BimodalHarness's oracle-interface-standards.md (Appendix B, line 298).

**What makes the Z3 encoding sound**:

The Z3 model finder searches over *finite* structures: N-bit world states, M-bounded integer time, finitely many world histories. A Z3 model is a concrete assignment of:
- A finite set of world states (BitVec values)
- A concrete task_rel function satisfying nullity_identity, forward_comp, converse
- A finite set of world histories (arrays with bounded integer intervals)
- A shift-closed collection (via Skolem abundance)
- A concrete valuation function
- An evaluation point (world 0, time 0)

Each of these concrete assignments *is* (or can be lifted to) a BimodalLogic structure over `Int`:
- BitVec values embed into any `WorldState` type
- The concrete task_rel satisfies the same axioms
- Each array with interval `[s, e]` defines a world history with convex domain `{t | s ≤ t ≤ e}` and states given by array lookup
- The Skolem abundance ensures shift closure
- The valuation is directly a `TaskModel`

The key step is showing that `true_at` in the Z3 encoding computes the same truth values as `truth_at` in BimodalLogic, restricted to the finite domain. This is straightforward for atom, bot, imp, box (by construction). For Until/Since it requires verifying that the Z3 encoding of strict witness + open guard matches. For G/H it requires verifying semantic equivalence with the Until/Since-based definitions.

### 6. Divergences That Are Sound

The following divergences do NOT threaten soundness:

1. **Finite world states (BitVec)**: Every finite model is a valid model in the BimodalLogic semantics (which quantifies universally over all models). If a formula has a finite countermodel, it has a countermodel.

2. **Bounded time domain**: Every bounded-time model embeds into an integer-time model. The time domain `(-M, M)` is a finite subset of `Int`, and world histories with bounded convex domains are valid `WorldHistory` structures.

3. **Array representation**: Z3 arrays with bounded intervals are equivalent to dependent functions with convex domains restricted to finite intervals.

4. **Skolem abundance (bounded shifts)**: The capped Skolem constraint provides shifts only within the finite time domain. This is a *weakening* of ShiftClosed (which requires closure under *all* shifts). However, this is still sound because: if the Z3 solver finds a countermodel *despite* only having bounded shifts available, then the formula is not valid (existence of *any* countermodel suffices). The completeness direction (if no countermodel exists in the finite domain, is the formula valid?) is separate — and is provided by BimodalLogic's decidability via the Finite Model Property.

5. **Unit-step lawfulness**: The Z3 constraint requires `task_rel(state_t, 1, state_{t+1})` only for unit steps. Combined with forward_comp and converse, this implies `task_rel(state_s, t-s, state_t)` for all `s ≤ t` within the history's domain. This matches `respects_task`.

### 7. Divergences That Need Verification

1. **G/H as primitive vs derived**: BimodalLogic defines `G(φ) = ¬F(¬φ)` where `F(φ) = U(φ, ⊤)` and equivalently `∀ s > t, truth_at ... s φ`. The Z3 `FutureOperator` directly implements `∀ s > t, truth_at`. These are semantically equivalent *if* the Z3 temporal quantification matches BimodalLogic's strict quantification. The `@[simp] theorem future_iff` in Truth.lean confirms `truth_at ... φ.all_future ↔ ∀ s, t < s → truth_at ... s φ`. So the Z3 implementation is sound — it directly implements the simp-normal form. **Verdict: Aligned, no proof needed beyond citing `future_iff`/`past_iff`.**

2. **Until/Since implementation**: Need to verify that the Z3 `UntilOperator` uses strict witness (`s > t`) and open guard (`∀ r, t < r → r < s → ...`), matching `Formula.untl` in Truth.lean. The operators.py implementation must be checked line by line.

## Recommended Approach

### Phase 1: Document the Correspondence (No Code Changes)

Create a formal correspondence document mapping each Z3 constraint to its BimodalLogic counterpart. This serves as the "soundness argument" before any Lean formalization:

1. **Frame axioms**: Direct 1-1 mapping (already done above)
2. **World history structure**: Document the embedding from Z3 arrays with intervals into WorldHistory structures with convex domains
3. **truth_at clauses**: Line-by-line comparison for all 6 formula constructors
4. **ShiftClosed**: Document how capped_skolem_abundance_constraint provides sufficient shift closure for soundness (not completeness)
5. **G/H equivalence**: Cite `future_iff`/`past_iff` simp lemmas

### Phase 2: Lean Infrastructure for Soundness Bridge

#### In BimodalLogic repo:

1. Create `Theories/Bimodal/Oracle/Interface.lean`:
   - Define `OracleSoundness` typeclass (already specified in BimodalHarness docs)
   - Define `semanticsVersion : String := "2.1.0"`
   - Define `IsCountermodelFor` predicate

2. Create `Theories/Bimodal/Oracle/Z3Frame.lean`:
   - Define `Z3TaskFrame` as a concrete `TaskFrame Int` with BitVec-valued states
   - Define `Z3WorldHistory` as a wrapper around bounded arrays
   - Define `Z3Model` bundling frame + model + Omega + evaluation point

#### In BimodalHarness repo:

3. The `LeanBridge` and `LeanSubprocessValidator` are already implemented. The `dataset_validator` executable exists in BimodalLogic for cross-validation.

#### In ModelChecker repo (or new BimodalOracle repo):

4. Create a `lean/` directory with:
   - `lakefile.lean` depending on BimodalLogic
   - `BimodalOracleSpec/Z3Frame.lean` mirroring the Z3 constraints in Lean
   - `BimodalOracleSpec/Soundness.lean` instantiating `OracleSoundness`

### Phase 3: Refactoring Strategy

The refactoring should maintain the following invariant:

> **The Z3 BimodalOracle implementation can diverge from BimodalLogic in encoding (BitVec states, bounded time, array histories, Skolem functions) but must preserve semantic equivalence for the countermodel claim.**

Concretely:
- BimodalLogic definitions are the canonical reference for what operators *mean*
- Z3 constraints are an *implementation* that searches for countermodels in a finite subdomain
- The soundness bridge proves that finite countermodels lift to full countermodels
- BimodalHarness cross-validation provides runtime verification

### Phase 4: Handshake Architecture

The three repos connect through:

```
BimodalLogic (Lean 4)
  ├── Defines: TaskFrame, truth_at, valid, OracleSoundness
  ├── Provides: lake exe dataset_validator (runtime cross-validation)
  └── Exports: Formula.toJson/fromJson, SimpleCountermodel.toJson
       │
       ├── lakefile dependency
       │
BimodalOracle / ModelChecker (Python + Lean spec)
  ├── Python: Z3OracleProvider implementing OracleProvider protocol
  ├── lean/: Z3Frame.lean mirroring Z3 constraints
  ├── lean/: Soundness.lean instantiating OracleSoundness
  └── Connects to BimodalHarness via entry point
       │
       ├── pip dependency + entry point
       │
BimodalHarness (Python + Lean bridge)
  ├── OracleProvider protocol (protocol.py)
  ├── SoundnessGateway (preflight validation)
  ├── LeanBridge (lean-interact REPL + subprocess)
  └── Cross-validation pipeline
```

**For the handshake to work when both are imported in BimodalHarness**:
1. BimodalOracle's `lean/lakefile.lean` declares `require BimodalLogic from git ...`
2. BimodalOracle's Lean spec imports BimodalLogic's `TaskFrame`, `truth_at`, `OracleSoundness`
3. BimodalOracle instantiates `OracleSoundness` for its `Z3Model` type
4. BimodalHarness calls `lake exe dataset_validator` in BimodalLogic to cross-validate countermodels
5. BimodalHarness can optionally call `lake build` in the oracle's `lean/` directory to verify the soundness proof compiles

### Lean Infrastructure Needs in This Repo (ModelChecker)

If the oracle remains in this repo (rather than a separate BimodalOracle package):

1. **`lean/` directory at repo root**:
   - `lean/lakefile.lean`: Lean package depending on BimodalLogic
   - `lean/lean-toolchain`: Pin to match BimodalLogic's toolchain (currently leanprover/lean4:v4.27.0-rc1 or compatible)

2. **`lean/BimodalOracleSpec/` modules**:
   - `Z3Frame.lean`: Define `Z3TaskFrame` as `TaskFrame Int` with finitely many world states
   - `Z3WorldHistory.lean`: Define world histories from bounded arrays
   - `Z3Model.lean`: Bundle into `Z3Model` with evaluation point
   - `CountermodelLifting.lean`: Prove `Z3Model → ∃ (F : TaskFrame Int) ...` 
   - `Soundness.lean`: Instantiate `OracleSoundness Z3Model`

3. **Key theorem** (the soundness bridge):
   ```lean
   instance : OracleSoundness Z3Model where
     sound := fun phi m h_cm => by
       -- Lift Z3Model to TaskFrame Int
       -- Show truth_at in Z3Model implies truth_at in BimodalLogic
       -- Extract the countermodel witnesses
       ...
   ```

4. **CI integration**: `lake build` in `lean/` directory as part of CI to ensure the soundness proof compiles against the current BimodalLogic version.

## Evidence/Examples

### Frame axiom alignment evidence

**Z3 nullity** (`semantic.py:274-297`):
```python
def build_nullity_identity_constraint(self):
    w = z3.BitVec('nullity_w', self.N)
    u = z3.BitVec('nullity_u', self.N)
    return z3.ForAll([w, u], self.task_rel(w, z3.IntVal(0), u) == (w == u))
```

**Lean nullity** (`TaskFrame.lean:104`):
```lean
nullity_identity : ∀ w u, task_rel w 0 u ↔ w = u
```

These are identical in meaning: Z3's `==` for BoolRef is biconditional (`↔`).

### Atom domain guard alignment

**Z3** (`semantic.py:1464-1472`):
```python
if sentence_letter is not None:
    in_domain = self.is_valid_time_for_world(eval_world, eval_time)
    eval_world_state = z3.Select(world_array, eval_time)
    return z3.And(in_domain, self.truth_condition(eval_world_state, sentence_letter))
```

**Lean** (`Truth.lean:124`):
```lean
| Formula.atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
```

Both require the time to be in the domain AND the valuation to hold. The Z3 conjunction is existential in disguise (the domain check gates the valuation).

## Confidence Level

**High confidence** on the alignment mapping and soundness argument structure. The Z3 implementation already closely mirrors BimodalLogic's definitions, with documented "ProofChecker Alignment" comments throughout `semantic.py`.

**Medium confidence** on the Lean infrastructure estimate. The actual proof work for `OracleSoundness` depends on how much of the lifting is "definitional" (which I expect most of it to be for finite models) vs requiring non-trivial reasoning.

**Medium confidence** on the G/H equivalence claim. The `future_iff`/`past_iff` simp lemmas confirm the semantic equivalence, but the Z3 operator implementations need line-by-line verification to confirm they implement exactly `∀ s, t < s → truth_at ... s φ`.
