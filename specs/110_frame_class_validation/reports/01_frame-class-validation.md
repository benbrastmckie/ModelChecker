# Frame Class Validation: Z3 Oracle "Base" Frame Class

- **Task**: 110 - Frame class validation for Base frame
- **Type**: Research
- **Date**: 2026-06-01
- **Sources**: semantic.py, BimodalLogic/Theories/Bimodal/ProofSystem/Axioms.lean,
  BimodalLogic/Theories/Bimodal/FrameConditions/FrameClass.lean,
  BimodalLogic/Theories/Bimodal/Semantics/TaskFrame.lean

---

## Executive Summary

The Z3 oracle's "Base" frame class declaration in task 103 is broadly justified but
requires precise qualification. The Z3 oracle (`BimodalSemantics`) enforces the three
core `TaskFrame` axioms (nullity_identity, forward_comp, converse) that appear in
BimodalLogic's `TaskFrame.lean` structure definition. However, several structural
constraints in the Z3 oracle go beyond the pure `TaskFrame` definition: lawful world
histories, shift closure (abundance), world uniqueness, and convex world ordering.
These are **model-building constraints** needed to find finite countermodels but are
not axioms of the frame class itself.

The disabled `task_restriction` constraint (constraint 10) creates a partial
**frame-to-model mismatch** but is not a soundness issue for countermodel generation.

The term "Base" in BimodalLogic's `FrameClass.lean` refers to the base proof-system
frame class (valid on all linear temporal orders), while the oracle's use of "Base"
would mean something different: a frame satisfying `TaskFrame` axioms with a serial,
shift-closed Omega. Formal alignment requires documentation of this distinction.

---

## 1. Z3 Frame Axioms in semantic.py

All three TaskFrame axioms are implemented as Z3 universal quantifier constraints,
built in `build_frame_constraints()` (semantic.py:467-697).

### 1.1 nullity_identity (semantic.py:274-297)

```python
def build_nullity_identity_constraint(self):
    """task_rel(w, 0, u) <-> w = u"""
    w = z3.BitVec('nullity_w', self.N)
    u = z3.BitVec('nullity_u', self.N)
    return z3.ForAll(
        [w, u],
        self.task_rel(w, z3.IntVal(0), u) == (w == u)
    )
```

**Location**: semantic.py:274-297
**What it enforces**: Zero-duration task relates a state to itself, and ONLY to itself.
This is a biconditional — stronger than mere reflexivity.

### 1.2 converse (semantic.py:299-336)

```python
def build_converse_constraint(self):
    """task_rel(w, d, u) <-> task_rel(u, -d, w) under duration validity guards"""
    w = z3.BitVec('converse_w', self.N)
    u = z3.BitVec('converse_u', self.N)
    d = z3.Int('converse_d')
    guard = z3.And(self.is_valid_duration(d), self.is_valid_duration(-d))
    return z3.ForAll(
        [w, u, d],
        z3.Implies(
            guard,
            self.task_rel(w, d, u) == self.task_rel(u, -d, w)
        )
    )
```

**Location**: semantic.py:299-336
**What it enforces**: Time-reversal symmetry. Going from w to u in duration d is
equivalent to going from u to w in duration -d.
**Guard**: `is_valid_duration(d)` restricts d to `(-M, M)`, ensuring both d and -d
are within the bounded domain.

### 1.3 forward_comp (semantic.py:338-388)

```python
def build_forward_comp_constraint(self):
    """If task_rel(w,d1,v) and task_rel(v,d2,u) then task_rel(w, d1+d2, u)"""
    # 5 quantified variables with multi-pattern for Z3 efficiency
    return z3.ForAll(
        [w, v, u, d1, d2],
        body,
        patterns=[z3.MultiPattern(self.task_rel(w, d1, v), self.task_rel(v, d2, u))]
    )
```

**Location**: semantic.py:338-388
**What it enforces**: Compositionality — sequential tasks compose with summed durations.
**Multi-pattern**: Uses `z3.MultiPattern` to guide Z3's E-matching instantiation,
reducing solver overhead for the 5-variable quantifier.
**Guards**: Duration validity guards on d1, d2, and d1+d2.

### 1.4 Additional World-Structure Constraints

Beyond the three TaskFrame axioms, the Z3 oracle enforces:

| Constraint | Location | Purpose |
|-----------|----------|---------|
| `valid_main_world` | semantic.py:507 | Main evaluation world is valid |
| `valid_main_time` | semantic.py:510 | Main evaluation time is valid |
| `enumeration_constraint` | semantic.py:518-525 | World IDs are non-negative |
| `convex_world_ordering` | semantic.py:530-544 | No gaps in world ID sequence |
| `world_interval` | semantic.py:552 | Each world has a valid time interval |
| `lawful` | semantic.py:558-582 | Each world history respects task_rel at unit steps |
| `skolem_abundance` | semantic.py:604 | Shift-closed world set exists |
| `world_uniqueness` | semantic.py:614-634 | Distinct worlds map to distinct histories |

These constraints collectively define the **model-building environment** — the
finite structure within which countermodels are searched. They are not axioms of
the BimodalLogic `TaskFrame` structure itself.

---

## 2. BimodalLogic Frame Hierarchy

### 2.1 FrameClass in the Proof System

**Location**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/ProofSystem/Axioms.lean:422-465`

```lean
inductive FrameClass where
  | Base
  | Dense
  | Discrete
  deriving Repr, DecidableEq, Inhabited
```

The FrameClass partial order:
```
Dense     Discrete
  ↑         ↑
   \       /
    Base
```

- **Base**: 37 axioms, valid on all linear temporal orders. Includes all BX temporal
  axioms, S5 modal axioms, propositional axioms, and interaction axiom (MF).
- **Dense**: Base + density axiom (`GGφ → Gφ`) + dense_indicator (`¬U(⊤,⊥)`).
  Valid on densely ordered frames.
- **Discrete**: Base + Prior-UZ, Prior-SZ, Z1. Valid on discrete frames
  (`SuccArchimedean` orders like `ℤ`).

`FrameClass.Base` is the **proof-system** concept — it classifies axiom validity.
It is NOT a semantic frame type.

### 2.2 LinearTemporalFrame and SerialFrame Typeclasses

**Location**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/FrameConditions/FrameClass.lean`

```
LinearTemporalFrame (AddCommGroup + LinearOrder + IsOrderedAddMonoid)
        |
   SerialFrame (+ Nontrivial + NoMaxOrder + NoMinOrder)
      /    \
DenseTemporalFrame       DiscreteTemporalFrame
(+ DenselyOrdered)        (+ SuccOrder + PredOrder + IsSuccArchimedean)
```

These are **semantic frame typeclasses** (marker classes bundling Mathlib constraints):

- `LinearTemporalFrame D`: The temporal domain D has ordered additive group structure.
- `SerialFrame D`: Linear temporal frame with no maximum or minimum elements.
  This provides witnesses for the seriality axioms `F(⊤)` and `P(⊤)`.
- `DiscreteTemporalFrame D`: Serial frame with immediate successor/predecessor structure.
  `Int` is the canonical instance.

### 2.3 TaskFrame Structure

**Location**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Semantics/TaskFrame.lean:93-122`

```lean
structure TaskFrame (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] where
  WorldState : Type
  task_rel : WorldState → D → WorldState → Prop
  nullity_identity : ∀ w u, task_rel w 0 u ↔ w = u
  forward_comp : ∀ w u v x y, 0 ≤ x → 0 ≤ y → task_rel w x u → task_rel u y v → task_rel w (x + y) v
  converse : ∀ w d u, task_rel w d u ↔ task_rel u (-d) w
```

This is the **semantic frame structure** — the fields that define what a task frame
is. The Z3 oracle's three axiom builder methods correspond exactly to these three
fields.

**Key difference from Z3 oracle**: The Lean `forward_comp` is restricted to
`0 ≤ x → 0 ≤ y` (non-negative durations only), while the Z3 oracle's `forward_comp`
uses general duration validity guards `is_valid_duration(d)` covering `(-M, M)`.
This is not a gap — the Lean TaskFrame comment explicitly states:
"Achieved via `forward_comp` (restricted to 0 ≤ x, 0 ≤ y) plus `converse`"
which gives full compositionality via direction reversal.

---

## 3. Axiom Mapping Table: Z3 Oracle ↔ BimodalLogic

| Z3 Oracle Constraint | BimodalLogic Lean Counterpart | Type | Notes |
|---------------------|-------------------------------|------|-------|
| `build_nullity_identity_constraint()` | `TaskFrame.nullity_identity` (TaskFrame.lean:104) | **TaskFrame axiom** | Exact correspondence: biconditional |
| `build_forward_comp_constraint()` | `TaskFrame.forward_comp` (TaskFrame.lean:114) | **TaskFrame axiom** | Z3 uses general duration guards; Lean restricts to `0 ≤ x` but derives full compositionality via converse |
| `build_converse_constraint()` | `TaskFrame.converse` (TaskFrame.lean:122) | **TaskFrame axiom** | Exact correspondence: biconditional with duration validity guard in Z3 |
| `lawful` constraint | `WorldHistory` / `respects_task` | **Model-building** | Enforces that each world history follows task_rel at unit steps; corresponds to `WorldHistory.respects_task` in WorldHistory.lean |
| `skolem_abundance` (capped_skolem_abundance_constraint) | `ShiftClosed` (Truth.lean:295) | **Model-building** | Ensures Ω is shift-closed; aligns with JPL paper app:auto_existence |
| `world_uniqueness` | (no direct Lean axiom) | **Model-building** | Required for finite model distinctness; not a frame axiom |
| `enumeration_constraint` | (no direct Lean axiom) | **Model-building** | World ID bookkeeping |
| `convex_world_ordering` | (no direct Lean axiom) | **Model-building** | Required for finite model enumeration |
| `world_interval` | (no direct Lean axiom) | **Model-building** | Domain bounds for world histories |
| ~~`task_restriction`~~ (DISABLED) | (no direct Lean axiom; partial semantic intent) | **Disabled** | See Section 4 |
| ~~`task_minimization`~~ (DISABLED) | (no direct Lean axiom) | **Disabled** | Performance heuristic |

---

## 4. Analysis of the Disabled task_restriction Constraint

### 4.1 What task_restriction Would Enforce

**Location**: semantic.py:636-672

```python
# 10. Task relation only holds between states in lawful world histories
task_restriction = z3.ForAll(
    [some_state, some_duration, next_state],
    z3.Implies(
        self.task_rel(some_state, some_duration, next_state),
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                self.is_world(task_world),
                self.is_valid_duration(some_duration),
                # Source and target are both in a lawful world at the right times
                some_state == z3.Select(self.world_function(task_world), time_shifted),
                next_state == z3.Select(self.world_function(task_world), time_shifted + some_duration)
            )
        )
    )
)
```

The constraint would enforce: `task_rel(s, d, u)` holds only if there exists a lawful
world history where state `s` occurs at time `t` and state `u` occurs at time `t+d`.
This would anchor the abstract task relation to the concrete world histories.

### 4.2 Why It Is Disabled

The code comment reads (semantic.py:695):
```python
# MAYBE (not yet enabled, preserved for future experimentation):
# task_restriction,     # restricts task_rel to lawful histories
```

The `task_restriction` constraint is labeled "MAYBE" — it is kept for future
investigation but has not been validated as necessary or correct. The implicit
engineering reason for disabling it is likely **performance**: adding this doubly-
quantified constraint (`ForAll` + nested `Exists` with 5 bound variables) significantly
increases Z3 solving time, especially for UNSAT checks where Z3 must prove the
constraint is satisfied under all possible task relations.

### 4.3 Soundness Analysis

**Does disabling task_restriction create soundness issues?**

The answer depends on the definition of "soundness" in context:

**For countermodel validity**: A countermodel found by the Z3 oracle is a structure
where the formula is false. The task_rel in such a model may contain "phantom"
task-pairs that do not correspond to any lawful world history (because task_restriction
is disabled). This means:

- The three TaskFrame axioms (nullity_identity, forward_comp, converse) ARE enforced
- But the task relation is NOT required to be grounded in world histories
- This could produce countermodels with a task_rel that is overly permissive

**For proving formulas valid**: If the oracle returns no countermodel (UNSAT), the
formula is valid in the search domain. Disabling task_restriction makes the search
domain LARGER (more models are admitted), which makes UNSAT results HARDER to achieve.
If the oracle returns UNSAT despite the larger domain, the formula is certainly
valid in the restricted domain. This direction is sound.

**For countermodel validity check by BimodalHarness**: If BimodalHarness validates
returned countermodels by checking the three frame axioms only (nullity_identity,
forward_comp, converse), then the countermodels are valid as TaskFrame instances.
If validation also checks that task_rel pairs correspond to lawful world histories,
countermodels may fail validation.

**Conclusion**: Disabling task_restriction is not a soundness issue for the oracle's
primary purpose (finding countermodels to falsify formulas) provided:
1. The oracle's found countermodel is validated by post-hoc checking the TaskFrame axioms
2. The oracle's UNSAT results are only used as "formula may be valid" (unknown), not
   as definitive proofs of validity

The `StructuredCountermodel.validate()` method in task 226's countermodel.py already
performs post-hoc frame axiom checking. This should be the validation contract.

### 4.4 Specific Gap Created

With task_restriction disabled, the following scenario is possible:
- World w1 has states: [s0, s1] at times [0, 1]
- World w2 has states: [s2, s3] at times [0, 1]
- task_rel(s0, 5, s2) = True (Z3 may freely set this)
- But there is no world with s0 at time t and s2 at time t+5

This phantom task-pair satisfies nullity_identity, forward_comp, and converse but is
semantically meaningless — it corresponds to no lawful history. The `lawful` constraint
only enforces FORWARD unit-step tasks within each world; it does not constrain the
abstract task relation to match cross-world transitions.

---

## 5. What the Oracle Guarantees About task_rel Structure

Given the active constraints, the Z3 oracle guarantees that every extracted
countermodel satisfies:

1. **Nullity Identity**: `∀ w u. task_rel(w, 0, u) ↔ (w = u)` — zero duration iff identity
2. **Converse**: `∀ w d u. valid_dur(d) ∧ valid_dur(-d) → (task_rel(w, d, u) ↔ task_rel(u, -d, w))`
3. **Forward Compositionality**: `∀ w v u d1 d2. task_rel(w,d1,v) ∧ task_rel(v,d2,u) ∧ valid_dur(d1) ∧ valid_dur(d2) → task_rel(w,d1+d2,u)`
4. **World Lawfulness**: `∀ world time. is_world(world) ∧ valid_time(time) → task_rel(state(world,time), 1, state(world,time+1))`
5. **Shift Closure**: `∀ world shift. shifted world exists if shift keeps interval in bounds`
6. **Serial Frame (implicit)**: The `is_valid_time` domain is open-ended in both directions within bounds `(-M, M)`, and with sufficient M, seriality axioms hold
7. **World Uniqueness**: `∀ w1 w2. w1 ≠ w2 → ∃ t. state(w1,t) ≠ state(w2,t)`

The oracle does NOT guarantee:
- `task_rel` pairs are grounded in lawful world histories (task_restriction disabled)
- The time domain is truly unbounded (it is bounded by M)
- NoMaxOrder/NoMinOrder for the global time domain (bounded domain)

---

## 6. FrameClass Terminology Mismatch

There is a naming collision between two uses of "Base":

### BimodalLogic's FrameClass.Base
- Defined in: ProofSystem/Axioms.lean:422-425
- Meaning: Axioms valid on ALL linear temporal orders (minimum frame class)
- The 37 base axioms include all BX temporal, S5 modal, propositional, and MF interaction axioms
- A formula valid on Base frames means it is proved by these 37 axioms alone
- Not a semantic frame type — a proof-system classification

### Oracle's "Base" in supported_frame_classes
- Claimed by: task 103 (OracleProvider stub) — `supported_frame_classes=frozenset({"Base"})`
- Intended meaning: The oracle produces countermodels that are TaskFrame instances
  satisfying DiscreteTemporalFrame-like properties (with Int-like time bounded to `(-M, M)`)
- Actually implemented: TaskFrame axioms + world-structure constraints + bounded integer time
- NOT a densely-ordered frame, NOT a FrameClass.Dense frame

### Recommended Naming
Given the semantics of the Z3 oracle, the supported_frame_classes should be:
- `"TaskFrameBase"` — satisfies nullity_identity, forward_comp, converse
- `"DiscreteSerial"` — also satisfies seriality (via bounded domain with sufficient M)
- Or simply document that "Base" in the oracle context means `TaskFrame` axioms hold,
  distinct from BimodalLogic's `FrameClass.Base` proof-system concept

---

## 7. Existing Test Infrastructure

### 7.1 Unit Tests for Frame Constraints

**Location**: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`

Three test classes cover the three active TaskFrame axioms:
- `TestNullityIdentity`: Tests that zero-duration self-tasks hold and cross-state zero-duration tasks are UNSAT
- `TestConverse`: Tests time-reversal symmetry and bidirectionality
- `TestForwardComp`: Tests compositionality via explicit task assertions
- `TestConstraintInteractions`: Smoke tests for joint satisfiability of all frame axioms

These tests validate each axiom in isolation and together but do NOT:
- Test that extracted countermodels satisfy the frame axioms (post-hoc validation)
- Test the relationship between task_rel and world histories
- Test the effect of the disabled task_restriction

### 7.2 Integration Tests

**Location**: `code/src/model_checker/theory_lib/bimodal/tests/integration/`

Several integration tests exist:
- `test_data_extraction.py`: Tests extraction of model elements from solved Z3 instances
- `test_strict_semantics.py`: Tests strict temporal semantics
- `test_until_since_integration.py`: Tests Until/Since operator semantics

None of these explicitly test frame class conformance against the BimodalLogic
Lean hierarchy.

---

## 8. Recommendations for Implementation Phase

### 8.1 test_frame_class_mapping.py Test Plan

A new test file at:
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`

Should assert the following for extracted countermodels:

**Fixture**: Run the oracle on known-countermodel-existant formulas from `examples.py`
(e.g., `BM_CM_1` through `BM_CM_N` examples with `expectation=True`).

**Test class 1: NullityIdentityPostHoc**
```python
def test_extracted_model_nullity_identity(countermodel):
    for s, d, u in countermodel.task_rel_pairs:
        if d == 0:
            assert s == u, f"task_rel({s}, 0, {u}) must have s == u"
        # And: for every state s, task_rel(s, 0, s) must hold
```

**Test class 2: ConversePostHoc**
```python
def test_extracted_model_converse(countermodel):
    for s, d, u in countermodel.task_rel_pairs:
        # Check converse holds
        assert (u, -d, s) in countermodel.task_rel_pairs or d == 0
```

**Test class 3: ForwardCompPostHoc**
```python
def test_extracted_model_forward_comp(countermodel):
    pairs = set(countermodel.task_rel_pairs)
    for s, d1, v in pairs:
        for _, d2, u in [(s2, d2, u2) for (s2, d2, u2) in pairs if s2 == v]:
            assert (s, d1+d2, u) in pairs, f"Composition {s}-{d1+d2}-{u} must exist"
```

**Test class 4: LawfulHistoryCheck**
```python
def test_extracted_model_lawful(countermodel):
    for world_id, history in countermodel.histories.items():
        for t, state in history.items():
            if t + 1 in history:
                assert (state, 1, history[t+1]) in countermodel.task_rel_pairs
```

**Test class 5: FrameClassDeclarationConsistency**
```python
def test_frame_class_claims_are_justified():
    # Z3 oracle claims "Base" support — verify this means TaskFrame axioms hold
    # Document what "Base" means in the oracle's terminology vs BimodalLogic
    assert "Base" in Z3OracleProvider().supported_frame_classes
    # Frame documentation should state: "Base" = TaskFrame axioms satisfied
    # NOT the same as BimodalLogic FrameClass.Base (proof-system concept)
```

### 8.2 Documentation Fix

The OracleProvider stub's `supported_frame_classes=frozenset({"Base"})` declaration
needs a docstring clarifying:
- "Base" here means `TaskFrame` axioms (nullity_identity, forward_comp, converse) hold
- This is NOT equivalent to BimodalLogic's proof-system `FrameClass.Base`
- The oracle uses bounded integer time `(-M, M)`, not the unbounded `Int` of `DiscreteTemporalFrame`

### 8.3 task_restriction Enablement Investigation

Future work (not blocking task 103/110): Investigate enabling `task_restriction` with:
1. A timeout-guarded SAT check where task_restriction is tried first, then removed if UNSAT takes too long
2. A post-processing step that validates whether found task_rel pairs are grounded in world histories
3. Evaluate on the 43-example test suite to measure performance impact

### 8.4 Converse Guard Discrepancy

The Z3 converse constraint uses `is_valid_duration(d)` to guard the biconditional,
but the Lean `TaskFrame.converse` is an unconditional biconditional (`∀ w d u`).
For the bounded finite model (Z3 oracle), the guard is needed to prevent duration
overflow. This is a finite-model approximation — document it explicitly.

When `d = M-1` (at the boundary), `-d = -(M-1)` is still within valid duration bounds.
When `d = M` (at the edge), `-d = -M` would be out of bounds. The guard ensures
the converse is only checked for d values where both directions are well-defined.
This is sound: the oracle checks converse only within the finite temporal domain.

---

## 9. Gaps and Ambiguities

| Gap | Description | Severity |
|-----|-------------|----------|
| Naming collision | "Base" in oracle vs "Base" in FrameClass | Medium — needs docstring clarification |
| task_restriction disabled | task_rel may contain phantom pairs | Low — doesn't break countermodel validity for frame axiom checking |
| Converse guard | Z3 version is guarded; Lean version is unconditional | Low — sound finite approximation |
| forward_comp asymmetry | Z3 uses general duration guards; Lean restricts to 0 ≤ x, 0 ≤ y | Low — equivalent via converse |
| No seriality constraint | SerialFrame requires NoMaxOrder/NoMinOrder; Z3 has bounded domain | Medium — with sufficient M, seriality holds for interior time points but not at boundaries |
| Bounded vs unbounded time | Z3 uses `(-M, M)`; Lean TaskFrame uses `Int` (unbounded) | Medium — countermodels are valid in bounded models but may not generalize to unbounded `Int` |

---

## 10. Summary

The Z3 oracle's three active frame axioms (nullity_identity, forward_comp, converse)
correspond exactly to BimodalLogic's `TaskFrame` structure fields. The oracle produces
countermodels that are valid `TaskFrame` instances over a bounded integer domain.

The disabled `task_restriction` creates a gap between the abstract task relation and
grounded world histories but is not a soundness issue for the oracle's primary purpose.

The term "Base" in `supported_frame_classes=frozenset({"Base"})` needs documentation
to clarify it refers to `TaskFrame` axiom satisfaction, not BimodalLogic's proof-system
`FrameClass.Base` concept.

The proposed `test_frame_class_mapping.py` should perform post-hoc validation of
extracted countermodels against the documented frame axioms.
