# Implementation Plan: Rotation-invariant bimodal isomorphism rejection

- **Task**: 190 - Rotation invariant bimodal isomorphism rejection
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: 189 (`fix_shared_iterator_is_world_assumption`) — `completed`; the stated
  blocker no longer holds (see Research Integration)
- **Research Inputs**: `specs/190_rotation_invariant_bimodal_isomorphism_rejection/reports/01_rotation-invariant-isomorphism-rejection.md`
- **Artifacts**: plans/01_rotation-invariant-isomorphism-rejection.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/standards/status-markers.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `code/docs/core/TESTING_GUIDE.md` (mandatory TDD: RED -> GREEN -> REFACTOR)
- **Type**: python
- **Lean Intent**: false

## Overview

`BimodalModelIterator` currently treats two certificates as distinct whenever they differ in any
single label bit or box guess, so a certificate that is a rotation of a previously-found lasso's
`back`/`fwd` segments, or a relabeling of its witness lassos, is reported as a fresh model. This
plan adds a rotation/permutation-invariant notion of duplicate: a shared symmetry module defining
the group action once, a real detector in `_check_model_isomorphism` (today a hard-coded
`(False, None)`), and an orbit-wide exclusion clause in `_create_non_isomorphic_constraint` (today
the same exact-bit clause `_create_difference_constraint` uses). Done means: a live `iterate: N`
run's yielded certificates are pairwise distinct *as orbits*, not merely as bit vectors; the
bimodal suite and the logos/imposition/exclusion cross-theory regression are green; and the six
documentation sites that currently record the exclusion as open are updated.

### Research Integration

Report `01_rotation-invariant-isomorphism-rejection.md` drives four load-bearing decisions this
plan adopts wholesale:

1. **The blocker is resolved.** Task 189 is `completed`, `iterate.py`'s module docstring states in
   the present tense that the live loop consults bimodal's three extension-point overrides, and
   `TestLiveIteration` already exercises a real non-mocked `iterate: 3` run. Planning proceeds as
   unblocked; the task's `BLOCKED` framing is historical.
2. **Two hooks, not one.** `_check_model_isomorphism` (`iterate.py`) returns `(False, None)`
   unconditionally, and `iterate/core.py`'s live loop only reaches
   `_create_non_isomorphic_constraint` (via `_build_stronger_constraint`) when
   `_check_model_isomorphism` reports `True`. Richening the exclusion clause alone is a provable
   no-op. Phases 3 and 4 change both, in that order.
3. **Detection belongs at the decoded level, exclusion at the raw-Z3 level.** Detection compares
   `model_structure.certificate` (`WitnessFamily`/`LabelledLasso`, already stored by
   `semantic/model.py`) via an orbit-invariant canonical key — pure Python, unit-testable with no
   solver. Exclusion must build a `z3.BoolRef` over `WitnessRegistry._bits`/`_guesses` (plus the
   target selector, see Phase 4) because that is the only representation
   `ConstraintGenerator.check_satisfiability` understands.
4. **One shared group definition.** The report's recommendation 1 asks that the detector and the
   excluder be parameterized by the *same* group so they cannot drift — mirroring the existing
   precedent where `witness_constraints.py` imports `_coherence_window`/`_scan_forward_bound`/
   `_scan_backward_bound` directly from `certificate.py` rather than restating them. Phase 2
   creates `semantic/symmetry.py` as that single definition; Phases 3 and 4 both consume it.

### Prior Plan Reference

No prior plan for this task. Effort calibration is taken from task 189's completed plan for the
same file and test module (7 phases, comparable per-phase scope).

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch's delegation context and no `specs/ROADMAP.md`
was consulted. The durable in-repo record this task closes is the reasoned exclusion stated in
`code/src/model_checker/theory_lib/bimodal/iterate.py`'s module docstring ("Isomorphism rejection
is simplified to exact difference, not rotation/permutation invariance") and mirrored in the five
`theory_lib/bimodal/docs/*.md` sites enumerated in Phase 6.

## Goals & Non-Goals

**Goals**:

- A single, shared definition of the symmetry group `(Z/nb x Z/nf)^L ⋊ S_k` (independent per-lasso
  `back`/`fwd` rotation for all `L = 1 + k` lassos, times permutation of witness-lasso indices
  `1..k` holding lasso `0` fixed), living in one new module and consumed by both hooks.
- `_check_model_isomorphism` becomes a real detector: it reports `(True, previous_model)` when the
  new structure's certificate lies in the same orbit as a previously-found one, and
  `(False, None)` otherwise — while remaining a complete opt-out of the shared `ModelGraph` path.
- `_create_non_isomorphic_constraint` excludes the whole orbit of the model it is handed, not just
  that model's exact assignment.
- Live `iterate: N` runs yield certificates that are pairwise distinct as orbits.
- The six documentation sites that record this as an open exclusion are updated to the new
  behavior.

**Non-Goals**:

- **No change to `_create_difference_constraint` or `_certificate_variables`.** Report
  recommendation 4 scopes this task to the isomorphism pair; the difference constraint already
  correctly rejects exact duplicates on the live path and is asserted unchanged by a regression
  test in Phase 4.
- No re-adoption of the shared `ModelGraph`/`IsomorphismChecker` path for this theory. The
  override stays a total opt-out of graph-based checking; it stops being an opt-out of isomorphism
  detection *altogether*.
- No new Lean-side proof obligation. The rotation-validity question is resolved operationally (see
  Risks), not by adding a lemma to `~/Projects/BimodalLogic`.
- No change to `_create_stronger_constraint`, which stays the documented `BoolVal(True)`
  placeholder.
- No widening of `back`/`mid`/`fwd` defaults or of `max_witnesses`.

## Decisions

Three design calls this plan makes, so the implementer does not have to re-derive them:

- **D-A: permutation is provably condition-preserving; rotation is not.** Permuting witness-lasso
  indices `1..k` preserves all four certificate conditions by inspection of
  `semantic/certificate.py`: `_coherent_at` (C1) and `_fulfil_at` (C2) are evaluated per lasso
  independently, `_box_faithful` (C3) quantifies universally over `family.lassos` (so its verdict
  is invariant under any reordering), and `_target_holds` (C4) reads `family.main` only — which
  permutation fixes. Rotation is *not* generally condition-preserving: `LabelledLasso.label`
  decodes `back[t % nb]` for `t < 0`, `mid[t]` for `0 <= t < nm`, and `fwd[(t - nm) % nf]` for
  `t >= nm`, so rotating `back` moves which tuple entry sits at position `-1` while leaving
  position `0` untouched, and C1/C2 read the immediate neighbours `t±1` *across* that boundary.
  A nontrivial rotation therefore re-pairs the biconditionals at the back/mid and mid/fwd
  boundaries and has no a-priori reason to stay coherent. This is the report's open risk,
  resolved: the answer is "no in general", which is why D-B and D-C are shaped as they are.
- **D-B: detection is self-validating, so it needs no recheck.** The detector asks "is there a
  `g` with `g(previous_certificate) == new_certificate`?" — structural equality of decoded,
  frozen dataclasses. `semantic/model.py` has already run `certificate.recheck` on
  `new_certificate` and raised `ModelConstructionError` otherwise, so any `g` the detector finds
  witnesses a transform whose image is an independently-rechecked valid certificate. No
  unverified transform is ever asserted valid.
- **D-C: orbit exclusion recheck-gates each element.** The excluder enumerates `G` and, for each
  `g`, decodes `g(isomorphic_certificate)` and runs `certificate.recheck` on it, keeping only the
  elements that pass. This is the report's recommended mitigation. It is not required for
  soundness relative to the quotient (every orbit element is by definition the same model under
  the equivalence this task adopts) but it keeps the clause small and honest, and it is the
  natural place to enforce the target-time correspondence noted in Phase 4.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A nontrivial rotation is not condition-preserving, so the group's action can leave the certificate space (D-A) | M | H (established, not speculative) | Detection compares transform-of-old against the already-rechecked new certificate (D-B), so it never asserts an unverified transform. Exclusion recheck-gates each orbit element (D-C) and drops the ones that fail. |
| Rotating lasso `0` moves the label the target condition (C4) reads, so a rotation is only equivalence-preserving together with a corresponding move of the one-hot target selector | H (silently wrong detection and over-exclusion if missed) | H | The canonical key normalizes `target_time` under lasso `0`'s canonicalizing rotation (Phase 2); the exclusion clause's variable set includes `constraint_generator._sel` and the group acts on selector positions through the same slot permutation (Phase 4). Both have dedicated tests. |
| Group size growth: `(nb * nf)^(1+k) * k!` is <= 128 at the current defaults (`nb=nf=2`, `k<=2`) but reaches 24576 at `nb=nf=4, k=3` | M | L now, M for future examples | Phase 2 implements a documented size cap with a reduced generating-set fallback (identity + single-segment single-lasso rotations + adjacent witness transpositions), with the growth formula recorded in the module docstring and a test covering the fallback branch. |
| Over-exclusion: the orbit clause suppresses a certificate a user should have seen | M | L | The quotient is the feature, and the clause is a conjunction of per-element *disjunctions* over a variable set that includes the selector, which makes each conjunct as weak as possible. D-C's recheck gate drops unreachable elements. Phase 5 asserts the live model count never *drops below* what the orbit-key invariant requires. |
| Detection reads `model_structure.certificate`, which is `None` for a structure whose solve was unsat | M | L | Detector returns `(False, None)` whenever either side's certificate is `None`; dedicated test in Phase 3. |
| Changing `_check_model_isomorphism` from a constant to a real scan perturbs the live loop's `isomorphic_model_count`/termination behavior, including `test_iterate_beyond_the_admitted_certificate_space_exhausts_cleanly` | M | M | Phase 1 captures that test's baseline behavior explicitly; Phase 5 re-asserts clean exhaustion with the detector live, and the `MAX_CONSECUTIVE_INVALID`/unsat exit paths in `iterate/core.py` are left untouched. |
| Cross-theory regression: the three `is_world` theories share `iterate/core.py`'s hook call sites | H | L | No file outside `theory_lib/bimodal/` is edited except the one stale sentence in `iterate/README.md`. Phase 1 records and Phase 6 re-runs the logos/imposition/exclusion gate. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 3 |
| 4 | 5 | 1, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 3, 4 and 6 all edit
`theory_lib/bimodal/iterate.py`, which is why they are serialized rather than batched.

---

### Phase 1: Baseline capture and rotation-validity measurement [NOT STARTED]

**Goal**: Establish the green pre-change baseline, and measure empirically how the rotation group
actually behaves on real extracted certificates, so Phase 5's live-test posture is chosen from
evidence rather than hope. This phase is a **decision gate** (see plan-format.md's "Decision gates
and contingency branches").

**Tasks**:
- [ ] Run and capture the bimodal suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] Run and capture the cross-theory regression gate:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ code/src/model_checker/theory_lib/imposition/tests/ code/src/model_checker/theory_lib/exclusion/tests/ code/src/model_checker/iterate/tests/ -v`
- [ ] Save both transcripts under
      `specs/190_rotation_invariant_bimodal_isomorphism_rejection/baselines/` (per CLAUDE.md's
      per-task baselines convention), including the current pass/fail counts and the observed
      model count from `TestLiveIteration::test_iterate_beyond_the_admitted_certificate_space_exhausts_cleanly`.
- [ ] Write a throwaway measurement script in the session scratchpad (NOT committed to the repo):
      build `BM_CM_1` at `back=2, mid=1, fwd=2`, call `semantics.extract_certificate`, then for
      every element of `(Z/2 x Z/2)^L ⋊ S_k` apply the transform to the decoded `WitnessFamily`
      and run `certificate.recheck` on the result (with the target time moved under lasso 0's
      rotation).
- [ ] Record, in the phase's completion note appended to this plan: (a) `L`, `k` and the group
      size for this example; (b) how many nontrivial elements yield a `"countermodel"` verdict;
      (c) whether any nontrivial element yields a valid certificate *different from* the original
      (i.e. whether a live rotation duplicate is reachable at all for this example).
- [ ] **Gate criterion**: does at least one nontrivial group element produce a valid certificate
      distinct from the original? Record the answer verbatim — Phase 5 reads it.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `specs/190_rotation_invariant_bimodal_isomorphism_rejection/baselines/` - new; two captured
  test transcripts plus the measurement findings
- (scratchpad only, not committed) the measurement script

**Verification**:
- Both baseline commands were run and their full output is saved under `baselines/`.
- Both baselines are green (any pre-existing failure is recorded explicitly as a pre-existing
  condition, not attributed to this task).
- The gate criterion has a recorded yes/no answer with the supporting counts.
- No file under `code/` was modified in this phase.

---

### Phase 2: `semantic/symmetry.py` — the one shared group definition (TDD) [NOT STARTED]

**Goal**: Create the single module that defines the rotation/permutation group, its action on
decoded certificates, its action on `WitnessRegistry` variable keys, and the orbit-invariant
canonical key — with unit tests written first and no dependency on Z3 or on a live solve.

**Tasks**:
- [ ] RED: write `code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py` against
      the not-yet-existing module, mirroring the naming convention of the existing
      `tests/unit/test_witness_registry.py` / `tests/unit/test_certificate.py` pairs. Cover:
      - `rotate_lasso(lasso, back_shift, fwd_shift)` returns a `LabelledLasso` with `back`/`fwd`
        cyclically rotated and `mid` untouched; shift `0, 0` is the identity; shifts are taken
        modulo `nb`/`nf`.
      - `permute_witnesses(family, perm)` reorders `lassos[1:]` only, never `lassos[0]`, and
        leaves `bx` untouched; rejects a `perm` that is not a permutation of `1..k`.
      - `enumerate_group(nb, nf, lasso_count, cap=...)` yields the identity first, has size
        `(nb*nf)**lasso_count * factorial(lasso_count-1)` when under `cap`, and falls back to the
        documented reduced generating set (identity + single-segment single-lasso rotations +
        adjacent witness transpositions) when over it.
      - `apply(element, family, target_time)` returns `(transformed_family, transformed_target_time)`
        where the target time is moved under lasso `0`'s rotation and left alone when lasso `0`
        is unrotated.
      - `certificate_orbit_key(family, target_time)` is **equal** for a rotation-equivalent pair,
        **equal** for a witness-permutation-equivalent pair, **equal** for a combined pair, and
        **unequal** for a genuinely different family (different `bx`, or a `mid` difference, which
        no group element can move).
      - `certificate_orbit_key` is deterministic and total on `FrozenSet[Formula]` labels
        (`semantic/formula.py`'s dataclasses are `frozen=True` but not `order=True`, so the key
        must sort by `repr`, not by `<`).
      - Tie-breaking: when lasso `0`'s `back` is periodic so several rotations are equally
        minimal, `certificate_orbit_key` picks the same normalized target position every time
        (test with a `back` whose entries repeat).
      - `slot_action(registry, element)` maps a `(lasso, slot, formula)` `_bits` key to the key it
        moves to: `formula` untouched; `slot` remapped within `[0, nb)` or
        `[nb+nm, nb+nm+nf)` only (mid slots `[nb, nb+nm)` are fixed points, since `mid` is read by
        absolute position and has no periodic structure); `lasso` remapped by the permutation
        component, which fixes `0`. Assert it is a bijection on the key set.
      - `selector_action(registry, element)` maps a target-selector position `t` in
        `registry.target_window()` to its image under lasso `0`'s rotation, and is a bijection on
        that window.
      - `guess_action`: assert (as an explicit test, not just a comment) that no `_guesses` key is
        ever touched — guesses are per-formula, not per-lasso or per-slot.
- [ ] Confirm the tests fail for the right reason (module does not exist), not on an unrelated
      import error.
- [ ] GREEN: implement `code/src/model_checker/theory_lib/bimodal/semantic/symmetry.py`. Import
      `LabelledLasso`/`WitnessFamily` from `.certificate` and duck-type on `.nb`/`.nm`/`.nf` so a
      `WitnessRegistry` can be passed where a `LabelledLasso` is expected, exactly as
      `certificate.py`'s window helpers already do.
- [ ] Write the module docstring: the group and its size formula, why `mid` is never rotated, why
      lasso `0` is fixed by the permutation component, D-A's proof sketch (permutation preserves
      C1-C4; rotation does not in general), and the cap's reduced fallback set.
- [ ] Do **not** re-export from `semantic/__init__.py`: that package is re-export-only for the
      three public classes per `docs/THEORY_ARCHITECTURE.md`'s Theory Contract, and this module is
      internal to the iterator.
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py -v`
      to green, then the whole bimodal unit suite.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: this phase asserts exactly two new files
(`semantic/symmetry.py`, `tests/unit/test_symmetry.py`) and zero modified files. Confirm at
implementation time with `git status --short` before committing; if the implementation needs a
change to `certificate.py` (for example to export a helper), that is a scope expansion to record
in the phase note, not a silent edit.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/symmetry.py` - new; the group, its two
  actions, `apply`, and `certificate_orbit_key`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py` - new; the RED-first
  unit tests above

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v` green.
- Every test listed above exists and passes, including the cap-fallback branch and the periodic-
  `back` tie-break case.
- `python -c "import model_checker.theory_lib.bimodal.semantic.symmetry"` succeeds with
  `PYTHONPATH=code/src` and pulls in no Z3 symbol (the module is solver-free by design).

---

### Phase 3: `_check_model_isomorphism` becomes a real detector (TDD) [NOT STARTED]

**Goal**: Replace the unconditional `(False, None)` with an orbit-key scan over previously-found
models, while keeping the override a total opt-out of the shared `ModelGraph` path.

**Tasks**:
- [ ] RED: extend `TestCheckModelIsomorphism` in
      `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`:
      - Keep `test_short_circuits_without_constructing_a_model_graph` passing (patch
        `model_checker.iterate.graph.ModelGraph`, assert never called) — this is a regression
        guard on the opt-out, not a behavior to change.
      - New: with `self.model_structures`/`self.found_models` seeded with a structure whose
        certificate is a hand-built `WitnessFamily` (use `back=2, mid=1, fwd=2` settings so the
        group is nontrivial), a new structure whose certificate is a rotation of it returns
        `(True, that_previous_z3_model)`.
      - New: a witness-permuted duplicate returns `(True, ...)`.
      - New: a genuinely different certificate (a `mid` difference, which no group element can
        move) returns `(False, None)`.
      - New: a new structure whose `certificate` is `None` returns `(False, None)` and does not
        raise.
      - New: a previous structure whose `certificate` is `None` is skipped, not treated as a
        match.
      - New: the returned second element is the `z3.ModelRef` from `found_models` at the *same
        index* as the matching structure in `model_structures` — the base class's
        `zip(previous_structures, previous_models)` pairing convention
        (`iterate/graph.py`'s `IsomorphismChecker.check_isomorphism`).
- [ ] GREEN: rewrite `_check_model_isomorphism` in
      `code/src/model_checker/theory_lib/bimodal/iterate.py` to compute
      `symmetry.certificate_orbit_key(new_structure.certificate, new_structure.target_time)` and
      compare it against the key of each `(structure, model)` pair from
      `zip(self.model_structures, self.found_models)`, returning the first match. Read `nb`/`nf`
      and the lasso count from `self.build_example.model_constraints.semantics.witness_registry`.
- [ ] Add a small memo (keyed by `id(structure)` or a per-iterator dict) so a previously-found
      structure's key is computed once per iteration rather than once per comparison; keep it
      simple and local to the iterator instance.
- [ ] Rewrite the method docstring: it remains a complete opt-out of `ModelGraph` (the
      `z3_world_states`/empty-graph false positive reasoning is preserved verbatim in substance),
      and it is **no longer** an opt-out of isomorphism detection as such. State explicitly that
      this is not a re-adoption of `ModelGraph`, so a future reader cannot mistake it for one
      (report Risk 3).
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: interface

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - `_check_model_isomorphism` body and
  docstring
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` -
  `TestCheckModelIsomorphism` extended

**Verification**:
- The full bimodal suite is green, including the pre-existing `TestLiveIteration` tests (a real
  detector must not break the `iterate: 3` run captured in Phase 1's baseline; any change in that
  test's yielded count is investigated before proceeding, not accepted).
- `ModelGraph` is still never constructed for this theory (the patch-based test passes).
- The enumerated one-hop dependent, `code/src/model_checker/iterate/`, is exercised:
  `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/ -v` green.

---

### Phase 4: `_create_non_isomorphic_constraint` excludes the orbit (TDD) [NOT STARTED]

**Goal**: Replace the exact-bit clause with a conjunction that excludes every recheck-valid
element of the handed model's orbit, over a variable set that includes the target selector.

**Tasks**:
- [ ] RED: add `TestNonIsomorphicOrbitExclusion` to
      `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`, following the
      `_solved_model` fixture pattern already in `TestDifferenceConstraintOverLabelsAndGuesses`
      but at `back=2, mid=1, fwd=2` so the group is nontrivial. Cover:
      - The clause evaluates to `False` under the handed model's own assignment (it excludes at
        least that model — the invariant the existing
        `test_create_non_isomorphic_constraint_is_false_against_its_own_model` already asserts,
        which must keep passing).
      - The clause is a conjunction with one conjunct per retained orbit element, and its element
        count matches the number of group elements whose transform rechecks as `"countermodel"`.
      - For each retained element `g`, the clause evaluates to `False` under the assignment
        `g(handed_model)` — i.e. the orbit really is excluded, not just its representative.
      - An element whose transform fails `recheck` contributes no conjunct (assert by constructing
        a case where a rotation breaks coherence, per D-A).
      - Trivially `BoolVal(True)` when the registry has no variables.
      - **Regression**: `_certificate_variables()` and `_create_difference_constraint` are
        unchanged — the difference clause still ranges over `_bits` + `_guesses` only and does
        **not** include `_sel` (Non-Goal 1).
- [ ] GREEN: in `iterate.py` add
      - `_orbit_variables()` — `_bits` + `_guesses` + `constraint_generator._sel`, deliberately
        separate from `_certificate_variables()` so the difference constraint's variable set is
        untouched;
      - `_orbit_blocking_clause(iso_model)` — for each `g` from
        `symmetry.enumerate_group(...)`: decode `iso_model` to `(family, target_time)` via the
        original semantics' `extract_certificate`, apply `g`, run `certificate.recheck` against
        `semantics._premise_formulas`/`_conclusion_formulas`, and on a `"countermodel"` verdict
        emit `Or(var != value_of(iso_model, g_inverse(var)))` over `_orbit_variables()` using
        `symmetry.slot_action`/`selector_action` to find each variable's preimage;
      - rewrite `_create_non_isomorphic_constraint` to return `z3.And(*conjuncts)` (or
        `BoolVal(True)` when nothing is retained).
- [ ] Decode `iso_model` once per call, not once per group element.
- [ ] Rewrite the method docstring: the orbit it now excludes, the recheck gate and why (D-C), the
      selector's inclusion and why (C4 reads lasso `0` at `target_time`), and the group-size cap.
- [ ] Run the full bimodal suite plus `code/src/model_checker/iterate/tests/`.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: this phase asserts that the whole change fits in `iterate.py` plus
`test_iterate.py`, with no edit to `witness_constraints.py` (whose `_sel` table is read, not
mutated) and no edit to `witness_registry.py`. Confirm with `git status --short` before
committing; a needed accessor on `WitnessRegistry` or `ConstraintGenerator` is a scope expansion
to record, not a silent edit.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - `_orbit_variables`,
  `_orbit_blocking_clause`, `_create_non_isomorphic_constraint` and their docstrings
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - new
  `TestNonIsomorphicOrbitExclusion` class

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green.
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/ -v` green.
- The Non-Goal 1 regression assertion passes: `_certificate_variables()` returns exactly
  `_bits` + `_guesses`.
- The clause is `False` under every retained orbit element's assignment, verified by the new test
  rather than by inspection.

---

### Phase 5: Live-iteration coverage (gate consumer + contingency) [NOT STARTED]

**Goal**: Give the feature teeth on the live, non-mocked `iterate: N` path. This phase consumes
Phase 1's gate answer and branches accordingly.

**Tasks**:
- [ ] Add, unconditionally (this assertion holds either way and is the real invariant the task
      asks for): extend `TestLiveIteration` with a test that runs a live `iterate: N` at
      `back=2, mid=1, fwd=2` and asserts every yielded structure's
      `symmetry.certificate_orbit_key(structure.certificate, structure.target_time)` is
      **pairwise distinct** across the whole run — strictly stronger than the existing
      `test_iterate_three_yields_three_pairwise_distinct_certificates`, which only asserts
      distinctness in some raw variable.
- [ ] Re-assert clean exhaustion with the detector live: extend or duplicate
      `test_iterate_beyond_the_admitted_certificate_space_exhausts_cleanly` at the nontrivial
      settings, asserting the run still terminates with a `"solver returned unsat"` debug message
      and does not loop on isomorphic skips. Compare the yielded count against Phase 1's recorded
      baseline and explain any difference in the phase note (a *lower* count is the expected,
      intended effect of quotienting; a hang or an exception is a defect).
- [ ] **Branch A** (Phase 1's gate answered *yes* — a live rotation/permutation duplicate is
      reachable): add the fully empirical test — a live run in which
      `iterator.isomorphic_model_count` is `>= 1`, proving the detector fired on a genuine
      solver-produced duplicate, with the exclusion clause then keeping the search moving.
- [ ] **Branch B** (Phase 1's gate answered *no*): take the plan's own contingency. Add the
      semi-synthetic live test instead — seed `iterator.model_structures`/`iterator.found_models`
      with a structure/model pair, then drive one `iterate_generator()` step and assert the
      rotated duplicate is detected and excluded on the live path. Close the fully-empirical
      variant with a `#### Reasoned Exclusions` record under this phase whose `Evidence` column
      cites Phase 1's recorded measurement output verbatim, and mark the phase
      `[COMPLETED WITH EXCLUSIONS]`.
- [ ] Update the `TestLiveIteration` class docstring: it no longer describes only task 189's
      crash-fix RED test; it now also covers orbit-level distinctness.

**Timing**: 1.5 hours

**Depends on**: 1, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` -
  `TestLiveIteration` extended (and its docstring)
- `specs/190_rotation_invariant_bimodal_isomorphism_rejection/plans/01_rotation-invariant-isomorphism-rejection.md` -
  this phase's heading marker and, on Branch B, its `#### Reasoned Exclusions` table

**Verification**:
- The orbit-key pairwise-distinctness test passes on a real, non-mocked `iterate: N` run.
- The exhaustion test still terminates cleanly, with the yielded count reconciled against
  Phase 1's baseline in writing.
- Exactly one of Branch A / Branch B was taken, and the choice cites Phase 1's recorded gate
  answer.
- Full repository suite green: `PYTHONPATH=code/src pytest code/tests/ -v` and
  `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -v`.

---

### Phase 6: Documentation sync and final gate [NOT STARTED]

**Goal**: Retire every in-repo statement that this exclusion is open, and close the task on a
full, green gate.

**Tasks**:
- [ ] Rewrite `iterate.py`'s module docstring section "## Isomorphism rejection is simplified to
      exact difference, not rotation/permutation invariance" into a present-tense description of
      the new behavior, preserving the HISTORY framing convention the surrounding sections already
      use. Record D-A (permutation provable, rotation not), D-B and D-C, the group-size formula
      and cap, and the fact that `_create_difference_constraint` is deliberately unchanged.
- [ ] Update the five bimodal doc sites that state the old behavior:
      - `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` (the summary line near the top
        and the "Distinctness is exact-bit/guess difference" section)
      - `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` (both the
        design-decisions entry and the follow-on-work entry)
      - `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` (the
        `_create_non_isomorphic_constraint` entry)
      - `code/src/model_checker/theory_lib/bimodal/docs/README.md` (the "Why isomorphism rejection
        is exact-difference" pointer)
      - `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` (the "they may be rotations
        of" caveat — now false)
- [ ] Update the one stale sentence in `code/src/model_checker/iterate/README.md`'s Extension
      Guide narrative, which says bimodal's `_check_model_isomorphism` override "unconditionally
      opts out of the shared graph representation" — keep the graph opt-out, drop the implication
      that it opts out of detection.
- [ ] Add `semantic/symmetry.py` to the bimodal `docs/ARCHITECTURE.md` module inventory if that
      document carries one (confirm with a grep before editing).
- [ ] Per `.claude/rules/no-task-references-in-deliverables.md`, cite durable anchors (file and
      section names) in all of the above — never a task number, since every file touched here is
      outside `specs/**`.
- [ ] Final gate, all green:
      - `PYTHONPATH=code/src pytest code/tests/ -v`
      - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
      - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ code/src/model_checker/theory_lib/imposition/tests/ code/src/model_checker/theory_lib/exclusion/tests/ code/src/model_checker/iterate/tests/ -v`
      - `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py` runs without
        error
- [ ] Diff the final gate output against Phase 1's baselines and state, in the phase note, that
      no test regressed.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: seven documentation sites are asserted here — `iterate.py`'s module
docstring, five `theory_lib/bimodal/docs/*.md` files, and `iterate/README.md`. The count came
from `grep -rn "rotation" code/src/model_checker/theory_lib/bimodal/docs/` plus
`grep -n "_check_model_isomorphism" code/src/model_checker/iterate/README.md`. Re-run both greps
at implementation time and reconcile: a site the grep finds that this list omits is a scope
expansion to record in the phase note; a listed site the grep no longer finds is an overcount to
close as a reasoned exclusion.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - module docstring
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` - distinctness sections
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - design decision and
  follow-on-work entries, module inventory
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` -
  `_create_non_isomorphic_constraint` entry
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` - the exclusion pointer
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - the rotation caveat
- `code/src/model_checker/iterate/README.md` - the Extension Guide narrative sentence

**Verification**:
- `grep -rn "not rotation/permutation invarian" code/src/model_checker/` returns nothing.
- `grep -rn "A follow-on task should implement the full symmetry-aware rejection" code/src/` returns
  nothing.
- All four final-gate commands are green, and the diff against Phase 1's baselines shows no
  regression.
- `bash .claude/scripts/check-task-references.sh` (or the repo's equivalent lint) reports no new
  task-number reference outside `specs/**`.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py -v` — the new solver-free unit suite, green.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` — full bimodal suite, green.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/ -v` — the shared iterate framework, green (no hook-contract regression).
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ code/src/model_checker/theory_lib/imposition/tests/ code/src/model_checker/theory_lib/exclusion/tests/ -v` — the cross-theory regression gate task 189's summary records, green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — repository suite, green.
- [ ] `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py` — the example set still runs end to end.
- [ ] Behavioral check, not just a passing suite: a live `iterate: N` run's yielded certificates are pairwise distinct as *orbits*, and the run still exhausts cleanly rather than looping on isomorphic skips.
- [ ] Coverage: the new `semantic/symmetry.py` is covered at the project's >90% critical-path bar (`pytest --cov=model_checker.theory_lib.bimodal.semantic.symmetry --cov-report=term-missing`).

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic/symmetry.py` — new; the single shared group definition, its two actions, and `certificate_orbit_key`.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py` — new; solver-free unit coverage of the group and the canonical key.
- `code/src/model_checker/theory_lib/bimodal/iterate.py` — modified; real detector, orbit-wide excluder, rewritten module and method docstrings.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` — modified; extended `TestCheckModelIsomorphism`, new `TestNonIsomorphicOrbitExclusion`, extended `TestLiveIteration`.
- `code/src/model_checker/theory_lib/bimodal/docs/{ITERATE,ARCHITECTURE,API_REFERENCE,README,USER_GUIDE}.md` and `code/src/model_checker/iterate/README.md` — modified; the open-exclusion statements retired.
- `specs/190_rotation_invariant_bimodal_isomorphism_rejection/baselines/` — new; Phase 1's pre-change test transcripts and the rotation-validity measurement findings.
- `specs/190_rotation_invariant_bimodal_isomorphism_rejection/summaries/01_rotation-invariant-isomorphism-rejection-summary.md` — the implementation summary.

## Rollback/Contingency

- **Per-phase**: every phase commits per green sub-step (`.claude/rules/git-workflow.md`'s
  Commit-Per-Green-Substep Mandate), so a failed phase reverts to the last green commit with an
  ordinary scoped `git revert` — no working-tree discard needed.
- **Before Phase 4's risky edit** (the only phase that rewrites a live Z3 clause builder), take a
  durable, non-reverting checkpoint with
  `bash .claude/scripts/git-snapshot.sh 190 --no-revert` (see
  `.claude/context/patterns/checkpoint-before-overflow.md`). Do **not** use the default reverting
  form as a routine precaution.
- **If a genuine whole-tree rollback becomes necessary**, follow
  `.claude/context/contracts/recovery.md`'s rollback rung for the exact invocation shape,
  including its out-of-scope override flag.
- **Feature-level fallback**: the change is additive and confined to `theory_lib/bimodal/`. The
  whole feature can be disabled by restoring `_check_model_isomorphism` to `return False, None`,
  which returns the live loop to exact-bit distinctness (the pre-change behavior) in one edit,
  leaving `semantic/symmetry.py` and its unit tests in place as dead-but-tested code. State this
  explicitly in the summary as the documented escape hatch.
- **If Phase 1's measurement shows the group is trivial for every example in the repository**
  (`nb = nf = 1` everywhere in practice), the feature is correct but inert. That is not a reason to
  abandon it — the default settings are `back=2, mid=1, fwd=2`, so the group is nontrivial at the
  defaults — but it must be stated plainly in the summary rather than presented as a behavior
  change users will observe.
