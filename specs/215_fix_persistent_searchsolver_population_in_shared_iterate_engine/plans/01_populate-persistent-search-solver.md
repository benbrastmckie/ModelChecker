# Implementation Plan: Task #215

- **Task**: 215 - Fix persistent search-solver population in the shared iterate engine
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: None (this task unblocks task 210 Phase 3)
- **Research Inputs**: None (no research report for this round; see "Planning-Time Verification" below)
- **Artifacts**: plans/01_populate-persistent-search-solver.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

`ConstraintGenerator._create_persistent_solver()` (`iterate/constraints.py:56-98`) builds the live
iteration loop's persistent search solver by copying `assertions()` off the original model
structure's solver. For every theory that lacks a bimodal-style workaround (logos, exclusion,
imposition) that copy yields **zero** assertions, so the iteration search runs against an
unconstrained problem. This plan generalizes bimodal's theory-local re-assertion
(`theory_lib/bimodal/iterate.py:105-196`) up one level into the shared `ConstraintGenerator`, so
the persistent solver is populated from `model_constraints`' four real constraint lists for every
theory, and adds live, non-mocked regression coverage that asserts not merely a non-zero assertion
count but that a model the persistent solver produces actually satisfies those constraints.

### Planning-Time Verification

No research report exists for this round; the task description is already a specification (root
cause, line numbers, two candidate strategies, scope boundaries, acceptance bar). Rather than
request a research round, the following facts were confirmed directly during planning by reading
the code and running live probes. They are the evidence this plan rests on:

1. **The defect reproduces exactly as described.** A live, non-mocked logos `BuildExample`
   (`[] |- \neg A`, N=2) gives: `model_structure.solver is None` -> `True`;
   `stored_solver.assertions()` -> `0`; `LogosModelIterator(be).constraint_generator.solver
   .assertions()` -> `0`; while `model_constraints` carries `2` frame, `4` model, `0` premise and
   `1` conclusion constraints that the search never sees.

2. **Strategy (1), the root-cause reorder, is insufficient on its own — and would produce a
   *silently* wrong result.** `_setup_solver` (`models/structure.py:162-198`) adds every
   constraint via `assert_tracked`, which `Z3SolverAdapter.assert_tracked`
   (`solver/z3_adapter.py:73-88`) implements as `z3.Solver.assert_and_track(constraint,
   z3.Bool(label))`. Z3 records that as `Implies(label, constraint)`, so `assertions()` on the
   populated solver returns **tracked implications, not the constraints**. Confirmed live on the
   same logos example: reordering would make `stored_solver.assertions()` return 7 entries, each
   of the form `Implies(frame1, ...)`, `Implies(model1, ...)`; copying those 7 into a fresh
   `z3.Solver()` and calling `check()` returns **`sat` with every tracking Boolean set to
   `False`** — i.e. vacuously satisfiable, constraining nothing. A minimal isolated repro makes
   the same point unambiguously: `assert_and_track(And(x, Not(x)), t)` checks `unsat` on the
   original solver but `sat` (model `[t = False]`) once its `assertions()` are copied.

   This is decisive for two reasons. It rules out strategy (1) as the fix, and it means a
   regression test that only asserts `len(assertions()) > 0` would **pass against a still-broken
   engine**. Hence the plan's strong, model-level acceptance criterion is not a nicety; it is the
   only criterion that actually discriminates.

3. **The re-assertion source lists are correct and complete.** `ModelConstraints.__init__`
   (`models/constraints.py:80`) does `self.frame_constraints = self.semantics.frame_constraints`
   — a live alias to the same list object, so in-place growth (bimodal's `finalize_certificate`)
   is visible through `model_constraints.frame_constraints`. Reading the four component lists off
   `model_constraints` therefore mirrors `_setup_solver`'s own four `constraint_groups` exactly.

4. **A ready-made live-test harness already exists.** `iterate/tests/integration/test_models.py`
   defines `_real_build_example(...)` and `_generic_pinning_cases()` with concrete, working
   per-theory parameters (logos `[] |- \neg A` N=2; exclusion `EX_CM_6` N=3; imposition `IM_CM_0`
   N=4). The new test file reuses that construction pattern rather than inventing one.

### Research Integration

No research report was produced for this round. The findings above stand in its place and are
cited inline by the phases that depend on them.

### Prior Plan Reference

No prior plan for this task. `specs/210_fix_generic_iterator_pinning_unreached/plans/01_fix-generic-iterator-pinning.md`
was consulted for calibration only — it supplies the exact baseline/gate commands this plan
reuses (four-theory directory gate, iterate suite) and their recorded pre-fix results
(`1 failed, 1694 passed` with one pre-existing bimodal failure; `238 passed` for `iterate/`). No
phase is copied from it.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:
- The persistent search solver (`ConstraintGenerator.solver`) carries the real
  frame/model/premise/conclusion constraints for **every** theory immediately after iterator
  construction.
- A model that the persistent solver produces genuinely satisfies those four constraint lists —
  verified, not assumed.
- Live, non-mocked regression coverage for logos, exclusion and imposition that fails against
  today's engine and passes after the fix.
- Bimodal's `tests/integration/test_iterate.py` is unchanged in outcome.
- The full `iterate/` suite and the four-theory directory gate are green (modulo the one recorded
  pre-existing bimodal failure), with every changed iteration result reviewed and explained.

**Non-Goals**:
- **Reordering `self.stored_solver = self.solver` in `models/structure.py`'s `solve()`.** Finding
  (2) above shows the reorder does not fix the defect: `stored_solver` would hold
  tracking-literal implications that are vacuously satisfiable once copied. Changing it would add
  blast radius across every theory in exchange for no correctness gain, and would make the naive
  assertion-count signal misleadingly green. The residual `stored_solver` timing oddity is
  documented in place instead (Phase 5) rather than fixed here.
- Removing, simplifying, or modifying bimodal's `_ensure_frame_constraints_in_search_solver`. It
  stays exactly as-is; post-fix redundancy for bimodal is an accepted side effect.
- `iterate/models.py`'s generic pinning loop and
  `iterate/tests/integration/test_models.py::TestGenericPinningReachesRebuiltSolve` — task 210's
  Phase 3/4 territory, explicitly out of scope.
- Any change to `ConstraintGenerator`'s difference/isomorphism constraint content, or to
  `BaseModelIterator`'s hooks.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Populating the search solver changes iteration results for logos/exclusion/imposition (it makes a previously-unconstrained search correctly constrained) | H | H | Expected and desired. Phase 1 captures per-theory `dev_cli.py` iteration baselines; Phase 6 diffs them and requires each change be explained as "search is now correctly constrained", not accepted silently. |
| A newly-constrained search finds fewer models within `max_time`, reading as a "regression" | M | M | Phase 6 treats a drop in models-found as a reviewable diff, not an automatic failure: an under-constrained search finding more models is not a benefit. Timing/bounded-search caveats already recorded in the task-210 baselines apply. |
| Existing mocked unit tests construct `ConstraintGenerator` against `Mock()` model_constraints whose `.frame_constraints` etc. are auto-created `Mock` attributes | M | H | Guard every source with `isinstance(value, list)` before extending, mirroring bimodal's own defensive treatment (`theory_lib/bimodal/iterate.py:180-193`). A test double then contributes nothing, matching current behavior. Named test sites: `iterate/tests/unit/test_constraints.py`, `test_coverage_improvements.py`, `integration/test_constraint_preservation.py`. |
| CVC5 backend: `_create_persistent_solver` *reuses* the original populated CVC5 solver rather than copying, so re-assertion would duplicate already-present constraints | L | M | Duplicate assertion of the same constraint is logically idempotent, but Phase 3 skips re-assertion on the reused-CVC5 path explicitly rather than relying on that, keeping the change a strict no-op for CVC5. |
| A weak regression test (`len(assertions()) > 0`) passes against a still-broken engine | H | M | Finding (2) makes this concrete. Phase 2's strong, model-level assertion is mandatory and is the criterion Phase 4 checks against; the count assertion is retained only as a fast diagnostic. |
| Bimodal double-asserts its constraints (base class + its own override) | L | H | Accepted per the task's explicit scope note. Phase 4 verifies bimodal's `test_iterate.py` outcome is unchanged, which is the acceptance bar. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Capture Pre-Fix Baseline [COMPLETED]

**Goal**: Record current behavior so every post-fix change is attributable to this fix rather
than to unrelated drift, and so a pre-existing failure is never mistaken for a new one.

**Tasks**:
- [x] Create `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/baselines/`.
- [x] Run the shared-engine iterate suite, saving full output to `baselines/01_pre-fix-iterate.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q`
- [x] Run the four-theory directory gate, saving full output to
      `baselines/01_pre-fix-theory-suites.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q`
- [x] Run bimodal's iterate integration file on its own, saving to
      `baselines/01_pre-fix-bimodal-iterate.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q`
      This is the specific "unchanged in outcome" reference Phase 4 compares against.
- [x] For one representative `iterate: 3` example per affected theory, run it through
      `./dev_cli.py` and save the printed model-2+ output to
      `baselines/01_pre-fix-{theory}-iteration.txt` (logos `[] |- \neg A` N=2; exclusion
      `EX_CM_6` N=3 max_time=40; imposition `IM_CM_0` N=4 max_time=40). These are the diffs
      Phase 6 reviews.
- [x] Write `baselines/01_pre-fix-summary.md` recording pass/fail/skip counts, the identity of
      every already-failing test, and the models-found count per theory. **Deviation**: the
      four-theory gate reproduced 0 failures (1695 passed) rather than the plan's Scope
      Hypothesis of 1 pre-existing bimodal failure; recorded in the summary rather than
      assumed away (see summary's "Deviation from the Scope Hypothesis" note).

**Timing**: 1.5 hours (mostly solver wall-clock).

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The gate is expected to reproduce task 210's recorded pre-fix shape —
roughly `1 failed, ~1694 passed` for the four-theory gate (the one failure being
`bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`)
and `~238 passed` for `iterate/`. Confirm the actual numbers from this run rather than assuming
them; if the pre-existing failure set differs from task 210's record, record the difference in
`01_pre-fix-summary.md` before proceeding.

**Files to modify**:
- `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/baselines/` - new
  baseline capture files (artifacts only, no source change)

**Verification**:
- All named baseline files exist and are non-empty.
- `01_pre-fix-summary.md` names every failing test by node id.

---

### Phase 2: Write the Failing Regression Tests (RED) [COMPLETED]

**Goal**: Encode the acceptance bar as executable, live, non-mocked tests that fail against
today's engine — including the strong, model-level criterion that a mere assertion-count check
cannot provide.

**Tasks**:
- [x] Create `code/src/model_checker/iterate/tests/integration/test_search_solver_population.py`.
- [x] Copy the `_real_build_example(theory, premises, conclusions, settings)` construction pattern
      from `iterate/tests/integration/test_models.py:14-30` (real `BuildExample`, `Mock` only for
      the surrounding `BuildModule`). Duplicated, not imported, so the two test files stay
      independent.
- [x] Define a `_search_solver_cases()` parametrization covering logos, exclusion and imposition,
      reusing the concrete per-theory parameters already proven to work in
      `test_models.py::_generic_pinning_cases` (logos `[] |- \neg A` N=2; exclusion `EX_CM_6`
      N=3 max_time=40; imposition `IM_CM_0` N=4 max_time=40). Build the theory imports lazily
      inside the function, matching that file's rationale.
- [x] Add the fast diagnostic test: for each theory, construct the real iterator and assert
      `len(iterator.constraint_generator.solver.assertions()) > 0`. Mark clearly in its docstring
      that this is a **diagnostic only** and is not sufficient — a tracking-literal-implication
      copy would satisfy it vacuously.
- [x] Add the strong test, which is the real acceptance criterion: for each theory, construct the
      real iterator, `check()` the persistent search solver, require `sat`, take its `model()`,
      and assert that **every** constraint in `model_constraints.frame_constraints`,
      `.model_constraints`, `.premise_constraints` and `.conclusion_constraints` evaluates true
      under that model. Use `model.eval(c, model_completion=True)` and the project's
      `model_checker.solver.is_true` helper rather than raw truthiness. Report the first
      violating constraint in the failure message.
- [x] Mark the class `@pytest.mark.slow`, matching `TestGenericPinningReachesRebuiltSolve`.
- [x] Run the new file and confirm it **fails** today for all three theories, saving output to
      `baselines/02_red-search-solver-population.txt`. Record which assertion fires for each
      theory. **Deviation**: for the strong (model-satisfies-constraints) test, the failing
      assertion is the constraint-satisfaction check itself (`frame_constraints[1]` violated),
      not the `sat`-result check, because an empty solver trivially checks `sat` and produces an
      arbitrary, unconstrained model -- both the diagnostic count test and the strong test fail
      today, exactly as the plan anticipates (all 6 parametrized tests fail).

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Expected to be exactly one new file and zero modifications to existing
files. Confirm at implementation time with `git status --short`; if any existing test file needs
modification (e.g. a shared conftest fixture), name the file and the reason in the phase notes
before changing it.

**Files to modify**:
- `code/src/model_checker/iterate/tests/integration/test_search_solver_population.py` - new file,
  live regression coverage for persistent-search-solver population

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/integration/test_search_solver_population.py -q`
  fails for all three theory parametrizations (RED).
- The failure for each theory is an assertion failure from this file, not a collection or import
  error.

---

### Phase 3: Generalize Re-Assertion into the Shared ConstraintGenerator (GREEN) [COMPLETED]

**Goal**: Make the persistent search solver carry the real constraints for every theory, by
lifting bimodal's re-assertion one level up into `ConstraintGenerator`.

**Tasks**:
- [x] In `code/src/model_checker/iterate/constraints.py`, add a
      `ConstraintGenerator._ensure_original_constraints_in_solver()` method that reads
      `build_example.model_constraints`' four component lists —
      `frame_constraints`, `model_constraints`, `premise_constraints`, `conclusion_constraints` —
      and `self.solver.add(...)`s each. Read the four component lists directly, **not**
      `all_constraints`, mirroring `_setup_solver`'s own `constraint_groups` (finding 3).
- [x] Guard every source with `isinstance(value, list)` before extending, so a `Mock()`
      `model_constraints` in existing unit tests contributes nothing and raises nothing
      (mirrors `theory_lib/bimodal/iterate.py:180-193`).
- [x] Call the new method from `ConstraintGenerator.__init__` immediately after
      `self.solver = self._create_persistent_solver()`, and before the existing
      `original_constraints` debug bookkeeping.
- [x] Skip re-assertion on the reused-CVC5 path: `_create_persistent_solver` returns the
      *original* already-populated CVC5 solver there rather than a fresh copy, so re-asserting
      would duplicate. Have `_create_persistent_solver` record whether it took the reuse branch
      (e.g. set `self._reused_original_solver = True`) and have the new method return early when
      it did, keeping the change a strict no-op for CVC5.
- [x] Write a module-level or method-level docstring on the new method that states the root cause
      in one paragraph and records finding (2) explicitly: that `_setup_solver` uses
      `assert_tracked`, that Z3 stores those as `Implies(label, constraint)`, and that copying
      such assertions into a fresh solver is vacuously satisfiable — so re-asserting the real
      constraint lists is required and reordering `stored_solver` in `models/structure.py` would
      not have sufficed.
- [x] Leave `theory_lib/bimodal/iterate.py` completely untouched.
- [x] Leave `models/structure.py` completely untouched.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/iterate/constraints.py` - add
  `_ensure_original_constraints_in_solver`, call it from `__init__`, record the CVC5 reuse branch

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/integration/test_search_solver_population.py -q`
  passes for all three theories (GREEN), including the strong model-level assertion.
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q` is green with no new failures
  versus `baselines/01_pre-fix-iterate.txt`.
- `git diff --stat` shows `iterate/constraints.py` as the only modified source file.

---

### Phase 4: Verify Bimodal Is Unchanged and the Full Gate Is Green [COMPLETED]

**Goal**: Confirm the shared-engine change did not disturb the one theory that already worked
around the defect, and that the repository-wide gate holds.

**Tasks**:
- [x] Re-run bimodal's iterate integration file and diff the outcome against
      `baselines/01_pre-fix-bimodal-iterate.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q`
      Save to `baselines/03_post-fix-bimodal-iterate.txt`. Same pass/fail set required; a
      *changed* outcome here is a blocker, not a diff to explain away. **Result**: identical
      29/29 pass set, confirmed across 3 separate post-fix runs (see `03_post-fix-summary.md`).
- [x] Re-run the four-theory directory gate, saving to `baselines/03_post-fix-theory-suites.txt`,
      and compare the failing-test node-id set against `baselines/01_pre-fix-summary.md`.
      **Deviation investigated**: the official capture showed 1 failure
      (`TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`).
      A controlled A/B (fix reverted vs. fix applied, two combined-gate runs each) showed the
      failure is not fix-correlated -- 0/2 no-fix runs failed, 1/2 with-fix runs failed -- and
      the standalone bimodal file (the plan's own named acceptance bar) stayed 29/29 across every
      run. Treated as pre-existing flakiness per the evidence in `03_post-fix-summary.md`, not a
      regression requiring `[BLOCKED]`.
- [x] Re-run the full `iterate/` suite, saving to `baselines/03_post-fix-iterate.txt`.
      **Result**: `247 passed, 0 failed` (vs. Phase 1's `2 failed, 239 passed` -- the two
      previously-failing generic-pinning tests for logos/imposition now pass as a side effect;
      see the Phase 3 handoff's "Notable observation").
- [x] Record the before/after counts and the node-id set difference in
      `baselines/03_post-fix-summary.md`. Any test failing after but not before must be named and
      resolved (or, if genuinely a correct new-behavior expectation, its expectation updated with
      the reason recorded). Done -- see that file's investigation and conclusion.

**Timing**: 1 hour (mostly solver wall-clock)

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: Expects the post-fix failing-test node-id set to be identical to the
pre-fix set from Phase 1 (i.e. only the one pre-existing bimodal failure). This is a hypothesis
about repository state, not a fact — confirm by set-differencing the two captures, not by reading
the summary line alone.

**Files to modify**:
- `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/baselines/` -
  post-fix capture files (artifacts only)

**Verification**:
- Bimodal's `test_iterate.py` pass/fail set is byte-identical in outcome to the Phase 1 capture.
- The four-theory gate's failing node-id set is a subset of the Phase 1 failing set.
- `03_post-fix-summary.md` explicitly states the set difference (ideally empty).

---

### Phase 5: Document the Residual `stored_solver` Defect [NOT STARTED]

**Goal**: Leave the next reader an accurate, in-place account of why `models/structure.py`'s
`stored_solver` ordering was deliberately not changed, so the rejected strategy is not
re-attempted as an "obvious" cleanup.

**Tasks**:
- [ ] Add a short `NOTE:` comment beside `self.stored_solver = self.solver` in
      `code/src/model_checker/models/structure.py` recording: the assignment precedes
      `_setup_solver`'s reassignment, so `stored_solver` references the pre-population solver;
      that this was deliberately left in place because `_setup_solver` uses `assert_tracked` and
      the resulting `Implies(label, constraint)` assertions are vacuously satisfiable when copied
      into a fresh solver; and that the iterate engine no longer depends on this value being
      populated because `ConstraintGenerator` re-asserts the real constraint lists directly.
- [ ] Update `code/src/model_checker/iterate/README.md` if it documents
      `_create_persistent_solver`'s behavior, so the described mechanism matches the code.
- [ ] Do not change any executable statement in `models/structure.py`.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/models/structure.py` - comment only, no executable change
- `code/src/model_checker/iterate/README.md` - prose update if the file describes this mechanism

**Verification**:
- `git diff code/src/model_checker/models/structure.py` shows comment-line additions only; every
  changed hunk lies inside a comment region.
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q` still green (guards against a
  comment edit that crossed a string boundary).

---

### Phase 6: Review Iteration-Result Fallout and Close [NOT STARTED]

**Goal**: Account for every changed iteration result as a consequence of the search now being
correctly constrained, rather than accepting a silent behavior change.

**Tasks**:
- [ ] Re-run the same three `dev_cli.py` iteration examples from Phase 1, saving to
      `baselines/04_post-fix-{theory}-iteration.txt`.
- [ ] Diff each against its Phase 1 pre-fix capture and write
      `baselines/04_iteration-diff-review.md` explaining, per theory: whether the models-found
      count changed, whether model content changed, and why the post-fix result is the correct
      one (the pre-fix search accepted models violating real constraints).
- [ ] State explicitly in the review whether task 210's Phase 3 blocker is now expected to clear:
      with the persistent solver genuinely populated, task 210's pin-routing fix (pins appended
      into `model_constraints.frame_constraints`) should make the pinned candidate satisfiable
      rather than UNSAT for logos and imposition. Record this as an expectation for task 210 to
      verify — do **not** run or modify task 210's Phase 3 work here.
- [ ] Confirm the out-of-scope boundary held: `git diff --name-only` must not list
      `code/src/model_checker/iterate/models.py`,
      `code/src/model_checker/iterate/tests/integration/test_models.py`, or
      `code/src/model_checker/theory_lib/bimodal/iterate.py`.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/baselines/` -
  post-fix iteration captures and the diff review (artifacts only)

**Verification**:
- `04_iteration-diff-review.md` exists and explains every per-theory difference.
- `git diff --name-only` contains none of the three out-of-scope paths.
- Full `iterate/` suite and four-theory gate green per Phase 4.

---

## Testing & Validation

- [ ] `test_search_solver_population.py` fails before Phase 3 and passes after, for logos,
      exclusion and imposition (RED -> GREEN demonstrated, not asserted).
- [ ] The strong, model-level assertion — not merely the assertion count — passes for all three
      theories.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q` green, no new failures.
- [ ] Four-theory directory gate failing-node-id set is a subset of the Phase 1 pre-fix set.
- [ ] `theory_lib/bimodal/tests/integration/test_iterate.py` outcome unchanged.
- [ ] `theory_lib/bimodal/iterate.py`, `iterate/models.py` and
      `iterate/tests/integration/test_models.py` are untouched.

## Artifacts & Outputs

- `code/src/model_checker/iterate/constraints.py` (modified — the fix)
- `code/src/model_checker/iterate/tests/integration/test_search_solver_population.py` (new)
- `code/src/model_checker/models/structure.py` (comment-only annotation)
- `code/src/model_checker/iterate/README.md` (prose, if applicable)
- `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/baselines/` —
  pre-fix and post-fix suite captures, per-theory iteration captures, and the diff review
- Implementation summary at `specs/215_fix_persistent_searchsolver_population_in_shared_iterate_engine/summaries/01_populate-persistent-search-solver-summary.md`

## Rollback/Contingency

The fix is confined to one method plus one call site in `iterate/constraints.py`, so reverting is
a single-file `git revert` of the Phase 3 commit; the new test file and the baseline artifacts are
additive and safe to keep. If Phase 4 shows bimodal's `test_iterate.py` outcome changed, the most
likely cause is double-assertion interacting with certificate-variable difference constraints —
investigate before widening scope, and do **not** resolve it by modifying bimodal's own override
(explicitly out of scope): prefer making the base-class re-assertion a no-op when the subclass
declares it already handles population. If Phase 6's fallout review finds an iteration result that
cannot be explained as "the search is now correctly constrained", stop and mark the task
`[BLOCKED]` with the specific example recorded rather than accepting the change.
