# Implementation Plan: Fix stale `ModelConstraints.all_constraints` snapshot

- **Task**: 207 - Fix stale `all_constraints` snapshot; audit every production reader
- **Status**: [IMPLEMENTING]
- **Effort**: 4.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/207_fix_stale_all_constraints_snapshot/reports/01_fix-stale-all-constraints.md
- **Artifacts**: plans/01_fix-stale-all-constraints.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/context/standards/artifact-management.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - code/docs/core/TESTING_GUIDE.md (mandatory TDD: RED -> GREEN -> REFACTOR)
- **Type**: z3
- **Lean Intent**: false

## Overview

`models/constraints.py:97` computes `all_constraints` once in `__init__` as an eager list
concatenation, so it is frozen at construction time while `self.frame_constraints` (a *reference*
to `semantics.frame_constraints`) keeps growing. For bimodal — whose encoding is deliberately
two-phase (decision D6): `frame_constraints` starts empty and is populated later by
`finalize_certificate()` — `all_constraints` therefore permanently omits the entire (C1)-(C4)
certificate encoding, for **every** solve, not only iterated ones (research measured length 2
against a true solved set of 132). This plan converts `all_constraints` into a read-only computed
property (the shape the test tree's `full_constraints()` already uses), migrates the single
production write site and the three dead `append`-into-`all_constraints` sites that a property
would silently turn into no-ops, and verifies under CI's own two-invocation gate shape because the
attribute is cross-theory. Definition of done: `all_constraints` always reflects the current
component lists for all four theories, no production site assigns to or appends to it, the full
repository gate is green at or above the recorded pre-fix baseline, and no existing assertion has
been narrowed.

### Research Integration

Key findings from `reports/01_fix-stale-all-constraints.md` that this plan is built on:

- **F1 (root cause confirmed; scope correction)**: the gap affects every bimodal solve, not only
  iterated ones. `self.frame_constraints` aliases `semantics.frame_constraints` by reference and
  stays live; `self.all_constraints` is a new list object frozen at construction.
- **F2 (blast-radius reducer)**: `models/structure.py`'s `_setup_solver` — the base implementation
  that logos/exclusion/imposition use unmodified, and that bimodal's override delegates to via
  `super()` after calling `finalize_certificate()` — builds its tracked solver from the four
  component lists directly and **never reads `all_constraints`, for any theory**. No reader of
  `all_constraints` can change what Z3 is asked to solve. This must be stated explicitly in the
  landed code and docs (Phase 6) so a future reader does not over-read the severity.
- **F3 (reader 1 severity resolved empirically)**: `iterate/models.py:93`/`:152` is **unreachable
  for bimodal today** — a live, non-mocked `iterate: 3` run had every rebuilt model pass the
  independent S3 `recheck()` — but only because `theory_lib/bimodal/iterate.py`'s
  `_pin_theory_specific_values` already routes around `all_constraints` by appending pins into the
  live `semantics.frame_constraints`. That existing bypass is load-bearing and must not regress.
- **F4 (new, adjacent, explicitly OUT OF SCOPE)**: the generic `is_world`/`verify`/`falsify`
  pinning in `iterate/models.py` never reaches the rebuilt structure's real solve for
  logos/exclusion/imposition (no theory-specific override exists for them), so their rebuilt
  models are effectively unpinned. Same underlying mechanism ("a dead attribute treated as
  load-bearing"), different defect. This plan deliberately does **not** fix it; Phase 6 records it
  for a follow-up task.
- **F5/F6 (readers 2-4)**: `iterate/constraints.py:51-52` is dead (debug-log count only);
  `models/structure.py:429,435` and the fourth reader found by research,
  `theory_lib/bimodal/semantic/model.py:344,349` (`save_to`), are display-only. All four are fixed
  for free by the property, with zero call-site changes, because they only *read*.
- **F7**: `theory_lib/bimodal/tests/_pinned_eval.py`'s `full_constraints()` already implements the
  exact correct shape; the property is that helper promoted into production.

One addition this plan makes beyond the report, established by direct inspection of the call sites
during planning: **a read-only property does not make the `inject_z3_model_values` append sites
fail loudly.** `model_constraints.all_constraints.append(x)` on a property that returns a fresh
list succeeds and silently discards — strictly worse than today's behaviour. Only *assignment*
(`iterate/models.py:152`) raises `AttributeError`. The three append sites are therefore migrated
explicitly in Phase 3 rather than left to a hoped-for exception.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch; ROADMAP.md was not consulted.

## Goals & Non-Goals

**Goals**:

- Make `ModelConstraints.all_constraints` a read-only computed property so it always reflects the
  current `frame_constraints + model_constraints + premise_constraints + conclusion_constraints`.
- Leave behaviour bit-identical for the three single-phase theories (logos, exclusion,
  imposition), whose component lists do not mutate after `__init__`.
- Migrate the one production assignment (`iterate/models.py:152`) and the three
  `inject_z3_model_values` append sites deliberately, with an explicit comment at each naming why
  the write was removed.
- Fix the display/`--save` under-reporting for bimodal (`models/structure.py`'s
  `_get_relevant_constraints`, `bimodal/semantic/model.py`'s `save_to`) as a consequence of the
  property, without touching those readers.
- Verify against the full repository gate in CI's own two-invocation shape plus the bimodal suite
  explicitly, compared against a recorded pre-fix baseline.
- State explicitly, in the landed code/docs, that `_setup_solver` never read `all_constraints`, so
  the solve path was never implicated.

**Non-Goals**:

- **Fixing F4** (generic iterator pinning never reaching the rebuilt structure's real solve for
  logos/exclusion/imposition). It changes iteration *results* for three theories and needs its own
  reproduction and severity write-up. Phase 6 records it for a follow-up task; Phase 2 must leave
  the generic pinning loop and the `temp_solver`/`_pin_theory_specific_values` call shape untouched.
- Redesigning the `_pin_theory_specific_values` hook signature or removing `temp_solver` from
  `iterate/models.py`. After the assignment at :152 is removed, `temp_solver` becomes visibly
  write-only for the generic path, but the object is still passed to the hook whose bimodal
  override has a load-bearing side effect. It stays, with a comment.
- Reviving or repairing the dead `IteratorBuildExample.create_with_z3_model` path (confirmed zero
  production callers). Phase 3 migrates its append target only so it stops being a silent no-op.
- Narrowing, weakening, or deleting any existing assertion. Phase 3's injection-test edits
  redirect assertions to the new append target at identical strength and identical counts.
- Changing `full_constraints()`'s observable behaviour in the test tree (Phase 4 delegates it to
  the property, which returns the identical value).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A production or test site assigns to `all_constraints` and starts raising `AttributeError` | H | M | Phase 2 re-greps for every assignment before editing; research found exactly one production site (`iterate/models.py:152`), and every test-tree assignment is on a `Mock`/`MagicMock` (never a real `ModelConstraints`), which a property on the real class cannot affect. Phase 2's verification re-confirms this rather than trusting the count. |
| A `.append()` on the property silently no-ops instead of failing loudly | H | H (if unaddressed) | Phase 3 migrates all three `inject_z3_model_values` append sites; Phase 1 adds a unit test that pins this contract ("appending to the returned value does not change the property") so the behaviour is documented rather than latent. |
| Regressing bimodal's existing `_pin_theory_specific_values` bypass (F3), which is what makes reader 1 currently safe | H | L | Phase 2 touches only line 152 in `iterate/models.py` and nothing in `theory_lib/bimodal/iterate.py`; Phase 5 re-runs the bimodal suite, which carries the two-phase-specific regression coverage. |
| The A2-triangle per-candidate comparison (which depends on `full_constraints()`) regresses | H | L | Phase 4 delegates `full_constraints()` to the property only after proving the two return the same value, and runs the bimodal pinned-eval/A2-triangle tests in the same phase before proceeding. |
| Cross-theory behaviour change slips through a bimodal-only verification | H | M | Phase 5 runs CI's exact two-invocation gate over `tests/` and `src/model_checker`, not just the bimodal suite, and diffs against the Phase 1 baseline. |
| A future reader over-reads F4 as in-scope, or under-reads the display fix as a soundness fix | M | M | Phase 6 updates `A2_GAP.md` with both statements explicitly: `_setup_solver` never read `all_constraints` (so no soundness issue), and F4 is a separate live defect with its own follow-up. |
| Concurrent sibling tasks (197, 208) are dispatched against this same working tree with no declared `file_scope` | M | M | Re-read every file immediately before editing; stage only this task's own hunks with an explicit file list (never `git add -A`, a directory, or a glob); treat a build failure outside this plan's file list as possibly a sibling's in-flight edit and report rather than "fix" it. See `context/contracts/territory.md` (Cross-Task Territory). |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 3 and 4 touch disjoint files
(`theory_lib/*/semantic/core.py` + `*/tests/integration/test_injection.py` vs.
`theory_lib/bimodal/tests/_pinned_eval.py`).

---

### Phase 1: Baseline and failing tests (RED) [COMPLETED]

**Goal**: Record the pre-fix gate state, then add tests that fail for the right reason — the
property semantics and the bimodal certificate gap — before any production edit.

**Tasks**:

- [ ] Record the pre-fix baseline to `specs/207_fix_stale_all_constraints_snapshot/baselines/01_pre-fix-gate.md`:
      run CI's two invocations (see Phase 5 for the exact commands) plus
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -q`, and record
      pass/fail/skip counts and the name of every pre-existing failure. A pre-existing failure is
      a baseline fact, not something this task fixes — but it must be named, so Phase 5 can tell a
      regression from an inherited failure.
- [ ] Add to `code/src/model_checker/models/tests/unit/test_constraints.py` (alongside the existing
      real-instance assertion at :160-161, which must keep passing unchanged):
      - a test that mutating a component list after construction (e.g.
        `constraints.frame_constraints.append(z3.Bool('late'))`) is reflected in
        `constraints.all_constraints` — the live-view contract;
      - a test that `all_constraints` is recomputed rather than stored: appending to the value
        returned by the property does NOT change what the next read returns (pins the
        silent-no-op contract named in Research Integration);
      - a test that assigning to `all_constraints` raises `AttributeError` (fail-fast, per
        CLAUDE.md principle 3 and the no-backwards-compatibility rule — no setter is provided).
- [ ] Add a bimodal regression test asserting that after a real solve, `all_constraints` contains
      the certificate encoding — i.e. `len(structure.model_constraints.all_constraints)` equals
      `len(full_constraints(structure))` (import the helper from
      `theory_lib/bimodal/tests/_pinned_eval.py`) and is far larger than the pre-fix value. Place
      it with the existing bimodal integration coverage
      (`theory_lib/bimodal/tests/integration/`), reusing the `_real_build_example` construction
      pattern that `test_iterate.py` already uses — a real, non-mocked solve, not a mock.
- [ ] Run the new tests and confirm they FAIL for the intended reason (stale snapshot / assignment
      permitted), not for a setup error. Record the observed failure messages in the baseline file.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:

- `specs/207_fix_stale_all_constraints_snapshot/baselines/01_pre-fix-gate.md` - new; pre-fix gate
  counts, named pre-existing failures, and the RED failure messages
- `code/src/model_checker/models/tests/unit/test_constraints.py` - add three property-contract tests
- `code/src/model_checker/theory_lib/bimodal/tests/integration/` - add the post-solve
  certificate-coverage regression test (new file, or an added test in an existing module — the
  implementer picks based on what is already there)

**Verification**:

- The three new `models` unit tests fail on the current eager snapshot (the live-view and
  assignment-raises tests fail; note which, if any, already pass — the recompute test may pass
  vacuously today and that is expected).
- The new bimodal test fails with a concrete count mismatch (research measured 2 vs. 132 for the
  non-iterated `BM_CM_1` case).
- No production file has been modified in this phase.

---

### Phase 2: Convert `all_constraints` to a read-only property; migrate the production write site [COMPLETED]

**Goal**: Replace the eager concatenation with a computed property, and remove the one production
assignment, leaving bimodal's existing pin bypass and the generic pinning loop untouched.

**Tasks**:

- [ ] Re-grep for every assignment to `all_constraints` across `code/` before editing
      (`grep -rn "all_constraints *=" code/src`), and confirm each hit is either the definition
      being replaced or a `Mock`/`MagicMock` attribute in the test tree. Record the confirmed list.
- [ ] In `code/src/model_checker/models/constraints.py`: delete the `self.all_constraints = (...)`
      assignment at the end of `__init__` (currently line 97) and add a read-only property:
      ```python
      @property
      def all_constraints(self) -> List["ExprRef"]:
          """Live view of every constraint this ModelConstraints currently carries."""
          return (
              self.frame_constraints + self.model_constraints
              + self.premise_constraints + self.conclusion_constraints
          )
      ```
      The docstring must state: (a) it is recomputed per access, so `frame_constraints` growth
      after construction (bimodal's two-phase `finalize_certificate()`, decision D6) is picked up;
      (b) it is read-only on purpose — assignment raises, and appending to the returned list is a
      no-op, so callers must append into the component list they mean; (c) `_setup_solver` never
      reads this attribute, so it is diagnostic/derivative, never solve-determining.
- [ ] In `code/src/model_checker/iterate/models.py`: remove the assignment at line 152
      (`model_constraints.all_constraints = list(temp_solver.assertions())`) and replace it with a
      comment recording precisely why: the attribute is now a computed view, and per the audit
      nothing downstream ever read the value written here (`_setup_solver` reads the four live
      component lists). The comment must also note that the generic pins accumulated in
      `temp_solver` above are consequently discarded for theories without a
      `_pin_theory_specific_values` override — a pre-existing, separate live defect (F4) tracked
      by its own follow-up task, deliberately NOT fixed here.
- [ ] Leave `iterate/models.py:93` (the read), the generic `is_world`/`possible`/`verify`/`falsify`
      pinning loop, the `temp_solver` construction, and the
      `self.iterator._pin_theory_specific_values(temp_solver, z3_model, model_constraints)` call
      exactly as they are. The hook's bimodal override has a load-bearing
      `semantics.frame_constraints.append(...)` side effect (F3) that must keep running.
- [ ] Do not add a setter, and do not add a compatibility shim (CLAUDE.md: no backwards
      compatibility, fail fast).

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase assumes there is **exactly one** production assignment to
`all_constraints` (`iterate/models.py:152`) and that **every** test-tree assignment targets a
`Mock`/`MagicMock` rather than a real `ModelConstraints` instance. Confirm at implementation time
with the re-grep in the first task above plus `grep -rn "all_constraints" code/src --include=*.py`,
checking each test hit's receiver; if any real-instance assignment exists, stop and extend this
phase's file list before editing.

**Files to modify**:

- `code/src/model_checker/models/constraints.py` - remove the eager assignment; add the read-only
  `all_constraints` property with the three-point docstring
- `code/src/model_checker/iterate/models.py` - remove the line-152 assignment; add the explanatory
  comment including the F4 pointer

**Verification**:

- Phase 1's three `models` unit tests now pass:
  `PYTHONPATH=code/src pytest code/src/model_checker/models/tests/unit/test_constraints.py -q`
- Phase 1's bimodal certificate-coverage test now passes.
- `PYTHONPATH=code/src pytest code/src/model_checker/models/ code/src/model_checker/iterate/ -q`
  is green (no `AttributeError` from a missed assignment).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -q` is green — bimodal's
  pin bypass still works.
- Spot-check the display fix by hand on one bimodal example with constraint printing enabled
  (`cd code && ./dev_cli.py` against a bimodal example with `print_constraints`, or the
  equivalent `--save` path): the printed set now includes the (C1)-(C4) certificate constraints
  instead of the near-empty snapshot.

---

### Phase 3: Migrate the three `inject_z3_model_values` append sites [COMPLETED]

**Goal**: Stop the three theory cores appending into a value nothing retains, so the dead
injection path is at least internally coherent under the new property, and redirect its tests to
the new target at identical strength.

**Tasks**:

- [ ] Re-read each site immediately before editing (sibling tasks share this tree):
      `theory_lib/logos/semantic/core.py` (`inject_z3_model_values`, ~lines 455-491),
      `theory_lib/exclusion/semantic/core.py` (~lines 533-570),
      `theory_lib/bimodal/semantic/core.py` (~lines 443-451).
- [ ] In each, change every `model_constraints.all_constraints.append(x)` to append into a live
      component list instead. Use `model_constraints.model_constraints.append(x)` — these are
      pinned model-content literals, and that list is owned by `ModelConstraints` itself rather
      than aliased to `semantics.frame_constraints`, so injection does not mutate semantics state.
      Add a short comment at the first site in each file noting that the doubled attribute name
      (`model_constraints.model_constraints`) is the ModelConstraints-owned model-constraint group,
      and that appending to `all_constraints` is now a silent no-op because it is a computed view.
- [ ] Do **not** switch these sites to `frame_constraints`: bimodal's `iterate.py` uses
      `frame_constraints` for certificate pins by design, and this path is unrelated to that one.
      Keep the two patterns distinct and commented.
- [ ] Update the injection tests to read the new target, keeping every assertion's count and
      structural check identical (redirect only, never weaken):
      `theory_lib/logos/tests/integration/test_injection.py` (setUp :25 and reads at :51, :82,
      :137, :159), `theory_lib/exclusion/tests/integration/test_injection.py` (:24, :50, :83,
      :112, :139, :153), `theory_lib/bimodal/tests/integration/test_injection.py` (:63, :69, :91,
      :97), `theory_lib/imposition/tests/integration/test_injection.py` (:23, :46 — imposition has
      no own `inject_z3_model_values` and exercises the inherited logos implementation).
- [ ] Also seed the `Mock`'s other component lists where a test's mock previously only carried
      `all_constraints`, so the mock keeps matching the real attribute surface.
- [ ] Leave `models/constraints.py`'s `inject_z3_values` delegation hook and
      `iterate/build_example.py`'s `create_with_z3_model` factory unchanged — the path remains dead
      (zero production callers); this phase only stops it from being silently broken.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **three** production append sites (logos, exclusion,
bimodal `semantic/core.py`) and **four** affected test files (those three theories plus
imposition). Confirm at implementation time with
`grep -rn "all_constraints.append" code/src --include=*.py` (expect zero hits afterwards) and
`grep -rln "all_constraints" code/src/model_checker/theory_lib/*/tests/integration/test_injection.py`;
if the counts differ, extend the file list before editing rather than skipping a site.

**Files to modify**:

- `code/src/model_checker/theory_lib/logos/semantic/core.py` - append into `model_constraints`
- `code/src/model_checker/theory_lib/exclusion/semantic/core.py` - append into `model_constraints`
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - append into `model_constraints`
- `code/src/model_checker/theory_lib/logos/tests/integration/test_injection.py` - redirect reads
- `code/src/model_checker/theory_lib/exclusion/tests/integration/test_injection.py` - redirect reads
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` - redirect reads
- `code/src/model_checker/theory_lib/imposition/tests/integration/test_injection.py` - redirect reads

**Verification**:

- `grep -rn "all_constraints.append" code/src --include=*.py` returns nothing.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/*/tests/integration/test_injection.py code/src/model_checker/models/tests/integration/test_constraints_injection.py -q`
  is green, with the same number of assertions as before (diff the test files to confirm only the
  attribute name changed, no assertion was relaxed or removed).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -q` is green.

---

### Phase 4: Delegate the test tree's `full_constraints()` to the property [COMPLETED]

**Goal**: Remove the divergence risk between the production property and the test helper without
changing the helper's observable behaviour, keeping the A2-triangle per-candidate comparison green.

**Tasks**:

- [ ] Re-read `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py`'s
      `full_constraints()` (~lines 391-411) and the note in
      `theory_lib/bimodal/tests/unit/test_pinned_eval.py:264` that points at its docstring.
- [ ] Prove equivalence before changing anything: assert in a scratch run (or a temporary
      assertion) that `full_constraints(structure)` and
      `list(structure.model_constraints.all_constraints)` are element-for-element equal on a real
      bimodal solve. Only proceed if they match.
- [ ] Replace `full_constraints()`'s body with a delegation to the property
      (`return list(structure.model_constraints.all_constraints)`), and rewrite its docstring:
      the production attribute has caught up, so this helper now exists as a named alias for
      callers rather than a workaround. Keep the historical explanation of why the workaround was
      needed, marked as history, so the A2-triangle reader still has the context.
- [ ] Update the pointer at `theory_lib/bimodal/tests/unit/test_pinned_eval.py:264` if its wording
      now misdescribes the helper. Do not change what that test asserts.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` - delegate `full_constraints()`
  to the property; rewrite the docstring (historical note retained)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` - comment/pointer
  wording only, if stale

**Verification**:

- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` is green,
  including every A2-triangle / pinned-eval test that consumes `full_constraints()`.
- `git diff` on the two files shows no assertion changed — only the helper body, docstrings, and
  comments.

---

### Phase 5: Full repository gate under CI's own invocation shape [COMPLETED]

**Goal**: Prove the change is cross-theory safe by running the gate CI runs, and compare to the
Phase 1 baseline rather than to an assumption.

**Tasks**:

- [ ] Run CI's exact two invocations from `.github/workflows/tests.yml`:
      ```
      cd code
      PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread
      PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread
      ```
      Background each run and wait with a bounded waiter (hard timeout, writer liveness via
      `kill -0` on the captured PID) per `context/patterns/bounded-build-waiter.md`.
- [ ] Run the bimodal suite explicitly:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v`. Per
      `code/docs/core/TESTING_GUIDE.md` section 8.14 the earlier blanket `development`-marker
      exclusion for bimodal is retired, so bimodal gates like any other theory and is not
      advisory-only here.
- [ ] Diff every result against `baselines/01_pre-fix-gate.md`. Any failure not named in the
      baseline is a regression from this task and must be fixed inside this task, not deferred.
      Any failure named in the baseline stays out of scope and is restated in the summary.
- [ ] Append the post-fix counts to the baseline file (or write
      `baselines/02_post-fix-gate.md`) so the comparison is recorded, not just observed.
- [ ] If a failure appears in a file outside this plan's file list, check `git log` and
      `git status` before assuming ownership — sibling tasks 197 and 208 share this working tree.
      Report a foreign change rather than "fixing" it.

**Timing**: 0.75 hours (mostly wall-clock waiting)

**Depends on**: 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:

- `specs/207_fix_stale_all_constraints_snapshot/baselines/01_pre-fix-gate.md` (or a new
  `02_post-fix-gate.md`) - post-fix counts and the baseline diff

**Verification**:

- Both CI invocations complete and show no failure absent from the Phase 1 baseline.
- The bimodal suite is green.
- The recorded diff explicitly enumerates any inherited (pre-existing) failure carried forward.

---

### Phase 6: Documentation and follow-up record [NOT STARTED]

**Goal**: Record the corrected severity precisely where a future reader will look, and hand F4 off
rather than losing it.

**Tasks**:

- [ ] Update `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` (around its existing
      `all_constraints` note at :188): state that `all_constraints` is now a computed view rather
      than a construction-time snapshot; state explicitly that `models/structure.py`'s
      `_setup_solver` never read `all_constraints` for any theory, so the solve path was never
      implicated and this was a diagnostic/display defect, not a soundness defect; and note that
      the verbose "SATISFIABLE CONSTRAINTS:" display and bimodal's `--save` output now report the
      full certificate encoding.
- [ ] Check `docs/architecture/MODELS.md` and `docs/architecture/SEMANTICS.md` for any prose
      describing `all_constraints` as a stored list built in `__init__`, and correct it if present.
      (`docs/architecture/MODELS.md:1300` is an unrelated local variable in an example — leave it.)
      Skip any file where no such claim is actually made rather than editing for its own sake.
- [ ] Record the F4 follow-up recommendation in the implementation summary with enough detail for
      `/task` to create it from: generic `is_world`/`verify`/`falsify` pinning in
      `iterate/models.py` never reaches the rebuilt structure's real solve for
      logos/exclusion/imposition; research evidence is in
      `reports/01_fix-stale-all-constraints.md` F4 (live logos probe: rebuilt model 2's
      `is_world` signature is an independent unpinned resolve, and `iterate/core.py`'s loop has no
      consistency check that would catch a divergent rebuild). Do not create the task from inside
      this phase — surface it for the user.
- [ ] Do not reference task numbers in any file outside `specs/**`
      (`.claude/rules/no-task-references-in-deliverables.md`); cite durable anchors (file names,
      the F-numbers, section headings) in `A2_GAP.md` and code comments instead.

**Timing**: 0.5 hours

**Depends on**: 5

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - corrected `all_constraints` note
  with the explicit non-soundness statement
- `docs/architecture/MODELS.md`, `docs/architecture/SEMANTICS.md` - only if they assert the stale
  snapshot shape

**Verification**:

- Diff read-through confirms every changed hunk is prose/comment with no compile surface.
- `bash .claude/scripts/check-task-references.sh` (or the equivalent repo lint) reports no new
  task-number reference outside `specs/**`.
- The summary contains the F4 follow-up record with its evidence pointer.

---

## Testing & Validation

- [ ] New `models` unit tests: live-view behaviour, recompute-not-stored behaviour, assignment
      raises `AttributeError`.
- [ ] Existing real-instance assertion `models/tests/unit/test_constraints.py:160-161`
      (`len(all_constraints) == 5`) still passes unchanged.
- [ ] New bimodal post-solve test: `all_constraints` length equals `full_constraints()` length
      (certificate encoding present).
- [ ] All four `test_injection.py` files green with assertions redirected, not weakened.
- [ ] Bimodal A2-triangle / pinned-eval tests green after `full_constraints()` delegation.
- [ ] CI's two-invocation gate over `tests/` and `src/model_checker` green relative to baseline.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v` green.
- [ ] `grep -rn "all_constraints.append\|all_constraints *=" code/src --include=*.py` shows no
      production write site (test-tree `Mock` assignments excepted).

## Artifacts & Outputs

- `specs/207_fix_stale_all_constraints_snapshot/baselines/01_pre-fix-gate.md` - pre-fix gate
  baseline with named pre-existing failures and the RED failure messages
- `specs/207_fix_stale_all_constraints_snapshot/baselines/02_post-fix-gate.md` (or an appended
  section in `01_`) - post-fix counts and baseline diff
- `specs/207_fix_stale_all_constraints_snapshot/summaries/01_fix-stale-all-constraints-summary.md`
  - implementation summary, including the F4 follow-up record
- Production changes: `models/constraints.py`, `iterate/models.py`, and the three
  `theory_lib/{logos,exclusion,bimodal}/semantic/core.py` injection sites
- Test changes: `models/tests/unit/test_constraints.py`, a new bimodal integration test, the four
  `test_injection.py` files, `bimodal/tests/_pinned_eval.py`
- Doc changes: `theory_lib/bimodal/docs/A2_GAP.md` (plus architecture docs if they assert the stale
  shape)

## Rollback/Contingency

- Each phase commits on its own green sub-steps, so reverting is `git revert` of that phase's
  commits — preferred over any working-tree discard.
- If Phase 2 reveals a real-instance assignment the Scope Hypothesis did not anticipate, stop
  before editing and extend the phase's file list; do not add a property setter to paper over it
  (that would reintroduce the snapshot semantics under a new name).
- If Phase 5 shows a cross-theory regression that cannot be resolved inside this task, revert the
  Phase 2 and Phase 3 commits, leave Phase 1's tests in place marked as expected-fail with a
  reason naming the blocker, and mark the task `[BLOCKED]` with the failing case recorded in the
  baselines directory.
- If an intentional whole-tree rollback of uncommitted work becomes necessary, follow
  `context/contracts/recovery.md`'s rollback rung for the exact snapshot-then-rollback invocation
  shape (including its out-of-scope override flag) rather than running a bare destructive git
  command.
