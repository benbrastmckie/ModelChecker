# Implementation Plan: Task #188

- **Task**: 188 - Diagnose BM_CM_4 deterministic countermodel failure
- **Status**: [NOT STARTED]
- **Effort**: 8 hours (core path, Phases 1-6); +2 hours if the Phase 7 contingency fires
- **Dependencies**: None
- **Research Inputs**: specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/reports/01_bm-cm-4-cost-regression.md
- **Artifacts**: plans/01_bm-cm-4-symbol-rename-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Research settled the diagnosis as case (a): BM_CM_4's countermodel is still reachable and
still returns the expected `match` verdict, but commit `f9cc081e`'s Skolemized
Seriality+Interpolation axioms push Z3's MBQI search past the 120s budget, deterministically.
Research also produced a candidate genuine fix (Acceptable Outcome 1): an alpha-rename of the
Z3 symbol identifiers inside `build_seriality_constraint` and `build_interpolation_constraint`
recovers a decided `match` in ~2s, reproduced 3/3 and stable across all three bound-var-counter
states the isolation test parametrizes. This plan takes that candidate through the evidentiary
bar the task description sets before it may be called a fix: a >= 20-seed sweep with no
undecided draw, plus a full 52-example regression diff that no other example regresses, plus
the currently-gating oracle bimodal suite. Only then does the rename land as the remedy and the
stale comments get corrected. If either gate fails, Phase 7 reverts the rename and converts the
evidence into an `UNSTABLE_EXAMPLES` entry meeting all four TESTING_GUIDE 8.9 criteria
(Acceptable Outcome 3). `max_time` is not raised on any branch.

### Research Integration

Findings carried directly into the phases below:

- **Diagnosis (a), not (b) or (c)** (report SS1-SS3, SS6). No bisection phase is needed: task 153
  already bisected this to `f9cc081e` and the report independently reproduced both the current
  failure (`inconclusive`, 40.205s at a 40s probe budget) and task 153's pre-change reference.
  ADEQUACY.md's unsoundness caveat is not implicated because every decided draw returns the
  expected `match`, never a flipped verdict.
- **The rename experiment** (report SS5) is the seed of Phase 2/Phase 3. Renaming *either* axiom's
  symbols alone is independently sufficient, so the fix is not a name-collision repair but a
  mitigation of Z3 quantifier-instantiation sensitivity to incidental symbol identity -- which
  Phase 3 must record honestly at the rename site rather than oversell.
- **Evidence gaps the report itself flags**: only 5 probe runs, no full 52-example regression,
  no >= 20-seed sweep. Phases 2 and 4 exist solely to close those gaps before landing.
- **The theory-wide `development` blanket** (bimodal/tests/conftest.py) keeps this failure off
  gating CI but does not substitute for 8.9's per-example bookkeeping. The oracle tree
  (`oracle/bimodal_logic/tests/`) deliberately does NOT register `development`, so its BM_CM_4
  assertions are gating and must be verified in Phase 5.
- **Stale text inventory** (report SS7) drives Phase 6.

### Prior Plan Reference

No prior plan. This is round 01 for the task.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch's delegation context and `roadmap_flag` is
absent, so `specs/ROADMAP.md` was not consulted and no roadmap phases are added.

## Goals & Non-Goals

**Goals**:
- Land a genuine, evidenced remedy for BM_CM_4's deterministic failure that does not raise
  `max_time`.
- Meet the task description's own evidentiary bar for Acceptable Outcome 1: >= 20-seed sweep
  with no undecided draw, plus no regression elsewhere in the 52-example set.
- Leave behind a rerunnable harness under this task's `baselines/` so the measurement can be
  reproduced rather than re-derived.
- Correct every stale claim identified in report SS7, preserving the history rather than deleting
  it (TESTING_GUIDE 8.9's promotion-path convention).

**Non-Goals**:
- Replacing the window-and-abundance encoding with the witness-family certificate design. That
  is the separate certificate-redesign track; if the evidence lands there, Phase 7 hands it over
  rather than attempting it.
- Re-litigating BM_CM_1, which is already a properly-recorded `UNSTABLE_EXAMPLES` entry.
- Raising `max_time` on BM_CM_4 or any other example as a remedy.
- Changing BM_CM_4's `expectation` (Acceptable Outcome 2): every decided draw confirms
  `expectation: True`, so there is no evidence to justify it.
- Removing or narrowing the theory-wide `development` blanket in bimodal/tests/conftest.py.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The rename is an empirical mitigation of a Z3 heuristic, not a structural fix; a future axiom/ordering change could re-trigger the pathology | M | M | Phase 3 documents it as such at the rename site; Phase 1's harness is left rerunnable as the standing regression probe |
| The rename silently regresses another example (notably BM_TH_3/BM_TH_4, tuned against the Skolemized-vs-nested-Exists choice) | H | M | Phase 4's full 52-example diff against the Phase 1 pre-change baseline is a hard gate before Phase 6 |
| The >= 20-seed sweep surfaces undecided draws the 5-run probe missed | M | M | Phase 2 runs the sweep BEFORE editing `core.py`; a failed sweep routes to Phase 7 with no source change to revert |
| Long solver runs distort each other's timings via CPU contention | M | H | Phases 4 and 5 are deliberately serialized (not same-wave), and the harness runs single-process; oracle's own `xdist_serial` marks on BM_CM_4 are respected |
| Oracle bimodal tests (gating, no `development` blanket) behave differently from the `code/` tree | M | L | Phase 5 runs `oracle/bimodal_logic/tests/` explicitly rather than inferring from the `code/` suite |
| Scope creep into the certificate redesign | H | L | Explicit Non-Goal; Phase 7 hands over with evidence instead of attempting it |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 (conditional) | 2, 4 |

Phases within the same wave can execute in parallel. Every wave here holds exactly one phase:
the measurement phases must not contend for CPU with each other, since the quantity being
measured is solve wall time. Phase 7 is conditional and executes only on the trigger stated in
its Goal.

### Phase 1: Rerunnable Harness and Pre-Change Baseline [NOT STARTED]

**Goal**: Stand up a rerunnable, seed-pinnable measurement harness under this task's
`baselines/` directory, and capture the current (unmodified-tree) verdicts for all bimodal
examples so Phase 4 has a same-host "before" reference.

**Tasks**:
- [ ] Create `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/`.
- [ ] Adapt `specs/archive/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_frame-axiom-regression-script.py`
      into `01_symbol-rename-harness.py`. Keep its structure: `sys.path.insert` to `code/src`,
      `isolated_z3_context()` per example, `run_enhanced_test`, incremental JSON writes, and
      monkeypatch-with-restore in a `finally`.
- [ ] Give the harness three arms: `baseline` (unmodified on-disk methods), `renamed` (both
      axioms' Z3 symbols alpha-renamed), and `renamed_single` (one axiom only, selectable) --
      the last preserves the report's SS5 single-axiom finding as a rerunnable check.
- [ ] Add a seed-pinning option (`z3.set_param` on `smt.random_seed` / `sat.random_seed`,
      matching the convention BM_CM_1_settings and BM_CM_4_settings already cite) and a
      probe-budget override so sweeps can cap at 40s instead of 120s.
- [ ] Add a bound-var-counter poisoning option (set `bimodal.operators._bound_var_counter` to a
      given `itertools.count(k)` start) so the isolation test's [0, 17, 30] states are
      reproducible from the harness.
- [ ] Run the `baseline` arm over all bimodal examples, writing
      `baselines/01_pre-change-verdicts.json`.
- [ ] Confirm the harness reproduces the known failure: BM_CM_4 `baseline` is
      `inconclusive`/`timeout` and BM_CM_1 is whatever it is today (recorded, not asserted --
      BM_CM_1 is out of scope).

**Timing**: 2 hours (including the baseline solver run)

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the bimodal example set is 52 examples (13 countermodel + 39 theorem,
measured at planning time via `countermodel_examples`/`theorem_examples`). The implementer must
confirm the count the harness actually enumerates and record the real number in the JSON rather
than assuming 52; a divergence means examples were added or removed since planning and the
Phase 4 diff must be read against the actual set.

**Files to modify**:
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/01_symbol-rename-harness.py` - new; adapted from task 153's harness
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/01_pre-change-verdicts.json` - new; harness output

**Verification**:
- The harness runs end to end and writes a JSON entry for every enumerated example.
- BM_CM_4's `baseline` entry shows `check_result: "inconclusive"`, `model_found: false`,
  `timeout: true` -- i.e. the harness reproduces the failure this task exists to fix.
- No file under `code/` or `oracle/` is modified by this phase (`git status --short` shows only
  the new `specs/188_.../baselines/` files).

---

### Phase 2: Twenty-Plus-Seed Sweep of the Renamed Construction [NOT STARTED]

**Goal**: Decide, before touching any source file, whether the renamed construction clears the
task description's bar for Acceptable Outcome 1 -- BM_CM_4 green across a >= 20-seed sweep with
no undecided draw.

**Tasks**:
- [ ] Run BM_CM_4 through the harness's `renamed` arm across >= 20 distinct pinned seeds at a
      capped probe budget (40s, deliberately below the 120s example budget so that a decided
      draw is decided with margin, not scraping the ceiling).
- [ ] Run the same >= 20-seed sweep against the `baseline` arm at the same capped budget as the
      control, so the comparison is same-host and same-budget rather than against the report's
      earlier numbers.
- [ ] Additionally run the `renamed` arm at the three bound-var-counter states [0, 17, 30] the
      isolation test parametrizes, confirming the report's SS5 result.
- [ ] Write `baselines/02_seed-sweep.json` with per-seed `check_result`, `model_found`,
      `timeout`, and `solving_time`, plus a short `baselines/02_seed-sweep.md` recording the
      seed list, the budget, the host, and the summary statistics (min/median/max decided time,
      count of undecided draws).
- [ ] **Decision gate**: if any seed produces an undecided draw, or any decided draw returns
      something other than `match`/`model_found: true`, STOP and route to Phase 7. Do not
      proceed to Phase 3.

**Timing**: 1.5 hours (worst case ~20 x 40s per arm plus overhead)

**Depends on**: 2 depends on 1

**Verification Tier**: local

**Scope Hypothesis**: >= 20 seeds at a 40s cap is asserted to complete in roughly 1.5 hours on
the strength of the report's ~2s decided-draw measurement. If undecided draws dominate, each
costs the full 40s and the phase runs long; the implementer should confirm the per-seed cost on
the first three seeds and, if the sweep is trending toward all-undecided, stop early -- that is
already the decision gate's negative answer and does not need 20 confirmations.

**Files to modify**:
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/02_seed-sweep.json` - new; raw per-seed results
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/02_seed-sweep.md` - new; summary and gate verdict

**Verification**:
- >= 20 distinct seeds recorded for the `renamed` arm, each with an explicit verdict.
- Zero undecided draws in the `renamed` arm, and every decided draw is `match` with
  `model_found: true` -- OR the gate is recorded as failed and Phase 7 is entered.
- The `baseline` control arm at the same budget shows the contrast (expected: undecided), so
  the sweep is evidence about the rename and not about the host.
- Still no modification under `code/` or `oracle/`.

---

### Phase 3: Land the Alpha-Rename in core.py [NOT STARTED]

**Goal**: Apply the alpha-rename to `build_seriality_constraint` and
`build_interpolation_constraint`, with the rationale recorded at the site, and confirm the
previously-failing bimodal tests go green.

**Tasks**:
- [ ] Edit `build_seriality_constraint` (`semantic/core.py:396-444`): rename the Skolem function
      identifiers (`serial_succ`, `serial_pred`) and the bound-variable names (`serial_w`,
      `serial_x`) to collision-free alternatives. Change nothing else -- same sorts, same
      arities, same `ForAll`/`Implies`/`And` structure, same guard.
- [ ] Edit `build_interpolation_constraint` (`semantic/core.py:446-501`): same treatment for
      `interp_witness`, `interp_w`, `interp_v`, `interp_d1`, `interp_d2`.
- [ ] Extend both docstrings with a short, dated paragraph recording: that the identifiers are
      load-bearing for solve cost but carry no semantic content; that the previous identifiers
      drove BM_CM_4 from a 4.07s decided `match` to a 120s+ `inconclusive` after `f9cc081e`;
      that the rename is an empirically-motivated mitigation of Z3 MBQI/E-matching sensitivity,
      NOT a principled encoding correction; that a future change in this area could in principle
      re-trigger the pathology; and that `specs/188_.../baselines/01_symbol-rename-harness.py`
      is the rerunnable probe.
- [ ] Run the four previously-failing BM_CM_4 node IDs:
      `tests/unit/test_bimodal.py::test_example_cases[BM_CM_4-example_case9]` and
      `tests/unit/test_bound_var_counter_isolation.py::TestBoundVarCounterOrderIndependence::test_bm_cm_4_independent_of_prior_counter_state[0|17|30]`.
- [ ] Commit this phase separately from the measurement phases, so a Phase 4 regression can be
      reverted as one atomic unit.

**Timing**: 1 hour

**Depends on**: 3 depends on 2

**Verification Tier**: interface

**Scope Hypothesis**: exactly two methods in one file
(`code/src/model_checker/theory_lib/bimodal/semantic/core.py`) carry the identifiers being
renamed. Before editing, confirm with
`grep -rn "serial_succ\|serial_pred\|serial_w\|serial_x\|interp_witness\|interp_w\|interp_v\|interp_d1\|interp_d2" code/ oracle/`
that no other production site references these Z3 symbol names by string (the task 153 archive
harness does, but it is an archived scratch artifact and must NOT be edited).

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - alpha-rename the Z3 symbol identifiers in `build_seriality_constraint` and `build_interpolation_constraint`; extend both docstrings with the rationale

**Verification**:
- The four previously-failing BM_CM_4 node IDs pass.
- The grep above confirms no other production reference to the old identifiers was left dangling.
- `git diff` on `core.py` shows identifier strings and docstring text only -- no change to any
  `z3.Function` signature, sort, arity, quantifier structure, or guard.
- TDD note: the RED tests already exist and already fail deterministically (seven consecutive
  pre-existing failures across two modules); no new test is written to manufacture a RED state.

---

### Phase 4: Full Example-Set Regression Diff [NOT STARTED]

**Goal**: Confirm that the landed rename changes no other example's verdict, by diffing a
post-change harness run against Phase 1's pre-change baseline.

**Tasks**:
- [ ] Run the harness's `baseline` arm again -- which now reads the *post-change* on-disk
      methods -- over the full example set, writing `baselines/03_post-change-verdicts.json`.
- [ ] Diff `03_post-change-verdicts.json` against `01_pre-change-verdicts.json` on
      `check_result`, `model_found`, and `timeout` for every example.
- [ ] Pay explicit attention to `BM_TH_3` and `BM_TH_4` at M=2 -- the examples the
      Skolemized-vs-nested-Exists choice was originally calibrated against, and therefore the
      most plausible collateral-damage sites.
- [ ] Record the diff in `baselines/03_regression-diff.md`: every example whose verdict moved,
      in which direction, with timings.
- [ ] **Decision gate**: the only acceptable verdict movement is BM_CM_4 going
      `inconclusive` -> `match`. Any other example moving from decided to undecided, or changing
      its `check_result`, fails the gate and routes to Phase 7. (BM_CM_1 is expected to remain
      undecided/unstable; that is not a regression and not this task's concern.)

**Timing**: 2 hours (solver-bound; the pre-change baseline run is the cost reference)

**Depends on**: 4 depends on 3

**Verification Tier**: full

**Scope Hypothesis**: the diff is asserted to touch exactly one example (BM_CM_4). The
implementer must confirm this against the actual diff output rather than spot-checking; a second
moved example is the gate failing, not a rounding error.

**Files to modify**:
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/03_post-change-verdicts.json` - new; post-rename harness output
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/03_regression-diff.md` - new; the pre/post diff and gate verdict

**Verification**:
- Every example in the pre-change baseline has a post-change counterpart (no silently dropped
  entries).
- Exactly one verdict moved, and it is BM_CM_4 `inconclusive` -> `match` -- or the gate is
  recorded as failed and Phase 7 is entered.
- `BM_TH_3` and `BM_TH_4` are individually named in the diff document with their before/after
  timings, whether or not they moved.

---

### Phase 5: Full Bimodal Suite and Gating Oracle Suite [NOT STARTED]

**Goal**: Confirm the change against the real pytest suites, including the oracle bimodal tree,
which is gating (it deliberately does not register the `development` marker) and carries its own
BM_CM_4 assertions.

**Tasks**:
- [ ] Run the full bimodal test tree:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.
      Compare against the dispatch's recorded pre-change figure (345 passed, 5 failed in 699s).
      Expect the four BM_CM_4 failures to be gone; BM_CM_1's single failure may remain (it is
      tracked `unstable` and out of scope).
- [ ] Run the oracle bimodal tree: `oracle/bimodal_logic/tests/`, including
      `test_boundary_regression.py::...::test_countermodel_bm_cm4_at_example_settings` and
      `test_regression_all_active_examples[BM_CM_4]`, honoring the `xdist_serial` marks those
      tests carry.
- [ ] Record both runs' pass/fail counts and wall times in
      `baselines/04_suite-verification.md`, alongside the pre-change reference figures.
- [ ] Do NOT run these concurrently with each other or with any other solver work -- the
      quantity under test is wall-clock solve cost.

**Timing**: 1.5 hours (mostly wall-clock waiting; ~700s for the bimodal tree alone)

**Depends on**: 5 depends on 4

**Verification Tier**: full

**Scope Hypothesis**: the pre-change bimodal-suite figure is 345 passed / 5 failed / 699s and
exactly four of those five failures are BM_CM_4. Confirm the post-change counts against the
actual run output; if a previously-passing test is now failing, that is a Phase 4-class
regression the diff missed and routes to Phase 7.

**Files to modify**:
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/04_suite-verification.md` - new; both suites' pre/post results

**Verification**:
- All four BM_CM_4 node IDs named in the task description pass.
- No test that passed pre-change now fails in either tree.
- The oracle bimodal tree passes, including both BM_CM_4 assertions.

---

### Phase 6: Correct the Stale Claims and Record the History [NOT STARTED]

**Goal**: Bring every stale comment identified in the research report into line with what is now
measured, preserving the history rather than deleting it.

**Tasks**:
- [ ] `code/src/model_checker/theory_lib/bimodal/examples.py`, `BM_CM_4_settings` (around lines
      426-446): replace the now-false sentence "The countermodel is still genuinely found on
      every probed seed" with an accurate, dated account -- the 2026-08-11 recalibration stands
      as history; `f9cc081e` then drove the example to a deterministic `inconclusive` at 120s;
      this task's rename recovered decided `match` draws, with the Phase 2 sweep's summary
      statistics cited. State explicitly that `max_time` was NOT raised as the remedy, and keep
      the sync note pointing at the oracle inline copy.
- [ ] Also correct the header comment above `BM_CM_4_premises` ("Previously timed out with Z3
      state issues; now finds countermodel with corrected semantics"), which carries the same
      stale framing.
- [ ] `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:69`: correct the
      NOTE "BM_CM_1, BM_CM_2, BM_CM_4 now reliably find countermodels with corrected semantics".
      BM_CM_2 is unaffected and the claim remains true for it; BM_CM_1 is tracked in
      `UNSTABLE_EXAMPLES`; BM_CM_4's real history is the `f9cc081e` regression and this task's
      rename. Cross-reference `BM_CM_4_settings` rather than restating the measurements.
- [ ] `oracle/bimodal_logic/tests/test_boundary_regression.py`: update the inline
      `BM_CM_4` comment copy (around lines 360-395 and 484-489) so the two sites stay in sync, as
      both comments already require of each other.
- [ ] `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py`
      module docstring: its seed history ("every other tested seed (0, 5, 10, 13, 15, 16, 18, 20,
      25, 30) passes") described a state that stopped holding under `f9cc081e` and holds again
      after the rename. Add a dated note recording that interval so a future reader who sees all
      three parametrized seeds fail again knows this is the second occurrence and where to look.
- [ ] Re-run the four BM_CM_4 node IDs after the edits (comment-only changes must not move any
      verdict; this is a cheap guard against an accidental code edit).

**Timing**: 1.5 hours

**Depends on**: 6 depends on 5

**Verification Tier**: prose

**Scope Hypothesis**: four comment sites are asserted to carry stale BM_CM_4 claims
(`examples.py` x2, `test_bimodal.py:69`, `oracle/.../test_boundary_regression.py`, plus the
isolation-test docstring note). Before editing, run
`grep -rn "BM_CM_4" code/ oracle/ --include=*.py` and confirm the full list; any additional site
making a reliability claim about BM_CM_4 must be corrected too.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - correct `BM_CM_4_settings`' comment and the example's header comment
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - correct the stale NOTE at line 69
- `oracle/bimodal_logic/tests/test_boundary_regression.py` - resync the inline BM_CM_4 comment copy
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py` - dated note on the seed history

**Verification**:
- No remaining occurrence of the sentence "The countermodel is still genuinely found on every
  probed seed" or of the unqualified "BM_CM_4 now reliably find countermodels" claim.
- Every corrected comment cites a concrete, dated measurement from this task's `baselines/`
  rather than a bare assertion.
- `git diff` on all four files shows comment/docstring lines only.
- The four BM_CM_4 node IDs still pass.

---

### Phase 7: CONDITIONAL -- Revert and Author an UNSTABLE_EXAMPLES Entry [NOT STARTED]

**Goal**: Executes ONLY if Phase 2's seed-sweep gate or Phase 4's regression gate fails. Falls
back to Acceptable Outcome 3: the rename is not landed (or is reverted), and BM_CM_4 gets an
`UNSTABLE_EXAMPLES` entry that genuinely satisfies all four TESTING_GUIDE 8.9 entry criteria.

**Tasks**:
- [ ] If Phase 3 already landed, revert the `core.py` rename commit so the tree carries the
      original, committed axioms.
- [ ] Add `"BM_CM_4"` to `UNSTABLE_EXAMPLES` in
      `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`, with a comment
      block following the BM_CM_1 entry's existing four-part structure:
      (1) **What fails and why** -- the `f9cc081e` Seriality+Interpolation cost regression, with
      task 153's isolation table (`neither` 3.10s < `seriality_only` 9.27s ~ `interpolation_only`
      6.33s < `both` undecided) and this task's own measured numbers.
      (2) **Demonstrably non-semantic** -- cite this task's decided draws under the renamed
      construction, every one of them returning the expected `match`; this is precisely the
      showing the task description said BM_CM_4 could not previously make, and it now can.
      (3) **Genuine fix attempted and its failure recorded** -- the alpha-rename, what the sweep
      or regression diff actually showed, and why it was not landed. Record `max_time` widening
      as explicitly ruled out.
      (4) **Exit criterion** -- verbatim and unambiguous, following 8.9's default: 20 consecutive
      unstable-watch runs with zero failures, OR a genuine encoding fix collapsing the tail
      across a >= 20-seed sweep with no undecided draw at `max_time = 120`.
- [ ] Extend `.github/scripts/unstable_watch_classify.py` with a BM_CM_4 signature branch,
      following the existing constant/branch pattern, and add its unit test in
      `code/tests/ci/test_unstable_watch_classifier.py` (TESTING_GUIDE 8.9: "Adding a third
      `unstable` marking means extending that module ... not editing workflow YAML").
- [ ] Still perform Phase 6's comment corrections -- they are required on every branch.
- [ ] If the evidence shows the failure is an artifact only the certificate redesign can fix,
      say so explicitly in the summary, record the evidence, and hand it over rather than
      attempting it.

**Timing**: 2 hours

**Depends on**: 7 depends on 2, 4 (fires on either gate's failure)

**Verification Tier**: interface

**Scope Hypothesis**: adding a third `unstable` marking is asserted to require touching
`test_bimodal.py`, `unstable_watch_classify.py`, and `test_unstable_watch_classifier.py`. Confirm
against TESTING_GUIDE 8.9's "Where the deselection is wired" paragraph and
`code/tests/ci/test_unstable_deselection_wiring.py` whether any additional accounting site names
the marked set by hand.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - add BM_CM_4 to `UNSTABLE_EXAMPLES` with the four-criteria comment block
- `.github/scripts/unstable_watch_classify.py` - BM_CM_4 signature branch
- `code/tests/ci/test_unstable_watch_classifier.py` - unit test for the new branch
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - reverted to its pre-Phase-3 state (if Phase 3 landed)

**Verification**:
- All four 8.9 entry criteria appear as separately identifiable items in the comment, each with
  concrete measurements (criterion 2 specifically backed by exhibited decided draws, not by
  assertion).
- The exit criterion is stated concretely enough that "has this been met?" has a yes/no answer.
- `code/tests/ci/test_unstable_watch_classifier.py` passes with the new branch.
- `git diff` on `core.py` is empty relative to the pre-task state.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest "code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_4-example_case9]" -v` passes.
- [ ] All three parametrized cases of
      `test_bound_var_counter_isolation.py::TestBoundVarCounterOrderIndependence::test_bm_cm_4_independent_of_prior_counter_state` pass.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` shows no
      failure that was passing before this task (BM_CM_1's known failure may persist).
- [ ] `oracle/bimodal_logic/tests/` passes, including both BM_CM_4 assertions in
      `test_boundary_regression.py`.
- [ ] The 52-example (or actual-count) regression diff shows exactly one moved verdict.
- [ ] The >= 20-seed sweep records zero undecided draws and zero non-`match` decided draws.
- [ ] No example's `max_time` value changed anywhere in the diff.
- [ ] No example's `expectation` value changed anywhere in the diff.

## Artifacts & Outputs

- `specs/188_.../baselines/01_symbol-rename-harness.py` - rerunnable, seed-pinnable measurement harness
- `specs/188_.../baselines/01_pre-change-verdicts.json` - pre-change verdicts for the full example set
- `specs/188_.../baselines/02_seed-sweep.json` and `02_seed-sweep.md` - the >= 20-seed sweep and its gate verdict
- `specs/188_.../baselines/03_post-change-verdicts.json` and `03_regression-diff.md` - post-change verdicts and the pre/post diff
- `specs/188_.../baselines/04_suite-verification.md` - both pytest suites' pre/post results
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (rename + rationale), `examples.py`, `tests/unit/test_bimodal.py`, `tests/unit/test_bound_var_counter_isolation.py`, `oracle/bimodal_logic/tests/test_boundary_regression.py` (comments)
- `specs/188_.../summaries/01_*-summary.md` - implementation summary (written by the implement phase)

## Rollback/Contingency

- **Phase-level rollback**: each phase is committed separately, and Phase 3 (the only phase that
  changes solver-visible behavior) is a single-file, identifier-only commit. Reverting that one
  commit restores the pre-task semantics exactly; the measurement artifacts under
  `specs/188_.../baselines/` are inert and can be kept.
- **Gate failure at Phase 2** (sweep shows undecided draws): nothing has been edited under
  `code/` yet. Go straight to Phase 7.
- **Gate failure at Phase 4 or 5** (another example regressed): revert the Phase 3 commit, record
  which example moved and by how much in `03_regression-diff.md`, then execute Phase 7 with that
  measurement as criterion 3's recorded fix-attempt failure.
- **If the rename proves to help BM_CM_4 but harm BM_TH_3/BM_TH_4**: do NOT attempt to tune a
  third identifier set to satisfy both. That is chasing a Z3 heuristic, and the task description
  explicitly forbids letting this task grow into the encoding replacement. Record the trade-off
  and hand it to the certificate-redesign track via Phase 7's final task.
- **Out of scope on every branch**: raising `max_time`, changing `expectation`, touching
  BM_CM_1's entry, and removing the theory-wide `development` blanket.
