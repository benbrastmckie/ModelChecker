# Implementation Plan: Task #176

- **Task**: 176 - fix_m3_shift_closure_sat_regression
- **Status**: [IMPLEMENTING]
- **Effort**: 6.5 hours (5.75 hours if Phase 6 is not entered)
- **Dependencies**: None
- **Research Inputs**: `specs/172_fix_contention_flaky_soundness_regression_tests/reports/02_spawn-analysis.md`
- **Artifacts**: plans/01_m3-shift-closure-sat-regression.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`
(`oracle/bimodal_logic/tests/test_soundness_regression.py:508`) fails deterministically at HEAD
with `structure.z3_model_status is False` for atom `p` at `N=2, M=3, temporal_depth=1,
max_time=15.0`. The plan first *classifies* the failure (genuine `unsat` vs. `unknown` vs.
mislabeled timeout) from the solver's own status, then attributes it to a concrete cause across
three independent axes (encoding drift in the bimodal semantic package, frame-axiom set growth,
and unpinned `z3-solver` version drift), then fixes the defect at the constraint/solver layer.
Marking the test `unstable` is a strictly-last-resort fallback gated on all four
TESTING_GUIDE.md section 8.9 entry criteria, entered only after a genuine fix attempt is recorded
as failed.

### Research Integration

The spawn analysis established the mechanism mismatch with task 172 (this test constructs
`BimodalStructure` directly and never touches `find_countermodel()`/`timeout_ms=5000`), the 2/2
deterministic reproduction, and the 2-8s-against-15s historical headroom that makes a budget
explanation implausible on its face. It named two open hypotheses — an incomplete revert of the
task-144 trigger/grounding experiments, and `z3-solver` version drift under `code/pyproject.toml`'s
unpinned `>=4.8.0` — and explicitly required both be answered with evidence rather than assumed.

**Planning-time finding not present in the research report (a third hypothesis, and a timeline
correction).** The spawn analysis ruled out same-window tree drift by checking tasks 152/158/175.
It did not check task 153. Commit `f9cc081e` ("task 153 phase 4: implement and wire Skolemized
Seriality/Interpolation", 2026-08-31 13:35) added two *new* frame axioms —
`build_seriality_constraint` and `build_interpolation_constraint` — wired into
`build_frame_constraints` immediately before `skolem_abundance`. Its own commit message records:
(a) a genuine cost regression on BM_CM_4 from "4.07s decided match" to "inconclusive at 120s
max_time", superlinear in the *combination* of the two axioms, with one pattern-based mitigation
already tried and failed; and (b) that it hit "a pre-existing MBQI pathology in
`capped_skolem_abundance_constraint`'s bare-satisfiability check at M=3, confirmed present
pre-Phase-4 too", worked around with `temporal_depth=0`. That second clause is an independent
observation of this task's exact symptom class.

Two consequences the plan must honor. **First, this is not the original cause**: task 172's 2/2
failing runs were recorded at commit `c8821e96` (2026-08-31 12:05) and the spawn landed at
`3224df24` (12:14), both *before* `f9cc081e` (13:35). Seriality/Interpolation cannot explain the
observed failures. **Second, it is now a live confound**: the failure at HEAD may have a different
or compounded character than the one observed pre-153, so Phase 1 must re-classify at HEAD rather
than inherit the pre-153 characterization, and Phase 4's attribution must be able to return a
two-cause verdict.

The `development` marker task 173 applied to the bimodal test tree does **not** cover `oracle/`
(verified: no `development` marker in `oracle/conftest.py` or `test_soundness_regression.py`), so
this test is still selected by `run-oracle-suite.sh` pass 1's
`-m "not xdist_serial and not slow and not unstable and not development"`. The test also carries no
`xdist_serial` marker of its own (task 172's `2aae7217` marked four other tests, not this one), so
it runs in the parallel `-n 6` pass.

### Prior Plan Reference

No prior plan for this task.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Classify the failure from the solver's own reported status: genuine `unsat`, `unknown` (with
  `reason_unknown`), or a budget overrun mislabeled as non-SAT.
- Attribute the regression to a concrete, evidenced cause across all three axes: bimodal semantic
  encoding drift since the post-task-114 baseline, the task-153 frame-axiom additions, and
  `z3-solver` version drift.
- Land a constraint/solver-layer fix that restores SAT at `M=3, temporal_depth=1, max_shift=1`
  with the test's existing assertions and existing 15.0s budget unchanged.
- If and only if no genuine fix is found, mark the test `unstable` with all four
  TESTING_GUIDE.md 8.9 entry criteria recorded as separately identifiable items at the marker site.
- Verify via a full `bash oracle/run-oracle-suite.sh` run reporting zero pass-1 failures.

**Non-Goals**:
- Changing `GATING_RECHECK_SOLVE_TIMEOUT_MS` or `MIN_CONCLUSIVE_GATING_FORMULAS`
  (`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`). Hard constraint.
- Widening the test's `max_time: 15.0` budget to force green. Historical measurement (2-8s against
  15s) shows budget was never the binding constraint; widening would only mask a genuine
  non-SAT result.
- Weakening, relaxing, or deleting any assertion in the test — including the
  `_check_shift_closure_bounded` violation assertion and the `not structure.timeout` conjunct.
- Reverting task 153's Seriality/Interpolation axioms. If Phase 4 finds they compound the failure,
  the finding is *recorded and escalated*; the axioms are in scope for this task's diagnosis but
  their removal is a user decision task 153 already deferred explicitly.
- Re-running task 172's verification or closing task 172. That is a separate follow-up
  (`/implement 172`) after this task lands.
- Fixing `test_oracle_provider.py::test_future_sat_returns_dict` (same-risk-class but never
  observed failing; the spawn analysis evaluated and declined it).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Failure is genuinely `unsat` — the M=3 depth-bounded encoding is over-constrained, meaning a real semantic defect, not a solver-heuristics issue | H | M | Phase 1 distinguishes `unsat` from `unknown` explicitly. An `unsat` verdict routes to a constraint-level fix (Phase 5) and forbids the `unstable` fallback entirely, since 8.9 criterion 2 (demonstrably non-semantic) cannot be met |
| Failure is `unknown`/MBQI-incompleteness — no clean encoding fix exists | M | M | Phase 5 budgets a real fix attempt across named avenues before Phase 6 is permitted; every rejected avenue is recorded so 8.9 criterion 3 is satisfiable honestly |
| Task-153 axioms compound the failure, entangling this task with a deferred user decision | M | M | Phase 4 tests `f9cc081e^` vs `f9cc081e` on the minimal repro and returns a two-cause verdict; the task-153 contribution is documented and escalated, never silently reverted |
| Z3 version sweep is confounded by the Nix devShell's pinned interpreter/package set | M | M | Phase 3 uses an isolated scratch venv with `--system-site-packages` disabled; if the sweep cannot be made clean, record that explicitly as an unresolved axis rather than reporting a false negative |
| Bisection over the candidate commit set fails because the package was renamed by task 126 (`semantic.py` -> `semantic/core.py`) | M | H | Phase 2/4 use `git show <sha>:<path-at-that-sha>` for pre-126 revisions rather than a path-stable diff; the exact old path is named in Phase 2 |
| The ~25-minute full-suite run is reaped by the harness as an ordinary background task | H | H | Phase 7 launches with `setsid nohup ... > log 2>&1 &` and polls the log; completion is judged from the script's own summary lines, never from PID liveness |
| Fix restores this test but regresses other depth-1/M=3 formulas sharing the abundance axiom (the exact failure mode of task 144 dead ends 7/8) | H | M | Phase 5's in-phase gate runs the full `test_soundness_regression.py` file, not the single test; Phase 7's full-suite run is the closing gate |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 5, 6 |
| 7 | 8 | 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Reproduce at HEAD and Classify the Solver Verdict [COMPLETED]

**Goal**: Establish, from the solver's own reported status at current HEAD, whether the failure is
a genuine `unsat`, an `unknown` (and with what `reason_unknown`), or a budget overrun — replacing
the research report's inference with a measurement. Produce a standalone minimal repro script that
every later phase reuses.

**Tasks**:
- [ ] Run the failing test in isolation and confirm it still fails at HEAD:
      `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py::TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 -x -v`
- [ ] Write a standalone repro script to
      `specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py` that constructs the same
      `BimodalSemantics`/`ModelConstraints`/`BimodalStructure` with the test's exact settings dict
      (`N=2, M=3, temporal_depth=1, contingent=False, disjoint=False, max_time=15.0,
      expectation=True, solver='z3'`) and prints, as one JSON line: `z3_model_status`,
      `structure.timeout`, the raw solver result (`sat`/`unsat`/`unknown`), `reason_unknown` where
      available, `solver.statistics()` (at minimum `rlimit-count` and `max-memory`), and wall-clock
      seconds. Exit code 0 on SAT, 1 otherwise, so the script is usable as a `git bisect run`
      predicate in Phase 4.
- [ ] Run the script 5 times and record the verdict distribution — this distinguishes a
      deterministic verdict from a heavy-tailed draw, which materially changes both the fix and the
      8.9 criterion-1 record.
- [ ] Read `BimodalStructure`'s solve path to confirm how `z3_model_status` and `timeout` are set
      from the underlying `z3.Solver.check()` result, so the repro's reported status is known to be
      the solver's and not a derived flag.
- [ ] Record the run under
      `specs/176_fix_m3_shift_closure_sat_regression/baselines/01_head-classification.json`.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the failure reproduces at HEAD with the same message the
research report recorded pre-153. Confirm by running the test at HEAD before writing the repro
script; if it now passes, or fails with a *different* message, stop and record that — the whole
attribution chain downstream changes.

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py` - new; minimal standalone
  reproduction and bisect predicate
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/01_head-classification.json` - new;
  recorded verdict, statistics, and 5-run distribution

**Verification**:
- `repro_m3.py` runs standalone under `PYTHONPATH=code/src` and prints a parseable JSON line
- The recorded verdict names one of `unsat` / `unknown` / `sat`, and `structure.timeout`'s actual
  boolean value is in the baseline file — the research report's central unanswered question
- The 5-run distribution is recorded (all-fail vs. mixed)

---

### Phase 2: Encoding-Drift Audit Against the Post-Task-114 Baseline [COMPLETED]

**Goal**: Determine whether the bimodal frame-constraint encoding reaching this test differs
semantically from the post-task-114 baseline that made it pass — covering both the claimed-clean
task-144 reverts and the task-153 frame-axiom additions.

**Tasks**:
- [ ] Extract the post-114 baseline source:
      `git show 12eb4ded:code/src/model_checker/theory_lib/bimodal/semantic.py` (note the pre-task-126
      path — task 126 phase 21, `a404edbd`, split this file into `semantic/core.py`, so a
      path-stable diff will not work).
- [ ] Diff, function by function, the current `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
      against that baseline for: `depth_bounded_skolem_abundance_constraint`,
      `capped_skolem_abundance_constraint`, `matching_states_when_shifted_var`,
      `world_interval_start`, `world_interval_end`, and the `skolem_abundance` dispatch block in
      `build_frame_constraints`. Confirm whether the task-144 reverts (`401bb58c`, `40ad9238`,
      `eb1639de`) left these functionally identical to the baseline, or only textually similar with
      added comments. Report the verdict per function, not in aggregate.
- [ ] Enumerate the *set* of constraints `build_frame_constraints` returns at HEAD vs. at
      `12eb4ded`, and identify every addition. Expected additions to confirm: `build_seriality_constraint`
      and `build_interpolation_constraint` (both from `f9cc081e`), plus anything from
      `71d437bd` (task 140, bimodal order-dependence root-cause fix).
- [ ] Extend `repro_m3.py` with an opt-in flag that prints the count and the top-level shape of each
      returned frame constraint, so the constraint-set delta is measured rather than read off the
      source.
- [ ] Record findings to
      `specs/176_fix_m3_shift_closure_sat_regression/baselines/02_encoding-drift.md`.

**Timing**: 1.0 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the candidate commit set touching the bimodal semantic
package since `12eb4ded` is exactly `{30f97c64, a404edbd, 71d437bd, 401bb58c, 40ad9238, eb1639de,
f9cc081e, a15a6dc7, 3555a864}`. Confirm at implementation time with
`git log --oneline 12eb4ded..HEAD -- code/src/model_checker/theory_lib/bimodal/semantic/` **plus**
the pre-rename path `code/src/model_checker/theory_lib/bimodal/semantic.py`, and additionally check
`code/src/model_checker/models/` and the solver-abstraction layer for changes reaching this path —
the list above is a hypothesis from planning-time inspection of one directory, not a proven closure.

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py` - add constraint-set dump flag
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/02_encoding-drift.md` - new; per-function
  drift verdict and the frame-constraint-set delta

**Verification**:
- A per-function verdict (identical / comment-only / semantically changed) exists for all six named
  functions
- The frame-constraint-set delta since `12eb4ded` is enumerated with the commit responsible for each
  addition
- The candidate commit set from the Scope Hypothesis is confirmed or corrected in writing

---

### Phase 3: Z3 Version Sweep [COMPLETED]

**Goal**: Answer whether `z3-solver` version drift — `code/pyproject.toml`'s `"z3-solver>=4.8.0"` has
no upper bound, and 4.16.0 is installed — flips this formula's verdict, an axis git bisection
cannot reach.

**Tasks**:
- [ ] Record the currently installed version and, if determinable, the version in use when task 114
      landed (2026-06-01) — check `code/pyproject.toml` history, any lockfile, `flake.nix`/Nix
      inputs, and task-114-era baseline artifacts under `specs/archive/114_skolem_abundance_overconstrain_fix/`.
- [ ] Create an isolated scratch venv (no `--system-site-packages`) under the scratchpad directory,
      install the repo's runtime deps, and run `repro_m3.py` under a ladder of `z3-solver` versions
      spanning the drift window (at minimum: the installed 4.16.0, one release near 2026-06-01, and
      2-3 intermediate releases). Bisect the ladder if a flip is found.
- [ ] For every version, record the verdict, `reason_unknown` where applicable, `rlimit-count`, and
      wall time — a version that still returns SAT but at 10x rlimit is a materially different
      finding from one that returns `unsat`.
- [ ] Record to `specs/176_fix_m3_shift_closure_sat_regression/baselines/03_z3-version-sweep.json`.

**Timing**: 1.0 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase assumes the repro runs cleanly in a venv outside the Nix devShell.
Confirm by running `repro_m3.py` in the fresh venv at the *already-installed* 4.16.0 first and
checking it reproduces Phase 1's verdict exactly. If it does not, the venv is not a valid control —
record that and fall back to `nix develop` with an overridden z3 input, or mark the axis unresolved.

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/03_z3-version-sweep.json` - new;
  per-version verdict, reason_unknown, rlimit, wall time

**Verification**:
- At least four z3-solver versions measured, each with a recorded verdict
- The control run (4.16.0 in the venv) matches Phase 1's HEAD verdict, or the axis is explicitly
  marked unresolved with the reason
- A clear yes/no on "does z3-solver version drift flip this formula's verdict?"

---

### Phase 4: Attribute the Root Cause [COMPLETED]

**Goal**: Convert Phases 2 and 3's evidence into a single named cause (or an explicitly-stated
multi-cause verdict), pinned to a commit and/or a z3 version.

**Tasks**:
- [ ] Pin the z3 version to whichever the sweep identified as the last SAT-producing one (or 4.16.0
      if no flip was found), so bisection varies only the tree.
- [ ] Run `repro_m3.py` at each candidate commit from Phase 2's confirmed set, using
      `git bisect run` with the script as predicate where the set is contiguous, or explicit
      `git stash`-guarded checkouts otherwise. Include the specific pair `f9cc081e^` vs `f9cc081e`
      to isolate the task-153 axiom contribution.
- [ ] Reconcile against the known timeline: the 2/2 observed failures predate `f9cc081e`
      (failures at `c8821e96`, 2026-08-31 12:05; `f9cc081e` at 13:35), so a bisect verdict naming
      `f9cc081e` as the *sole* cause contradicts the record and means the bisect is wrong or the
      pre-153 failure had a different cause. Resolve the contradiction explicitly rather than
      reporting the bisect result unqualified.
- [ ] Cross-check against task 153's own recorded observation of "a pre-existing MBQI pathology in
      `capped_skolem_abundance_constraint`'s bare-satisfiability check at M=3, confirmed present
      pre-Phase-4 too" (`f9cc081e` commit message) — an independent sighting of this symptom class
      that any root-cause account must be consistent with.
- [ ] Write the attribution to
      `specs/176_fix_m3_shift_closure_sat_regression/baselines/04_attribution.md`, stating the cause,
      the evidence, and the confidence.

**Timing**: 1.0 hours

**Depends on**: 2, 3

**Verification Tier**: local

**Scope Hypothesis**: This phase assumes the candidate commits are individually checkoutable and
runnable (the repro imports only `model_checker`, which existed across the whole window). Confirm by
checking out the oldest candidate and running the repro before starting the sweep; if older
revisions cannot import, narrow the bisect window and record the floor.

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/04_attribution.md` - new; the root-cause
  verdict with evidence and confidence

**Verification**:
- A named cause (commit, z3 version, or both) with the evidence supporting it
- The pre-153 timeline contradiction is addressed explicitly, not left implicit
- The account is consistent with task 153's independent M=3 MBQI-pathology sighting, or the
  inconsistency is stated

---

### Phase 5: Implement the Constraint/Solver-Layer Fix [IN PROGRESS]

**Goal**: Restore SAT at `N=2, M=3, temporal_depth=1, max_shift=1` with the test's assertions and
15.0s budget unchanged — or, failing that, produce the recorded failed-fix-attempt evidence that
TESTING_GUIDE 8.9 criterion 3 requires.

**Tasks**:
- [ ] Confirm the test currently fails (RED) before any source edit — the TDD entry state. The test
      already exists and already asserts the correct thing; no new test is written to create RED.
- [ ] Implement the fix indicated by Phase 4's attribution. The avenue depends on the verdict:
      an `unsat` verdict means the depth-bounded abundance encoding (or a newly-added frame axiom
      interacting with it) is over-constrained at M=3 and the constraint itself must be corrected;
      an `unknown` verdict means an MBQI/E-matching instantiation problem and the avenue is an
      encoding change that preserves the constraint's logical content.
- [ ] Before trying any trigger/pattern-based avenue, read the recorded task-144 dead ends 7, 8, and
      10 in the docstrings of `depth_bounded_skolem_abundance_constraint` and
      `capped_skolem_abundance_constraint` (`code/src/model_checker/theory_lib/bimodal/semantic/core.py`).
      Those three avenues are closed with measurements; do not re-try them without a stated reason
      why the closing measurement no longer applies.
- [ ] After each candidate edit, run `repro_m3.py` and record verdict + `rlimit-count` + wall time,
      so a rejected candidate leaves a measurement behind (feeding 8.9 criterion 3 if Phase 6 is
      entered).
- [ ] In-phase regression gate after any green candidate: run the whole file
      `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v` and the
      bimodal unit tree `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.
      This is the specific guard against repeating task 144 dead end 8's failure mode — a change that
      helps the target formula and starves other depth-1/M=3 formulas sharing the same axiom.
- [ ] Record every avenue tried and its measurement to
      `specs/176_fix_m3_shift_closure_sat_regression/baselines/05_fix-attempts.md`, whether or not a
      fix lands.
- [ ] If no candidate reaches green within the phase budget, stop and state that plainly in
      `05_fix-attempts.md`; do not extend into budget-widening or assertion-weakening.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - the constraint/solver-layer fix
  (expected site: `depth_bounded_skolem_abundance_constraint` and/or the `skolem_abundance` dispatch
  in `build_frame_constraints`)
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/05_fix-attempts.md` - new; every avenue
  and its measurement

**Verification**:
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py::TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 -v`
  passes, with no edit to the test's settings dict or assertions
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v` shows no
  new failures relative to Phase 1's baseline
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` shows no new
  failures
- `git diff` confirms `GATING_RECHECK_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, and the
  test's `max_time: 15.0` are untouched
- Or: `05_fix-attempts.md` records a documented failure with per-avenue measurements

---

### Phase 6: Fallback — `unstable` Marking (CONDITIONAL) [NOT STARTED]

**Goal**: Only if Phase 5 landed no fix, quarantine the test under the `unstable` marker with all
four TESTING_GUIDE.md section 8.9 entry criteria recorded as separately identifiable items at the
marker site.

**ENTRY GATE**: Enter this phase **only** if Phase 5's `05_fix-attempts.md` records a failed fix
attempt. If Phase 5 landed a fix, skip this phase entirely and proceed to Phase 7.

**BLOCKING PRECONDITION**: If Phase 1/4 classified the failure as a genuine `unsat`, 8.9 criterion 2
("demonstrably non-semantic — the assertion holds on every decided/complete run; the failure mode is
a budget overrun or resource exhaustion, never a changed logical conclusion") **cannot** be met. An
`unsat` verdict is a changed logical conclusion by definition. In that case do not mark the test
`unstable`: leave it failing, mark the phase [BLOCKED], and escalate — a genuine `unsat` at M=3 is a
semantic defect that must not be quarantined.

**Tasks**:
- [ ] Re-read `code/docs/core/TESTING_GUIDE.md` section 8.9 in full before writing anything.
- [ ] Confirm the blocking precondition above does not apply, and record the confirmation.
- [ ] Add `@pytest.mark.unstable` to
      `TestShiftClosure::test_shift_closure_on_extracted_worlds_m3` with a source-site comment
      containing four separately identifiable, individually labeled items:
      (1) **What fails and why** — the mechanism from Phase 1/4 with concrete measurements
      (verdict, `reason_unknown`, `rlimit-count`, wall time, the 5-run distribution);
      (2) **Demonstrably non-semantic** — the evidence that the assertion holds on every decided run
      and the failure is resource/heuristic, not a changed logical conclusion;
      (3) **Fix attempted and its failure recorded** — each avenue from Phase 5 with what its
      measurement showed, plus the closed task-144 dead ends, so a future reader starts at the
      frontier;
      (4) **A written, concrete exit criterion** — yes/no answerable; the section's concrete default
      is 20 consecutive zero-failure `unstable-watch` runs OR a demonstrated encoding fix across
      >= 20 seeds, absent a test-specific reason to differ.
- [ ] Confirm the `unstable` marker is registered for `oracle/` — it is registered in
      `oracle/conftest.py`'s `pytest_configure` (mirroring `code/pyproject.toml`), since `oracle/`
      is outside `code/pyproject.toml`'s ini-discovery reach.
- [ ] Confirm the test is picked up by `.github/workflows/unstable-watch.yml` so it stays observed
      rather than forgotten, and update that workflow's accounting if it names tests explicitly.

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: local

**Files to modify**:
- `oracle/bimodal_logic/tests/test_soundness_regression.py` - add `@pytest.mark.unstable` plus the
  four-criteria comment block
- `.github/workflows/unstable-watch.yml` - only if it names marked tests explicitly

**Verification**:
- All four 8.9 entry criteria present as separately identifiable, individually labeled items at the
  marker site — not merely implied
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py -m "not unstable" --collect-only`
  no longer collects the test
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py -m "unstable" --collect-only`
  collects exactly it
- No assertion in the test body was weakened or removed; `max_time` is still 15.0

---

### Phase 7: Full Oracle Suite Verification [NOT STARTED]

**Goal**: Confirm pass 1 of the full gating oracle suite reports zero failures — the task's stated
exit criterion and task 172's blocked one.

**Tasks**:
- [ ] Launch the full suite detached so the harness cannot reap it:
      `cd /home/benjamin/Projects/ModelChecker && setsid nohup nix develop --command bash oracle/run-oracle-suite.sh > "$SCRATCH/oracle-suite-176.log" 2>&1 & echo $!`
      (the script requires the devShell and refuses to run without `pytest-xdist` importable).
- [ ] Poll the log periodically rather than blocking; budget ~25 minutes (measured basis: pass 1
      ~649-720s, plus pass 2). Judge completion from the script's own summary lines, never from PID
      liveness — the suite's own contract is explicit that a vanished PID is not a verdict.
- [ ] Confirm pass 1 reports zero failures. Note the suite reports `TIMED OUT (exit 124/137)`
      distinctly from `FAILED (exit N)`; a timed-out pass is not a pass.
- [ ] Compare the pass/skip/xfail counts against the pre-fix baseline (`1 failed, 615 passed,
      2 skipped, 4 xfailed`). If Phase 6 was entered, the count shifts by one deselected test —
      account for that explicitly rather than treating the delta as unexplained.
- [ ] Confirm the run was a full run, not a narrowed selection — the research report is explicit that
      narrowed gates are what hid this defect originally.
- [ ] Save the log to `specs/176_fix_m3_shift_closure_sat_regression/baselines/06_full-suite-run.log`
      and record the summary counts.

**Timing**: 0.75 hours (mostly wall-clock wait)

**Depends on**: 5, 6

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts the pre-fix baseline is `1 failed, 615 passed, 2 skipped,
4 xfailed`. That count was measured before tasks 173/177 landed marker and workflow changes, so it
may legitimately have shifted. Confirm by reading the post-run counts against the log rather than
asserting the delta; only the "pass 1 zero failures" criterion is fixed.

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/06_full-suite-run.log` - new; full run log

**Verification**:
- `bash oracle/run-oracle-suite.sh` pass 1 reports zero failures
- Pass 1 completed (did not report `TIMED OUT`)
- The run was full, not narrowed
- Count deltas against the pre-fix baseline are each accounted for

---

### Phase 8: Document the Outcome [NOT STARTED]

**Goal**: Leave a durable record of the root cause and the resolution so a future reader starts at
the frontier, and update `code/docs/core/TESTING_GUIDE.md` if and only if the `unstable` path was
taken.

**Tasks**:
- [ ] Write the decision record to
      `specs/176_fix_m3_shift_closure_sat_regression/baselines/07_decision-record.md`: the classified
      verdict, the attributed cause, the fix (or the recorded failure and the quarantine), and the
      verification evidence.
- [ ] If Phase 5 landed a constraint fix, add a dead-end/finding note in the touched function's
      docstring in `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, matching the
      existing task-144 dead-end note style, so the next reader sees why this shape is now required.
- [ ] If Phase 6 was entered, update `code/docs/core/TESTING_GUIDE.md` section 8.9's accounting only
      where it enumerates marked tests. Do not restate the four criteria there — 8.9 requires them at
      the marker source site, and duplicating them invites drift.
- [ ] If Phase 4 confirmed a task-153 Seriality/Interpolation contribution, record it in the decision
      record and flag it for escalation. Do not revert those axioms; task 153 explicitly deferred that
      to a user decision.
- [ ] Note in the decision record that task 172 is now unblocked and should be re-verified and closed
      via `/implement 172`.
- [ ] Apply `.claude/rules/no-task-references-in-deliverables.md`: task numbers are fine in
      `specs/**` and commit messages, but any note added to `core.py`, the test file, or
      `TESTING_GUIDE.md` must cite durable anchors. Note that `core.py` already contains "Task 114" /
      "Task 144" references at these sites — match the existing local convention rather than
      introducing a divergent one, and do not add *new* bare task-number citations of your own.

**Timing**: 0.5 hours

**Depends on**: 7

**Verification Tier**: prose

**Files to modify**:
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/07_decision-record.md` - new
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - docstring note (only if Phase 5
  landed a fix)
- `code/docs/core/TESTING_GUIDE.md` - marked-test accounting (only if Phase 6 was entered)

**Verification**:
- Decision record states the classified verdict, the attributed cause, and the resolution
- Every changed hunk in `core.py` and `TESTING_GUIDE.md` lies inside a comment/docstring/prose region
- No new bare task-number citation was introduced outside `specs/**`

---

## Testing & Validation

- [ ] `TestShiftClosure::test_shift_closure_on_extracted_worlds_m3` passes at HEAD (or is
      legitimately `unstable`-marked with all four 8.9 criteria recorded at the marker site)
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v` shows
      no new failures against the Phase 1 baseline
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` shows no new
      failures
- [ ] `bash oracle/run-oracle-suite.sh` pass 1 reports zero failures, on a full (not narrowed) run
      that did not time out
- [ ] `git diff` confirms `GATING_RECHECK_SOLVE_TIMEOUT_MS` and `MIN_CONCLUSIVE_GATING_FORMULAS` are
      untouched
- [ ] `git diff` confirms the test's `max_time: 15.0` is unchanged and no assertion was weakened or
      removed

## Artifacts & Outputs

- `specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py` — minimal reproduction and
  bisect predicate
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/01_head-classification.json`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/02_encoding-drift.md`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/03_z3-version-sweep.json`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/04_attribution.md`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/05_fix-attempts.md`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/06_full-suite-run.log`
- `specs/176_fix_m3_shift_closure_sat_regression/baselines/07_decision-record.md`
- A fix in `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, **or** an `unstable` marking
  in `oracle/bimodal_logic/tests/test_soundness_regression.py`

## Rollback/Contingency

Every source edit is confined to `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
(Phase 5) and `oracle/bimodal_logic/tests/test_soundness_regression.py` (Phase 6), each landing in
its own commit, so `git revert` of a single commit restores the prior state without touching the
diagnostic artifacts under `specs/`. Phases 1-4 write only under `specs/` and are non-destructive.

If Phase 5's fix passes the target test but Phase 7's full-suite run surfaces a regression elsewhere,
revert the Phase 5 commit and re-enter Phase 5 with the regression recorded as a new closed avenue in
`05_fix-attempts.md` — the same regressive-candidate policy task 144 applied to its dead ends.

If Phase 1 classifies the failure as genuine `unsat` and Phase 5 finds no fix, the task terminates
[BLOCKED] rather than [COMPLETED]: Phase 6's blocking precondition forbids quarantining a semantic
defect, and task 172 stays blocked pending escalation.
