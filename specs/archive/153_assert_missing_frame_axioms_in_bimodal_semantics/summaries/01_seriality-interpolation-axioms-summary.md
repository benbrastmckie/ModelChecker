# Implementation Summary: Assert Seriality and Interpolation in BimodalSemantics

- **Task**: 153 - Assert missing frame axioms in bimodal semantics
- **Plan**: `plans/01_seriality-interpolation-axioms.md`
- **Status**: COMPLETED -- both axioms implemented, tested, documented, and **landed as-is on the
  user's explicit authority**. The `BM_CM_4`/`BM_CM_1` cost regression is accepted as a known,
  recorded cost with its mechanism still unestablished; it is no longer a blocker. The bimodal
  suite has been made non-gating for release runs (see "Landing decision" below).

## What was implemented

- `build_seriality_constraint` and `build_interpolation_constraint` added to
  `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, Skolemized per the research
  report's mandate (single top-level `ForAll` each, witness functions eliminate the existentials,
  no `z3.Exists` in either -- confirmed by direct source inspection).
- Both wired into `build_frame_constraints`'s returned list after `forward_comp` and before
  `*skolem_abundance`, taking the constraint count from 11 to 13 (M<=2).
- `core.py`'s docstrings and the `task_restriction` soundness-analysis comment corrected from
  "three TaskFrame axioms" to five, with item numbers renumbered (7-11) and a stated free/asserted
  ledger pointer to ARCHITECTURE.md.
- New `### Frame-Class Axioms` subsection in `bimodal/docs/ARCHITECTURE.md`: a 7-row
  constraint-level table (5 asserted, 2 free) with per-row citations, an explicit note resolving
  the "asserted axiom count" ambiguity (5/2 at the Z3-row level vs. 2/2 at the paper-axiom level),
  and a duration-domain-guard footnote recording the bounded-window vs. unbounded-`\Z` gap as open.
- New/renamed tests: `TestFrameConstraintsJointSatisfiability`, `TestSeriality`,
  `TestInterpolation` in `test_frame_constraints.py`; `TestSerialityPostHoc`,
  `TestInterpolationPostHoc` in `test_frame_class_mapping.py`;
  `test_three_taskframe_axioms_present_in_frame_constraints` renamed to
  `test_five_taskframe_axioms_present_in_frame_constraints`. Both files: 27/27 passing, 19.08s.

## Phase 2: definitional-reachability alternative -- measured, not adopted

Prototyped `task_rel` as bounded R-reachability (unrolled disjunction over the `2M-1` duration
window, Skolemized chain witnesses, no nested `Exists`, no `z3.TransitiveClosure`) via a
process-local `ReachabilitySemantics` subclass; `core.py` untouched by this measurement. Result on
the six-example subset: `BM_TH_3`/`BM_TH_4` stay `match` at comparable timing (0.05s/0.05s vs.
baseline 0.11s/0.04s), `BM_TH_1`/`BM_TH_2` unchanged `inconclusive`-at-30s, no Z3-specific API
needed (had to drop one existing `MultiPattern` hint on `forward_comp`).

**Outcome: "go" on the narrow macro-substitution question measured, but this does not cover the
redesign's actual soundness payoff** (deriving `nullity_identity`/`converse`/`forward_comp` as
theorems rather than assertions, which would require a materially harder shared-witness design not
attempted here). Per the plan's scope call, this does not expand the task -- both axioms were
implemented against the Skolemized direct-fix regardless. **Recommended as a follow-on task** if
the reachability redesign is pursued, with this measurement's scope caveat carried forward.

## Landing decision: both axioms accepted as-is, on the user's explicit authority

The cost regression documented in the next section was raised to the user as two
`user_decision_needed` blockers. The user answered:

> "I don't want tests from bimodal logic to hang things up when the entire bimodal logic is in
> development and shouldn't be considered part of the release to pass all tests."

That resolves both blockers as **accept the cost regression and land both axioms as-is**. What
this did and did not authorize, stated precisely:

- **Both axioms stay in the code exactly as specified.** Neither was dropped, weakened, or
  deferred. The plan's own "land Seriality alone, defer Interpolation" fallback was **not** taken.
- **Nothing was engineered around the finding.** No `max_time` was raised on any bimodal example,
  no expected verdict was adjusted, no test was marked `unstable` or `xdist_serial`, and
  `BM_CM_4`'s and `BM_CM_1`'s example definitions were not edited.
- **Accepting the cost is not explaining it.** The mechanism remains unestablished; the section
  below is unchanged and stands as the honest record. The repeated-runs variance study needed to
  settle it is still an open follow-on.

The substantive work this authorized is making bimodal non-gating, recorded under "Making bimodal
non-gating" below.

## The accepted regression: BM_CM_4 cost, mechanism not established

Full detail in `baselines/README.md`'s "Phase 7" section; summarized here.

**The finding (well-evidenced)**: `BM_CM_4` (N=2, M=2 countermodel example, `\Diamond A -> \past A`)
regresses from a clean, fast, decided countermodel (4.07s `match` pre-change; 18.26s-20.29s in the
task 152 baseline and this task's own Phase 1 pre-change run) to `inconclusive` at its own
`max_time=120` with both new axioms present. Four independent measurements against the real,
committed `build_seriality_constraint`/`build_interpolation_constraint` methods all agree:
`pytest -k "BM_CM_4"` (120.78s, FAILED), a direct `run_enhanced_test` call (120.37s,
`inconclusive`), the full 52-example Phase 7 suite run (120.36s, `inconclusive`), and an isolation
probe at a shorter 40s budget (40.21s, `inconclusive`). This is a **cost** regression, not a shown
soundness/verdict flip: the axioms have not been shown to eliminate `BM_CM_4`'s countermodel, only
to make the search not finish within budget.

`BM_CM_1` (the pre-existing, documented-`unstable` example) shows the same before/after direction
(decided `match` pre-change, `inconclusive` at its own `max_time=60` post-change), but its
isolation table is **non-monotonic and contradicts `BM_CM_4`'s pattern** (its `both` configuration
decides *faster*, 16.43s, than `neither`, 22.55s; its `interpolation_only` configuration is the one
that fails to decide). This rules out stating a single general mechanism ("the two axioms interact
superlinearly") -- the honest statement is that Z3's solving cost here is highly sensitive to the
exact constraint set and to incidental formula-construction details in ways that are not
compositional, corroborated independently by a harness artifact discovered mid-investigation
(symbol naming alone -- `serial_succ` vs. `serial_succ_inline` -- changed `BM_CM_4` from
120s-`inconclusive` to 4.56s-`match`). `BM_CM_1`'s own `neither` baseline in this isolation run
(22.55s) is already well above its documented median (~7-8s), confirming it is inherently
high-variance independent of this task's changes; its `unstable` marker is not re-adjudicated.

**`TN_CM_2`** (`inconclusive` at 10.1s post-change) is confirmed unchanged -- already `inconclusive`
pre-change in both the task 152 baseline (10.09s) and this task's own Phase 1 run (10.1s). Not a
new or affected example. **`BM_TH_1`/`BM_TH_2`** remain unchanged `inconclusive`-at-~30.3s in all
three sources -- per the plan's own rule, reported as no signal, never as evidence of no
regression. **`BM_TH_3`/`BM_TH_4`** stay `match`, exactly as the research report's Skolemized
benchmark predicted.

**Mitigation attempted**: an explicit Z3 pattern anchoring `build_interpolation_constraint` to its
premise's ground `task_rel` term (mirroring `build_forward_comp_constraint`'s existing
`MultiPattern` convention) did not recover a decided result on `BM_CM_4` (still `inconclusive` at
40s). Guard-tightening was not attempted separately: both axioms' guards are already exactly as
tight as their mathematical content allows (no slack to remove without changing what the axiom
means).

**What settling the mechanism would need**: repeated runs per configuration to characterize the
variance distribution, distinguishing genuine superlinear interaction from Z3 search-cost variance
that happens to correlate with constraint-set changes. This is beyond this task's budget and is
recommended as a follow-on.

**Why the plan's own documented fallback was not applied**: the plan's rollback section names
"land Seriality alone, defer Interpolation" as the safe fallback for exactly this failure mode. It
was not applied here because (a) isolation shows neither axiom alone is responsible for `BM_CM_4`'s
regression -- both individually stay decided at modest cost -- so dropping Interpolation alone
would not obviously fix it and would also not obviously be necessary; and (b) it would silently
narrow this task's shipped scope (both axioms asserted, per the task's own stated definition of
done) without the user's decision. The user subsequently decided in favour of landing both (see
"Landing decision" above), so the fallback stays unapplied -- now by decision rather than by
deferral.

## Making bimodal non-gating (Phase 8)

**The mechanism already existed; nothing claimed it.** A `development` pytest marker was already
registered in `code/pyproject.toml`, already carried by all six release-gating `-m` expressions
(`.github/workflows/tests.yml`'s two passes, `flake.nix`'s two, `differential-tests.yml`, and
`oracle/run-oracle-suite.sh`), already enforced by `code/tests/ci/test_unstable_deselection_
wiring.py`, already supported by `.github/scripts/unstable_watch_classify.py`, and already
documented as `TESTING_GUIDE.md` section 8.14 -- whose own "Currently marked" paragraph read "No
test carries `development` today." So no new exclusion mechanism was invented. The missing step
was applying it.

**What was done.** A path-scoped `pytest_collection_modifyitems` hook in
`code/src/model_checker/theory_lib/bimodal/tests/conftest.py` applies `development` to all 313
tests collected from that tree. Both gating expressions now collect **0 of 313** bimodal tests;
`-m development` collects all 313, so the suite stays runnable on demand.

**A real defect was found and fixed during implementation.** The first version of the hook looped
over `items` without a path check. pytest hands a `pytest_collection_modifyitems` implementation
the *entire session's* item list once its conftest has loaded -- it is not scoped to that
conftest's directory. The unfiltered version marked all **2534** tests in the repository, and the
gating parallel expression consequently collected **zero**. This leak is invisible to a per-root
containment check (a subprocess collecting only `logos` never loads bimodal's conftest, so it
passes against a fully-leaking hook); it only appears in a mixed-root collection, which is exactly
the `pytest tests src/model_checker` shape both gating drivers invoke. A mixed-root assertion was
added and is what catches it.

**TDD.** `code/tests/ci/test_development_marker_application.py` was written first and confirmed
RED (3 failed, 4 passed) before the hook existed. Final: 9 passed. It asserts complete coverage of
bimodal, zero leakage against each non-bimodal root individually *and* in the mixed-root
collection, that the opt-in path works, and that the gating expression still collects >1000 tests
so a future leak surfaces as a collapsed count rather than a silent green.

**Scope.** Bimodal only, enforced structurally. No logos, exclusion, imposition, or core test was
skipped, deselected, or weakened. Bimodal's soundness and cross-oracle differential tests live in
`oracle/bimodal_logic/tests/`, where `development` is deliberately unregistered, so they remain
fully gating -- no semantic claim about bimodal's correctness is quarantined by this change.

**Deliberately not done: no `addopts` default.** `code/pyproject.toml`'s `addopts` was **not**
given an `-m "not development"` filter. That would be a second exclusion mechanism parallel to the
repo's established one, and it would make `pytest <bimodal path>` and `./run_tests.py bimodal`
collect zero tests and report success -- the silent-green failure mode section 8.14 exists to
prevent. **Consequence, stated rather than hidden:** a bare local `pytest` from `code/` still
collects and can still fail on bimodal. The gating-equivalent local invocation
(`pytest tests src/model_checker -m "not development"`) is documented in 8.14 and in bimodal's
`tests/README.md`. If the intent was for the bare local run to be green too, that is a one-line
`addopts` change plus an ergonomics fix in `run_tests.py`, and it needs a deliberate decision.

**Documentation.** Section 8.14's granularity rule was amended from "per-test, never theory-wide"
to "per-test by default; theory-wide only on an explicit, recorded declaration", with bimodal as
the one authorized blanket; its "Currently marked" paragraph now records the accepted risk (a
bimodal test regressing from passing to failing no longer gates), the three bounds on it, the
opt-in invocation, and the exit path. `bimodal/tests/README.md` was a 0-byte file and now carries
the running guide and a per-file inventory. `bimodal/README.md` gains a Development Status section.

**One cross-task consequence.** The `development` marker's owning task recorded a Phase 6 exit
criterion "`pytest --collect-only -m development -q` collects zero tests". That is now false by
design -- this is the first claim on the category. Section 8.14's "Currently marked" paragraph, the
one place that statement lived, has been updated.

## A regression this task caused outside the bimodal test tree, found and fixed

Running the gating suite (which the previous dispatch had not done) surfaced three failures in
`tests/cli/test_flag_matrix.py::test_output_affecting_boolean_flag_changes_output`
(`print_constraints`, `print_z3`, `print_impossible`) under the `-n 4` parallel pass. They are
**not** bimodal-test-tree failures, are **not** covered by the `development` marker, and were
**caused by this task's axioms**:

- `code/tests/cli/conftest.py`'s tiny CLI example module used **bimodal** with no explicit
  `max_time`, inheriting `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS`' 1-second default.
- Measured directly: that example solves in **~0.42s** with `core.py` at `eb1639de` (pre-axiom,
  3/3 runs) and **~4.2-4.7s** with both axioms present (3/3 runs at a 30s budget). It therefore now
  always times out at 1s and finds no model.
- With no model, `-p`/`-z`/`-i` have nothing extra to print, so the flagged and unflagged runs
  produce byte-identical output except for a `Solver Run Time: 1.000X seconds` float. The test
  passed serially only on microsecond jitter in that float and failed three ways under `-n 4`.

**This is an independent, ~10x cost data point on the two axioms**, on a far simpler example than
`BM_CM_4`/`BM_CM_1` (N=2, no premises, single conclusion `A`), and it corroborates the cost
regression on a formula with no modal or temporal operator at all.

**Fix**: the fixture was switched from bimodal to logos (~0.001s for the same example), matching
the precedent and rationale `test_flag_matrix.py`'s `_CVC5_COMPATIBLE_EXAMPLE` already documents
for its own switch. These are gating CLI-*plumbing* assertions -- flags accepted, output changed,
files written -- and nothing in them is bimodal-specific; pinning them to the one deliberately
non-gating theory coupled the CLI gate to that theory's solver cost. `tests/cli/`: 90 passed, 1
skipped, 12.0s. The failure was **not** absorbed into the bimodal exclusion.

## Test results

| Run | Result |
|---|---|
| `pytest tests/` (the suite the previous dispatch recorded as not run) | **601 passed, 5 skipped, 0 failed** (198.66s) |
| `pytest tests/ci/` (CI contract suite) | 92 passed |
| `pytest tests/ci/test_development_marker_application.py` | 9 passed |
| `pytest tests/cli/` | 90 passed, 1 skipped (12.0s) |
| Gating parallel pass, `-n 4`, CI's own `-m` expression | **2088 passed, 1 skipped, 0 failed** (83.66s, exit 0) |
| Gating serial pass, CI's own `xdist_serial` expression | **9 passed, 2527 deselected, 0 failed** (exit 0) |
| Full bimodal suite (`-m development`) | 308 passed, 5 failed -- unchanged, accepted, non-gating |

The 5 skips in `tests/` are pre-existing and unrelated: one CLI installed-mode guard (skipped in
`source` mode by design) and four `test_inclusions.py` notebook-directory skips.

Both gating passes are green, which is the release-relevant result: the parallel pass reproduces
`.github/workflows/tests.yml`'s and `flake.nix`'s own `-m` expression and `-n 4` verbatim. The
same two passes were run **before** the `tests/cli/conftest.py` fix and gave 3 failed / 2084
passed; the delta is exactly the three flag-matrix cases discussed above.


## Plan Deviations

- Phase 1's harness script includes a `with_new_axioms` arm (inline reconstruction) that was
  discovered during Phase 7 to diverge from the real committed methods due to Z3 MBQI sensitivity
  to symbol naming -- documented in `baselines/README.md` with a correction note; Phase 7's actual
  post-change run used the `baseline` arm against the post-Phase-4 tree instead.
- Phase 7's "full bimodal suite green" verification item is not met: 5 failures (`BM_CM_1`,
  `BM_CM_4`, and 3 `test_bound_var_counter_isolation.py` parametrizations of `BM_CM_4`), all
  attributable to the characterized cost regression, none new or unexplained. **Accepted, not
  resolved**, on the user's explicit authority; the suite is now non-gating, so these failures no
  longer gate a release run. Still 5 failures, and not claimed otherwise.
- The broader `code/tests/` suite, recorded as not run in the previous dispatch, was run in Phase
  8: **601 passed, 5 skipped, 0 failed**.
- No axiom was dropped, no bimodal example's `max_time` was raised, no test was marked `unstable`
  or `xdist_serial`, and no expected verdict was adjusted to route around the regression. The
  regression is reported as found, not engineered away.
- **Phase 8 was added after the plan was written**, to execute the user's landing decision. It is
  not a deviation from a planned phase but an addition beyond the plan's original 7.
- Phase 8 changed one file outside the plan's declared `file_scope`, `code/tests/cli/conftest.py`,
  to repair a gating-test regression this task's own axioms caused (detailed above). Leaving it
  would have meant shipping a red gate; absorbing it into the bimodal exclusion was explicitly
  ruled out.

## Out-of-scope follow-ups (flagged, not fixed)

- `oracle/bimodal_logic/provider.py:17`-`70` carries a frame-axiom table quoting `core.py`'s
  now-superseded three-axiom claim (outside this task's `file_scope`) and will diverge further as
  `core.py`'s docstring has now changed. Needs a follow-on task.
- The definitional-reachability redesign (Phase 2) is measured but not implemented; a follow-on
  task should carry the theorem-derivation half of that measurement forward if pursued.
- The BM_CM_4/BM_CM_1 cost-regression mechanism needs a repeated-runs variance study to settle
  whether it is a genuine axiom interaction or Z3 search-cost sensitivity, or both.
- The duration-domain gap (bounded window `(-M, M)` vs. the paper's unbounded `\Z`) remains
  recorded, not resolved, per Deliverable 4's own scope.
- **`--print_constraints` / `-p` is an unwired CLI flag.** Found while diagnosing the flag-matrix
  failures: `ModelStructure.print_constraints()` (`src/model_checker/models/structure.py:499`) has
  **zero callers** anywhere in `src/model_checker`. With a model found and the fixture on logos,
  `-p` changes the CLI's output by nothing at all except run-time floats, so
  `test_output_affecting_boolean_flag_changes_output[print_constraints]` -- a test whose own
  docstring says it exists to stop the flag matrix "passing vacuously for a no-op flag" -- is
  itself passing vacuously for that parameter. `-z` (18 differing lines) and `-i` (2) are genuinely
  wired. Pre-existing and unrelated to this task. Deliberately **not** fixed here: repairing the
  test's assertion without repairing the flag would turn a currently-green gating suite red on an
  unrelated defect. Needs its own task covering both halves.
- **Whether the bare local `pytest` run should also exclude bimodal.** See "Deliberately not done"
  above; it needs a decision, not just an edit.

## Artifacts

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/` -- regression harness,
  pre-change and post-change verdict JSON, reachability-alternative measurement, README with full
  Phase 7 diff and flip accounting.
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/handoffs/` -- per-phase handoffs.
- Modified (Phases 1-7): `code/src/model_checker/theory_lib/bimodal/semantic/core.py`,
  `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`.
- Added (Phase 8): `code/tests/ci/test_development_marker_application.py`,
  `code/src/model_checker/theory_lib/bimodal/tests/README.md` (was a 0-byte file).
- Modified (Phase 8): `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
  `code/docs/core/TESTING_GUIDE.md`, `code/src/model_checker/theory_lib/bimodal/README.md`,
  `code/tests/cli/conftest.py`.
