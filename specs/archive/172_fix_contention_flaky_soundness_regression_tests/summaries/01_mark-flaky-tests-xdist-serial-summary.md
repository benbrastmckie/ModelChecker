# Implementation Summary: Fix contention-flaky soundness regression tests

- **Task**: 172 - fix_contention_flaky_soundness_regression_tests
- **Plan**: plans/01_mark-flaky-tests-xdist-serial.md
- **Status**: [PARTIAL] — the four-test remedy is fully implemented and verified; the task cannot
  close as fully `[COMPLETED]` because Phase 3's full two-pass verification surfaced a
  reproducible, out-of-remedy defect (see below) that the plan's own Non-Goals forbid fixing here.

## What was done

Phases 1 and 2 completed cleanly. Phase 1 confirmed, by enumerating all 25 `find_countermodel(`
call sites in `oracle/bimodal_logic/tests/test_soundness_regression.py`, that exactly four are
unmarked, bare-default (`timeout_ms=5000`), `temporal_depth>=1` calls with no
`pytest.raises(OracleTimeoutError)` guard — matching the plan's four-test hypothesis exactly.
Phase 2 added `@pytest.mark.xdist_serial` plus an inline rationale comment (matching the
`test_oracle_m_formula_depth1_boundary_safe` precedent's style) to:

- `TestBoundaryVacuity::test_depth1_boundary_safe_is_true`
- `TestBoundaryVacuity::test_depth1_countermodel_has_required_fields`
- `TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output`
- `TestGuardedCompositionality::test_nullity_with_temporal_formula_output`

Both `--collect-only` checks passed (9 tests selected under `-m xdist_serial`, 30 total collected,
unchanged), and `git diff` on the target file showed only the four additive decorator+comment
blocks — no assertion, call, or docstring touched.

## Phase 3 verification results

Two independent full runs of `bash oracle/run-oracle-suite.sh` / its pass-1 command, both against
current HEAD after tasks 152/158/175 landed their commits:

- **Run 1** (full two-pass driver): pass 1 (`-n 6`, 622 items) `1 failed, 615 passed, 2 skipped,
  4 xfailed in 705.05s`; pass 2 (serial, 19 items) `19 passed in 790.92s` (inside the 1800s
  budget). Script summary: pass 1 FAILED, pass 2 PASSED.
- **Run 2** (pass-1-only rerun, full unnarrowed selection, launched to test reproducibility):
  `1 failed, 615 passed, 2 skipped, 4 xfailed in 718.15s` — identical counts, identical failure.

**None of the four target tests appear in either run's failure list**, and pass 2 is green both
times with the expected +4 test-count growth. The remedy this plan set out to implement is fully
verified working.

**A fifth, reproducible failure was discovered**, unrelated to the remedy:
`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3` fails identically in both runs —
`AssertionError: Solver should find SAT for atom 'p' at M=3 with depth-bounded abundance`
(`structure.z3_model_status` is `False`) at `test_soundness_regression.py:541`. This test never
calls `find_countermodel()` — it constructs `BimodalStructure` directly with its own
`max_time: 15.0` setting, entirely outside the `timeout_ms=5000`/`OracleTimeoutError` mechanism
this task's remedy targets, and was correctly outside Phase 1's `find_countermodel(`-scoped
inventory. Two independent full pass-1 runs failing on the same assertion is evidence of a
reproducible failure, not the contention-flake class this task addresses (an earlier working
hypothesis that this might be a one-off contention blip is retracted). `git log --stat` confirms
tasks 152/158/175's landed commits touched no bimodal semantic/solver code this test depends on,
so the failure is not attributable to tree drift during this dispatch. It is **in scope by file**
(same target file) **but out of scope by remedy** (shares no mechanism with the four tests fixed
here).

Per the plan's Risk row for exactly this scenario ("the full two-pass run surfaces a different
pass-1 failure... do not widen scope... record it as a follow-up candidate rather than fixing it
in this task"), this failure was **not fixed** here. Phase 3 therefore closes `[PARTIAL]`, not
`[COMPLETED]`: its own stated verification criteria ("pass 1: zero failures", "the script's own
summary reports success for both passes") are not met, even though the criteria specific to this
plan's remedy (none of the four target tests failing; pass 2 green with +4 growth inside budget)
are fully met.

## Decisions recorded (Phase 4)

1. **`max_rlimit` evaluated and deliberately not used** at the four call sites.
   `code/docs/core/TESTING_GUIDE.md` section 8.13 already rejected this tradeoff for the
   `CL_TH_12`/`CL_TH_13` flake: an rlimit bound can only ever cause an inconclusive result, never
   prevent one, and once a test is in the serial pass there is no residual wall-clock risk left
   for `max_rlimit` to address — adding it would only supply a second independent failure mode.
2. **No AST floor guard added** to `code/tests/ci/test_example_budget_floor.py`. That guard's
   scan shape works on a per-call-site `'max_time': N` dict literal; here the risk is a *shared
   function default* crossed with a formula's `temporal_depth` (not statically readable from the
   call site), which an AST scan cannot resolve without false-positiving on
   `TestKnownBoundaryUnsafe`-style calls that correctly expect a timeout.

## Follow-up candidates (recommend `/spawn`)

1. `oracle/bimodal_logic/tests/test_oracle_provider.py::test_future_sat_returns_dict` — same
   `find_countermodel`/bare-default/`temporal_depth=1` risk class as the four tests fixed here,
   outside this task's `file_scope`.
2. `oracle/bimodal_logic/tests/test_soundness_regression.py::TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`
   — reproducible (2/2 runs) `AssertionError` at line 541, `z3_model_status is False` for a direct
   `BimodalStructure` construction at M=3 with depth-bounded abundance. In scope by file, out of
   scope by remedy. Historically `xfail`'d for "M=3 solver over-constraint"
   (`specs/archive/108_soundness_regression_test_suite/`,
   `specs/archive/114_skolem_abundance_overconstrain_fix/`), measured 2-8s against its 15s budget
   in past runs — worth investigating as a solver/constraint-layer regression, not a scheduling
   issue. This is a stronger follow-up case than a suspected flake, given the 2-for-2
   reproducibility evidence.

## Measured before/after figures

| Metric | Before (task baseline) | After (Run 1 / Run 2) |
|--------|--------------------------|--------------------------|
| Pass 1 failures | 3 (the reported tests) | 1 (unrelated, reproducible; zero of the four target tests) |
| Pass 1 wall clock | not recorded in baseline | 705.05s / 718.15s (budget 1300s) |
| Pass 2 test count | 15 | 19 (both runs) |
| Pass 2 wall clock | 677.08s | 790.92s (Run 1) |
| Pass 2 result | green | green (both runs), inside 1800s budget |

## Non-goals held

`git diff --stat` confirms `oracle/bimodal_logic/provider.py` and
`code/tests/ci/test_example_budget_floor.py` are absent from this task's diff — both explicit
non-goals held throughout.

## Plan Deviations

- Phase 3 closes `[PARTIAL]` rather than `[COMPLETED]`: the phase's own stated "pass 1: zero
  failures" verification criterion is not met, due to an unrelated, out-of-remedy, reproducible
  defect discovered during verification (see above). This is not a deviation from the plan's
  Goals/Non-Goals (which are fully met for the four-test remedy) but a deviation from a clean
  Phase 3 closure, recorded honestly rather than forced green.
- Phase 4's decision-record content was completed despite Phase 3 not closing cleanly, per
  explicit orchestrator direction — Phase 4's own scoped goal (record decisions, confirm file
  purity) has no dependency on Phase 3's pass-1 outcome beyond the already-available measured
  figures.
- No other deviations. All four target tests were marked exactly as planned, with no assertion,
  timeout, or `max_rlimit` change; `provider.py` and `test_example_budget_floor.py` are
  unmodified.

## Rollback

Unchanged from the plan: `git revert` of the Phase 2 commit (`2aae7217`), or
`git checkout HEAD -- oracle/bimodal_logic/tests/test_soundness_regression.py` before commit,
restores the prior state exactly.
