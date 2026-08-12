# Implementation Summary: Fix Bimodal Solver-Timing Flakes and Introduce the `unstable` Test Category

- **Task**: 159 - fix_bimodal_flake_and_unstable_category
- **Status**: [COMPLETED]
- **Started**: 2026-08-12T19:49:00Z
- **Completed**: 2026-08-12T20:06:00Z
- **Effort**: ~7.5 hours (plan estimate); actual agent time substantially less, dominated by two
  ~3-minute local oracle-suite test runs
- **Dependencies**: None
- **Artifacts**: plans/01_bimodal-flake-unstable-category.md, reports/01_bimodal-flake-and-unstable-category.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Both bimodal test defects named in the task were investigated with a repair-first ordering per
the plan's phase sequencing. BM_CM_1's timing flake had no available encoding fix (a third
avenue -- finite unrolling of the time quantifier -- was tried and closed as
inconclusive-to-negative) and was marked `unstable` with all four entry criteria recorded
in-line. The oracle gating floor's conclusive-population shortfall had a genuine,
measurement-backed repair (widening `GATING_RECHECK_SOLVE_TIMEOUT_MS` 20000 -> 40000ms), landed
and verified locally at 103/103 conclusive, but not yet verified on real CI (a user action). The
`unstable` marker, its deselection wiring across all gating workflows (plus `flake.nix`, outside
the original file scope), the non-gating `unstable-watch.yml` observation workflow, and
`TESTING_GUIDE.md` section 8.9 were all implemented per the plan's 8 phases. A conditional
follow-up task (160) was created since neither defect fully closed.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/operators.py`: `_fresh_bound_int`'s docstring gained
  a third closed-avenue record (finite unrolling of `ForAllTime`/`ExistsTime`) alongside the two
  avenues a prior round of work already closed.
- `code/src/model_checker/theory_lib/bimodal/examples.py`: `BM_CM_1_settings`' comment gained the
  real 60.94s CI failure datum, this round's independent 7-seed sweep, and an explicit
  re-affirmation that `max_time` is not to be re-tuned again.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`: `GATING_RECHECK_SOLVE_TIMEOUT_MS`
  widened 20000 -> 40000ms with a full method/measurements/ruled-out/USER-ACTION-REQUIRED
  justification comment. `MIN_CONCLUSIVE_GATING_FORMULAS` untouched (still 100).
- `.github/workflows/differential-tests.yml`: `--timeout` raised 900 -> 1500 (headroom for the
  wider per-formula budget); `-m` expression on the first invocation extended with
  `and not unstable`.
- `code/pyproject.toml` and `oracle/conftest.py`: `unstable` marker registered in both pytest
  trees, verbatim task text, mirroring the `slow`/`differential` dual-declaration pattern.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`: `UNSTABLE_EXAMPLES =
  {"BM_CM_1"}` and a `pytest.param`-based parametrize apply `pytest.mark.unstable` to
  `test_example_cases[BM_CM_1-example_case7]`, with all four entry criteria and a written exit
  criterion recorded in-line. Node IDs verified byte-identical before/after.
- `.github/workflows/tests.yml` and `.github/workflows/release.yml`: gating `-m` expressions
  extended with `and not unstable`; `release.yml`'s `test-and-release` job (which runs no pytest
  suite) got a documented no-op comment instead.
- `.github/workflows/unstable-watch.yml` (new): nightly `schedule` + `workflow_dispatch`,
  non-gating, runs `-m unstable` across both trees, classifies failures as TIMING vs. NEW,
  fails the job only on NEW, tracks a consecutive-green streak via `gh run list`, and surfaces
  `READY TO PROMOTE` at 20.
- `code/docs/core/TESTING_GUIDE.md`: new section 8.9 documenting the full policy; also corrected
  section 8.8's now-stale `20000 ms` reference to the widened `40000 ms` budget.
- `flake.nix` (outside the originally declared file scope; widened with reason recorded in the
  Phase 5 commit): `checks.default`'s textually-identical `-m` expression to `tests.yml`'s also
  extended with `and not unstable`, since it runs the same bimodal suite under the nixpkgs Z3
  toolchain and would otherwise silently re-expose the same flake there.
- `specs/state.json` / `specs/TODO.md`: follow-up task 160
  (`verify_bimodal_oracle_budget_and_watch_unstable_marker`) created, `task_type: "python"`,
  carrying forward the six required items (marked test + exit criterion, do-not-re-tune verdict,
  oracle measurements + floor instruction, the outstanding CI verification obligation, everything
  already ruled out, and the promotion path/20-run threshold).

## Decisions

- Phases 2 and 3's file edits landed in a single commit (a staging slip -- both phases' files were
  staged together before the first phase-2 commit) rather than two separate commits as the plan's
  per-phase convention intends. Content is correct and complete; only the commit boundary is
  merged. No functional impact.
- `flake.nix` was widened into scope during Phase 5, per the plan's own Scope Hypothesis
  instruction to check it and extend if it carries a matching `-m` expression (it does, and is
  outside the file scope named in the delegation message). Recorded here and in the Phase 5 commit
  message rather than silently skipped.
- The follow-up task was named `verify_bimodal_oracle_budget_and_watch_unstable_marker` (containing
  "bimodal") specifically so the plan's own literal verification command
  (`jq '... select(.project_name | test("bimodal"))'`) would match it.

## Plan Deviations

- Phases 2 and 3 committed together instead of as two separate commits (see Decisions above) --
  altered, not skipped: both phases' work is complete and verified, only the git history
  granularity differs from the plan's stated per-phase convention.
- `flake.nix` added to the touched file set beyond the delegation's declared file scope -- this was
  explicitly directed by the plan's Phase 5 task list and Scope Hypothesis (not a spontaneous
  widening), and is recorded in the Phase 5 commit message per that same instruction.

## Impacts

- BM_CM_1 no longer runs in any gating pytest invocation (`tests.yml`, `differential-tests.yml`,
  `flake.nix`'s check); it is observed nightly by `unstable-watch.yml` instead. The documented CI
  flake this task exists to fix should stop appearing in gating `Tests` workflow runs.
- The oracle gating floor's conclusive-population shortfall has a landed, locally-verified fix,
  but real-CI verification is outstanding -- see the USER ACTION note in
  `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s comment and follow-up task 160.
- `release.yml`'s `build` job and `test-and-release` job are both now structurally incapable of
  gating on a quarantined test (a defensive posture, since neither runs bimodal tests today).
- A new, first-of-its-kind `schedule:`-triggered workflow exists in this repository
  (`unstable-watch.yml`); it has never been exercised on real GitHub Actions infrastructure by this
  implementation round (only locally rehearsed: node ID selection, YAML parsing, and the
  classification Python's logic against a hand-written JUnit XML sample).

## Follow-ups

- Follow-up task 160 (`verify_bimodal_oracle_budget_and_watch_unstable_marker`,
  `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/`) carries forward: the
  outstanding `workflow_dispatch` verification of `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` on
  real CI; monitoring `unstable-watch.yml`'s `READY TO PROMOTE` surfacing for BM_CM_1; and the
  full frontier of what has already been ruled out for both defects.
- **USER ACTION REQUIRED**: push this branch and dispatch `.github/workflows/differential-tests.yml`
  via `workflow_dispatch` 2-3 times to verify the widened oracle budget on real CI (agents cannot
  push or trigger `workflow_dispatch` per `.claude/rules/pr-prohibition.md`). Once verified, a
  single `workflow_dispatch` of `.github/workflows/unstable-watch.yml` would additionally confirm
  the new workflow runs green on real infrastructure.

## References

- `specs/159_fix_bimodal_flake_and_unstable_category/reports/01_bimodal-flake-and-unstable-category.md`
- `specs/159_fix_bimodal_flake_and_unstable_category/plans/01_bimodal-flake-unstable-category.md`
- `code/docs/core/TESTING_GUIDE.md` section 8.9
- `specs/state.json` (task 160)
