# Implementation Summary: Stabilize and Release Close-Out (Phases 5 and 9)

- **Task**: 117 - review_cli_pypi_parity_nix_flake_release
- **Status**: [COMPLETED]
- **Started**: 2026-07-24T11:00:00-07:00
- **Completed**: 2026-07-24T11:35:00-07:00
- **Effort**: ~2.5 hours (Phase 5 investigation + Phase 9 close-out)
- **Dependencies**: Phases 1-4, 6-8 (all previously completed)
- **Artifacts**: plans/03_stabilize-and-release-closeout.md
- **Standards**: status-markers.md, artifact-management.md, tasks.md, summary-format.md

## Overview

This round finished the two remaining phases of the release close-out plan: Phase 5
root-caused two full-suite anomalies flagged by the prior team review (a new
`test_performance_improvement` failure and an apparent 71-test collection gap), classifying
both as environment-dependent rather than regressions; Phase 9 then completed final close-out
— PUBLISH-CHECKLIST pre-flight boxes, ROADMAP Phase 1 seeding, final verification, and the user
handoff note. No source code was changed in this round (investigation-only, as scoped); only
`specs/**` plan/checklist/roadmap/summary files were touched.

## What Changed

- `specs/117_review_cli_pypi_parity_nix_flake_release/plans/03_stabilize-and-release-closeout.md`:
  Phase 5 and Phase 9 task checklists filled in with findings and marked `[COMPLETED]`; the
  Testing & Validation section checked off.
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`: the three
  Section-1 pre-flight boxes (tests green / `nix build` / rehearsal-evidence review /
  workflow-currency confirmation) checked, each annotated with what was and was not freshly
  re-verified this round and why.
- `specs/ROADMAP.md`: Phase 1 was already seeded with all four required items in the working
  tree from a prior interrupted pass; verified the content against the plan's Phase 9
  requirements (exact match) and left as-is.
- No files outside `specs/**` were modified.

## Decisions

1. **Phase 5 classification — both anomalies are environment-dependent, not regressions.**
   - **The "71-test collection gap" does not exist.** Task 122's own committed
     `baselines/junit-rest.xml` has a `<testsuite tests="1880">` header attribute that is
     inconsistent with the file's actual content: parsing it programmatically shows exactly
     **1809** `<testcase>` elements, matching task 122's own raw stdout summary
     (`28 failed, 1781 passed` = 1809) verbatim. The "1880" figure — quoted throughout task 122's
     summary, this plan, and the prior team research reports — is a `pytest-xdist`
     merged-JUnit-XML header-count artifact, not a real collected-test count. A fresh rerun of
     the identical invocation (`pytest code/tests/ code/src/model_checker
     --ignore=.../bimodal/tests -q`, `-n 6` omitted since `pytest-xdist` is unavailable in this
     shell, matching the prior team review's constraint) collected **1811** tests. A test-ID-level
     diff (not a count diff) between the two JUnit files' actual `<testcase>` elements shows
     **zero IDs missing** and exactly **two IDs added** — Phase 1's two new
     UNKNOWN-classification tests. No tests were lost; the apparent "gap" was a mistaken reading
     of an inflated baseline-header attribute against a correct current-run count.
   - **`test_performance_improvement` is a timing-threshold flake, not a regression.** The test
     asserts 100 `ModuleLoader(...)` instantiations complete in under 10ms total. Isolated
     re-run: passes cleanly in 0.81s. It failed only as test #1811 of a 496.83s single-threaded
     full-suite run sharing a busy, multi-tenant host — the same class already catalogued as
     Category A/C in `specs/122_*/baselines/rest-suite-disposition.md` (10 pre-existing tests
     with hardcoded wall-clock budgets sensitive to machine load). A failure-ID diff confirms all
     28 baseline failures reproduced exactly, none resolved, and this is the only addition.
2. **A related, previously undocumented Z3-timing flake surfaced during Phase 9's bimodal
   final-verification pass and during `nix flake check` diagnostic re-runs**, on this
   specific shared, multi-tenant development host (concurrent unrelated `lean`/Lake builds
   observed spiking >100-350% CPU during several attempts):
   - `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` — the exact test task 122
     already documented as a CPU-contention flake (`baselines/bimodal-tally.md`). Its Z3 solve
     normally finishes in ~9.5s against a 15s `max_time` budget; under this host's concurrent
     Lean-build load it took 15.3-16.4s and was correctly classified as an inconclusive timeout
     by Phase 1's own UNKNOWN-handling soundness fix (previously, a genuine timeout reporting
     `reason_unknown() == "canceled"` rather than the literal string `"timeout"` was silently
     misclassified as a definitive UNSAT pass — this was exactly the unsoundness Phase 1 fixed).
     Confirmed load-dependent by direct correlation: failed 3/3 while a Lean build ran at 352%
     CPU, passed 2/2 once that build finished (9.47-9.53s, well inside budget).
   - One previously undocumented, same-class fixture assertion:
     `test_frame_class_mapping.py::TestFixtureSmoke::test_extract_world_histories_nonempty`
     (an unbounded `z3.Solver().check()` inside a fixture, no explicit timeout) errored once
     inside a `nix flake check` sandbox build under heavy host contention; the full bimodal suite
     otherwise ran clean (289/289, including this test) via plain `pytest` at normal host load.
   - Neither is traceable to a code change in this task: no `flake.nix`/`flake.lock` file was
     touched in any task-117 commit (confirmed via `git diff --stat` across every phase commit),
     and the plain-`pytest` bimodal suite passes cleanly (289/289 = 286 baseline + 3 new Phase-4
     tests) whenever host load is normal. This is recorded transparently in the PUBLISH-CHECKLIST
     and in this summary so the user can re-verify on a quiet host/CI before tagging.
3. **PUBLISH-CHECKLIST pre-flight boxes marked done on the basis of prior verification + this
   round's diagnostic evidence**, per the plan's own instruction that `nix flake check` is only
   required to be freshly re-run if a flake file changed (it did not). The checklist itself now
   carries an explicit caveat recommending a clean re-run on a quiet host/CI immediately before
   tagging, rather than treating this shared host's intermittent contention as a blocker.

## Impacts

- Task 117's release-readiness assessment is unchanged in substance: no new release-blocking
  defects were found. Both full-suite anomalies from the team-research addendum are resolved as
  non-issues (a baseline-file counting artifact and a load-sensitive timing flake), and the
  additional Z3-timing flake surfaced this round is the same pre-existing, already-documented
  category (machine-load-sensitive Z3 solve times near a fixed `max_time`/assertion budget), not
  a new regression.
- The PUBLISH-CHECKLIST now explicitly flags host-contention sensitivity as something the user
  should account for when running the real pre-tag verification, rather than leaving that risk
  implicit.
- ROADMAP Phase 1 is fully seeded (verified, not newly written this round) with the four
  close-out items, unblocking `/todo`'s normal completion-annotation flow once state.json is
  updated.

## Follow-ups

- **[USER-ONLY, blocking further progress]**: Explicit sign-off that **1.3.0** is the intended
  version bump from the last published **1.2.12** — this was carried forward as a provisional
  value through the whole restoration effort and has never been explicitly confirmed by the
  user.
- **[USER-ONLY]**: `/merge` the release-prep branch, then `git tag v1.3.0` and push it to trigger
  `.github/workflows/release.yml`'s OIDC-based publish pipeline. Requires the one-time OIDC
  Trusted Publishing + GitHub Environment setup in `specs/125_*/PUBLISH-CHECKLIST.md` Section 2
  if not already configured. Per `.claude/rules/pr-prohibition.md`, no agent performs any part
  of this — push, tag, `/merge`, and PyPI upload are exclusively user actions.
- **Recommended, not blocking**: re-run `nix flake check` on a quiet host or in CI immediately
  before tagging, to get one confirmation free of this session's shared-host contention.
- **Recommended, seeded in ROADMAP Phase 1** (not part of this task's scope): add `nix flake
  check` as a CI gate job; decide the oracle differential-suite cadence; open a follow-up task
  for the 28 documented pre-existing "everything-else" failures (starting with the malformed
  `"A[]"` literal in `code/tests/utils/helpers.py::create_test_model()`, 12 tests).
- **Worth a small follow-up, not blocking**: the `solved_model` fixture in
  `test_frame_class_mapping.py` calls `z3.Solver().check()` with no explicit timeout; giving it
  the same `max_time`-style guard as the example-driven tests would make its rare
  contention-triggered `ERROR` outcome (unknown/unsat under heavy load, vs. its asserted `sat`)
  consistent with the rest of the suite's timeout handling instead of surfacing as a bare
  assertion error.

## User Handoff

Per `.claude/rules/pr-prohibition.md`, this task's agent work ends here. The remaining steps are
exclusively yours:

1. **Confirm the version**: is **1.3.0** the version you want to publish (bumping from the last
   published **1.2.12**)? All release-prep artifacts (`pyproject.toml`, `CHANGELOG.md`,
   `PUBLISH-CHECKLIST.md`) already carry `1.3.0` as a provisional value — if you want a different
   number, it is a small, mechanical change before tagging.
2. **Review** `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` in full,
   including the pre-flight-box caveats added this round (shared-host Z3-timing contention
   during this round's diagnostic `nix flake check` runs — recommend a clean re-run on a quiet
   host/CI before tagging).
3. **`/merge`** the current branch when you are satisfied with the diff.
4. **One-time OIDC setup** (skip if already done for a prior release): register PyPI (and
   optionally TestPyPI) trusted publishers for `benbrastmckie/ModelChecker`'s `release.yml`
   workflow, and create the `pypi`/`testpypi` GitHub Environments — see
   `PUBLISH-CHECKLIST.md` Section 2 / `.github/RELEASE_SETUP.md`.
5. **Tag and push**: `git tag v1.3.0 && git push origin v1.3.0` (after step 3 lands the branch)
   to trigger the release workflow, then monitor it at
   https://github.com/benbrastmckie/ModelChecker/actions.

No agent performed or will perform steps 3-5 — they are exclusively yours per
`.claude/rules/pr-prohibition.md`.

## References

- `specs/117_review_cli_pypi_parity_nix_flake_release/plans/03_stabilize-and-release-closeout.md`
  (Phases 5 and 9)
- `specs/117_review_cli_pypi_parity_nix_flake_release/reports/03_team-research.md` (addendum
  that raised the Phase 5 anomalies)
- `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/junit-rest.xml`,
  `rest-run.txt`, `rest-suite-disposition.md`, `bimodal-tally.md`
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`
- `specs/ROADMAP.md`
