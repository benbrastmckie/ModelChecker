# Implementation Summary: Re-run the release rehearsal and prepare the PyPI publish

- **Task**: 151 - rerun_release_rehearsal_and_publish_to_pypi
- **Status**: [COMPLETED]
- **Started**: 2026-08-12T17:00:00Z
- **Completed**: 2026-08-12T18:05:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: 147, 149, 150, 155, 156, 157 (all `[COMPLETED]`)
- **Artifacts**: plans/01_release-rehearsal-publish-prep.md, PUBLISH-CHECKLIST.md,
  rehearsal/ (11-file evidence set), this summary
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  pr-prohibition.md

## Overview

Executed the terminal task of the release sequence: corrected `code/scripts/release-verify.sh`'s
gate contract (bare `check-wheel-contents` no longer needs `--ignore W002`, since the duplicate
`VERSION` files that triggered it are gone), synced the two documentation files that still
described the old contract, expanded the never-published `## [1.3.0]` CHANGELOG entry to cover
everything landed since it was written, captured a fresh, fully-green rehearsal evidence set, and
obtained a PASS `nix flake check` verdict on a confirmed-quiet host. Wrote a task-scoped
`PUBLISH-CHECKLIST.md` gating on the PyPI trusted-publisher registration as item 0. All six phases
closed `[COMPLETED]`; no user-only operation (`git push`, `git tag`, `twine upload`, `/merge`,
`/tag`) was executed at any point.

## What Changed

- `code/scripts/release-verify.sh`: flipped `check-wheel-contents` (bare) to a hard gate; removed
  the now-redundant `--ignore W002` step (`step_d2_wheel_contents_ignore_w002()`), its evidence
  file, and its call site; corrected the header comments and evidence-file manifest (12 files ->
  11); confirmed via `bash -n` and `--help`.
- `.github/RELEASE_SETUP.md`: corrected the evidence table, the hard-gate list, both W002-reading
  paragraphs, and the "historical context only" note so the tree-state clause reads correctly
  (the tree has since **lost**, not grown, the duplicate `VERSION` files).
- `code/scripts/README.md` (deliberately widened beyond the recorded `file_scope`, since it
  carried the same stale framing): corrected the `release-verify.sh` section and output-file list.
- `code/CHANGELOG.md`: expanded the never-published `## [1.3.0]` entry with new sections covering
  the core/theory_lib boundary refactor, the `theory_lib/*/VERSION` dedupe (clearing
  `check-wheel-contents` `W002`), two CI fix classes (missing `wheel` build dependency,
  timing-budget raises), and the new `release-verify.sh` rehearsal runner. No version bump; all
  three version literals (`pyproject.toml`, both `flake.nix` sites) remain in agreement at
  `1.3.0`.
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/`: fresh, fully-green
  11-file evidence set from an end-to-end `release-verify.sh --ref 1.2.12` run (exit 0).
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/PUBLISH-CHECKLIST.md`: new, derived from
  the archived task-125 template's structure with entirely fresh data, gating on the PyPI
  trusted-publisher registration as item 0.

## Decisions

- **d2 disposition: removed, not demoted.** With W002 no longer firing, bare
  `check-wheel-contents` and `--ignore W002` are functionally identical against the current
  wheel; retaining a permanently-redundant second invocation added no signal, so `step_d2_*` was
  removed entirely rather than kept as an `info`-classified historical comparison.
- **CHANGELOG: fold into 1.3.0 (Option A), not a version bump.** `1.3.0` has never been published
  to PyPI or tagged in git, so there is no external consumer whose view of a prior "1.3.0" could
  be confused by the entry growing. The date line was changed to note the entry was expanded
  2026-08-12, with the actual publish date deferred to the `v1.3.0` tag push.
- **`nix flake check` judged quiet-host-valid by load average, not process count.** `ps aux`
  showed 40 concurrent `claude` processes on the shared host, which could read as contended, but
  per-process CPU% showed nearly all idle and the load average (0.76-1.31 on 24 cores) was well
  under the documented 4.84 contended baseline. Load average — the metric that actually predicts
  Z3-solve wall-clock contention — was the deciding signal, not raw process count.
- **PUBLISH-CHECKLIST.md's Section 0 restates the archived checklist's "One-Time OIDC Setup" gate
  as the lead item**, rather than leaving it in its original structural position (Section 2),
  because the GitHub-Environments half is now confirmed done and only the PyPI-side
  trusted-publisher registration remains — surfacing it first matches the plan's explicit
  instruction to make it "gate item 0, first and blocking."

## Plan Deviations

- None (implementation followed plan). The one plan-anticipated fork — Phase 5's FLAKE branch and
  its conditional `max_time` hardening of
  `code/src/model_checker/builder/tests/unit/test_example.py` — was not taken, because the
  quiet-host run returned a clean PASS with neither documented contention-sensitive test failing;
  this is the plan's own "no hardening needed" outcome, not a deviation from it.

## Impacts

- The release-blocking documentation/gate-contract defect (`release-verify.sh` and
  `RELEASE_SETUP.md` both describing a W002 expectation that no longer holds) is corrected; a
  future rehearsal run will not need to re-diagnose this.
- A fresh, fully-green rehearsal evidence set now exists under `specs/151_.../rehearsal/`,
  superseding both the archived task-125 evidence and every intermediate task's now-stale set.
- `nix flake check` is confirmed clean on a quiet host at the current tree state, clearing that
  release-blocking gate without needing any test-budget hardening.
- The only remaining blocker before the user can safely tag `v1.3.0` is the PyPI-side
  trusted-publisher registration (web-UI work, outside agent reach) — everything else in
  `PUBLISH-CHECKLIST.md`'s Pre-Flight section is already checked off with fresh evidence.

## Follow-ups

- **User**: complete `PUBLISH-CHECKLIST.md` Section 0 (register the PyPI trusted publisher for
  `benbrastmckie/ModelChecker`, workflow `release.yml`, environment `pypi`) before tagging.
- **User**: if any commit touches `code/src` between now and the tag push, re-run
  `bash code/scripts/release-verify.sh --ref 1.2.12` immediately before tagging — the rehearsal
  evidence in this task is not one-and-done.
- **User**: execute `PUBLISH-CHECKLIST.md` Sections 3-4 (tag, push, monitor `release.yml`,
  post-publish verification runbook) once Section 0 is cleared. None of this was executed by this
  task, per the standing user-only constraint.

## References

- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/plans/01_release-rehearsal-publish-prep.md`
  — the executed plan, with per-phase implementation notes recorded inline.
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/reports/01_release-rehearsal-rerun.md`
  — the research this plan was built from.
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/parity-diff.md` — this round's
  rehearsal evidence and parity diff against `model-checker==1.2.12`.
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/PUBLISH-CHECKLIST.md` — the user-facing
  publish checklist this task produced.
