# Implementation Summary: Fix TestPyPI Trusted Publisher + One-Glance OIDC Diagnostics

- **Task**: 161 - Fix TestPyPI trusted-publisher registration and make future OIDC mismatches diagnosable in one glance
- **Status**: [BLOCKED] (Phase 1 complete; Phases 2 and 3 are USER GATE and remain outstanding)
- **Started**: 2026-08-26T01:14:00Z
- **Completed**: 2026-08-26T01:20:00Z
- **Effort**: ~30 minutes (Phase 1 only; agent-side)
- **Dependencies**: None
- **Artifacts**: plans/01_fix-testpypi-trusted-publisher.md, reports/01_fix-testpypi-trusted-publisher.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md, pr-prohibition.md

## Overview

This task adds an additive, diagnostic-only OIDC-claims step to the `publish-testpypi` job of
`.github/workflows/release.yml`, so a future TestPyPI `invalid-publisher` rejection is readable
at a glance. Only Phase 1 (this diagnostic step) is agent-authorable. Phase 2 (registering the
trusted publisher on test.pypi.org) and Phase 3 (verifying on a real `v*` tag push) are both
explicitly USER GATE / USER-ONLY per the plan and `.claude/rules/pr-prohibition.md`, and were
correctly left untouched (`[NOT STARTED]`) by this dispatch.

## What Changed

- `.github/workflows/release.yml`: inserted one new step, `Print OIDC claims (diagnostic
  only)`, as the first entry of the `publish-testpypi` job's `steps:` list, before `Download
  distribution artifact` and before the `Publish to TestPyPI` upload step. The step:
  - Resolves the OIDC audience at runtime from `https://test.pypi.org/_/oidc/audience`, falling
    back to the literal `testpypi` on a failed/malformed fetch.
  - Mints the Actions OIDC token via `ACTIONS_ID_TOKEN_REQUEST_URL`/`ACTIONS_ID_TOKEN_REQUEST_TOKEN`.
  - Decodes the JWT payload (base64url, padded to a multiple of 4) and prints exactly four
    whitelisted claims via `jq`: `sub`, `repository`, `workflow_ref`, `environment`.
  - Carries step-level `continue-on-error: true` (distinct from the pre-existing job-level flag
    at `release.yml:147`, which was not touched).
- Diff is additive-only: `git diff --stat` on `release.yml` showed 36 insertions, 0 deletions,
  one file.
- Plan checklist items for Phase 1 (tasks and verification) checked off; Phase 1 heading
  advanced `[NOT STARTED]` -> `[IN PROGRESS]` -> `[COMPLETED]`.
- Phase-end handoff written to
  `specs/161_fix_testpypi_trusted_publisher/handoffs/phase-1-handoff-20260826T011646Z.md`.

## Decisions

- Followed the plan's step shape verbatim, including the deliberate choices it calls out
  (runtime-resolved audience with hardcoded fallback, `|| echo ''` inside the audience command
  substitution, `set -euo pipefail`, four-claim whitelist only).
- Committed in two steps: the workflow change itself (`task 161 phase 1: add OIDC claims
  diagnostic step to publish-testpypi`), then the plan-checklist/handoff bookkeeping (`task 161
  phase 1: mark plan checklist complete and add phase handoff`).

## Plan Deviations

- None (implementation followed plan).

## Impacts

- `publish-testpypi`'s runtime behavior is otherwise unchanged; the new step cannot fail the
  job (step-level `continue-on-error: true`) and does not affect `publish-pypi`, `build`, or the
  shared `dist` artifact.
- The dependent task `harden_release_ci_testpypi_gate` can re-read `release.yml` cleanly: no
  `verify-testpypi` job, no removal or weakening of the job-level `continue-on-error` at line
  147, no preflight assertions or confirmation gates were added.
- TestPyPI publishing will continue to fail with `invalid-publisher` until Phase 2 (trusted
  publisher registration) is completed by the user — this diagnostic step does not fix the
  registration itself, only makes the next failure legible.

## Follow-ups

- **User action required — Phase 2**: register (or correct) the GitHub Actions trusted
  publisher for `model-checker` on test.pypi.org with Owner `benbrastmckie`, Repository
  `ModelChecker`, Workflow name `release.yml`, Environment name `testpypi`. Full instructions
  and fallback ladder are in the plan's Phase 2 section
  (`plans/01_fix-testpypi-trusted-publisher.md:250`).
- **User action required — Phase 3**: push a real `v*` tag and confirm `publish-testpypi` goes
  green, comparing the diagnostic step's printed claims against the Phase 2 registration. See
  the plan's Phase 3 section (`plans/01_fix-testpypi-trusted-publisher.md:348`).
- This task cannot be marked `[COMPLETED]` until both user gates are done; it is expected to sit
  in a blocked/awaiting-user state until then.

## References

- `specs/161_fix_testpypi_trusted_publisher/plans/01_fix-testpypi-trusted-publisher.md`
- `specs/161_fix_testpypi_trusted_publisher/reports/01_fix-testpypi-trusted-publisher.md`
- `specs/161_fix_testpypi_trusted_publisher/handoffs/phase-1-handoff-20260826T011646Z.md`
- `.github/workflows/release.yml`
- `.github/RELEASE_SETUP.md`
