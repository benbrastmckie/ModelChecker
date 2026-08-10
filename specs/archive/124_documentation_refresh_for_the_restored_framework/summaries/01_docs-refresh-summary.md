# Implementation Summary: Task #124

**Completed**: 2026-07-24
**Duration**: ~2 hours

## Overview

Refreshed the seven scoped documentation files so they describe the restored, green-gated
ModelChecker framework state accurately. Ground truth (four registered theories, restored
`builder`/`iterate`, standalone `oracle/` tree excluded from the wheel, no first-order
quantification in logos) was established from source before any prose was edited. All six plan
phases completed; several plan-anticipated defects (the root README jupyter link/quick-start,
the `code/scripts/README.md` QUANTIFIER_SOLVERS link) were found already resolved on disk and
were verified rather than re-edited.

## What Changed

- `README.md` — fixed a stale "19 operators" count to the verified "18 operators" (two places);
  repointed four dead relative links (`code/docs/DEVELOPMENT.md` x2, the logos notebooks link,
  `docs/architecture/ARCHITECTURE.md`, `code/MAINTENANCE.md` x2) to their existing on-disk
  equivalents (`docs/installation/DEVELOPER_SETUP.md`, `code/docs/development/README.md`,
  `code/docs/core/ARCHITECTURE.md`, `code/docs/core/CODE_STANDARDS.md`,
  `code/src/model_checker/theory_lib/README.md`). Verified the jupyter `[jupyter]` extra and
  jupyter link were already correct.
- `CLAUDE.md` (repo root) — fixed both `cd Code` → `cd code` casing occurrences, corrected the
  stale "Main Repository" path, and added the standalone `oracle/` tree to the Project Structure
  diagram. This file is edited on disk but is not git-tracked (`**/CLAUDE.md` is gitignored
  repo-wide, predating this task), so the change could not be included in a commit.
- `code/README.md` — fixed `cd ModelChecker/Code` → `cd ModelChecker/code` casing, fixed the same
  stale "19 operators" count, and repointed two dead `github.com/.../blob/master/...` links
  (`docs/usage/COMPARE_THEORIES.md`, which never existed, and `docs/DEVELOPMENT.md`) to
  `docs/usage/TOOLS.md` and `code/docs/development/README.md` respectively.
- `code/scripts/README.md` — no edit needed; verified the `../../docs/theory/QUANTIFIER_SOLVERS.md`
  link already resolves (592-line file present on disk).
- `docs/usage/SEMANTICS.md` — no edit needed; all 18 first-order/quantifier hits are legitimate
  Z3-constraint-language usage (`ForAll`/`Exists` API calls), none imply logos still exposes
  first-order quantification.
- `code/CHANGELOG.md` — added a `## [1.3.0] - 2026-07-24` release entry with a "Framework
  Restoration" subsection covering the package-identity restore, the four-theory set, the
  first-order removal from logos, and the standalone oracle relocation, following the existing
  Keep-a-Changelog structure (the pre-existing Issue #73 package-loading entries now nest under
  the same release).
- `specs/ROADMAP.md` — added a "Durable Decisions" section seeding the package-identity decision
  (ships as `model_checker` with the four registered theories; oracle kept standalone/unpacked),
  leaving the existing placeholder sections intact.

## Decisions

- Repointed dead links to existing, topically-matching on-disk files rather than removing them or
  creating new files, consistent with the plan's non-goal against restructuring beyond accuracy
  corrections.
- Where a plan-anticipated defect (jupyter link, QUANTIFIER_SOLVERS link) was found already
  resolved on disk, verified and recorded rather than making a speculative edit.
- Left `code/MANIFEST.in` unmodified per the plan's explicit non-goal; confirmed no mismatch
  against real paths during Phase 1's read-only cross-check.

## Plan Deviations

- **Task 3.3** (`code/scripts/README.md` QUANTIFIER_SOLVERS link) skipped: the linked file exists
  on disk (592 lines) and the relative link already resolves; not dead as of this dispatch.
- **Task 4.3** (`docs/usage/SEMANTICS.md` stale-reference edit) skipped: all first-order/quantifier
  hits found are legitimate Z3-constraint-language usage; no stale removed-logos references
  existed to correct.

## Verification

- Build: N/A (documentation-only task)
- Tests: N/A (documentation-only task)
- Files verified: Yes — all edited files confirmed to exist and contain the intended changes; a
  full relative-link scan was run across all seven scoped files (see Notes for one pre-existing
  exception).

## Notes

- `CLAUDE.md` is excluded from git tracking by a pre-existing `**/CLAUDE.md` rule in `.gitignore`
  (confirmed to predate this task via `git log --all -- CLAUDE.md`, which returns no history).
  The file was edited on disk as required by the task's file scope, but the change is not part of
  any git commit for this task and will not appear in `git diff` against HEAD.
- One pre-existing, unrelated dead-link pair was found in `code/CHANGELOG.md`'s historical
  Issue #73 `## Links` section (`specs/plans/issue_73_package_loading_refactor.md` and
  `docs/migration/package_loading_v2.md`, both from an older, already-merged change entry). Left
  unedited per the non-goal against restructuring beyond this task's scope; flagged here for a
  future documentation pass.
- `code/shell.nix` and `flake.nix`/`flake.lock` were observed changing in the working tree during
  this session (owned by a concurrent agent) and were never staged or touched by this task's
  commits.
