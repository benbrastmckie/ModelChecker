# Research Report: Task #147

**Task**: 147 - Correct stale release and environment docs
**Started**: 2026-08-11T00:00:00Z
**Completed**: 2026-08-11T00:00:00Z
**Effort**: Small (4 files, mostly line-level fixes; one file needs a rewrite-or-delete decision)
**Dependencies**: None
**Sources/Inputs**: - Codebase (`.github/workflows/`, `code/docs/`, `docs/installation/`), specs/reviews/review-20260811.md, specs/archive/125_release_engineering_and_pypi_rehearsal/
**Artifacts**: - This report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- All four drift claims in the task description are verified accurate against the current tree;
  every cited line number and "does not exist" claim checked out exactly.
- `.github/workflows/README.md` is unsalvageable as a maintained doc: every substantive claim in
  it (secret name, test matrix, directory casing, `run_update.py`, manual `twine upload`) is
  wrong, and `.github/RELEASE_SETUP.md` already covers the same ground accurately. **Recommend
  deletion**, not rewrite — see Decisions below for the reasoning.
- `.github/RELEASE_SETUP.md` needs exactly three corrections: one matrix-description line, two
  `specs/archive/` path segments. Everything else in the file (the five-job pipeline description,
  OIDC setup steps, troubleshooting) is already accurate and should not be touched.
- `code/docs/development/ENVIRONMENT_SETUP.md` needs the two fixes named in the task (line 18
  Python floor, line 103 `shell.nix` reference), plus has an additional, unlisted casing bug
  (`cd ModelChecker/Code`, lowercase `code/` is correct) at lines 39 and 100 in the same file —
  flagged here for the implementer to decide whether to fold in while already editing this file.
- `docs/installation/BASIC_INSTALLATION.md` has no existing NixOS verification content to
  conflict with — the recipe is a pure addition under the existing `## NixOS Installation`
  section (or a new subsection immediately after it), not a rewrite of the `nix develop` guidance.
- **Out-of-scope but material finding**: `run_update.py` (and a `test_update.py` sibling) is
  referenced as the "recommended"/"automated" release path in at least six more files not named
  in this task — `code/README.md`, `code/docs/development/README.md`,
  `code/docs/development/PACKAGE_TESTING.md`, `code/docs/development/TEST_RELEASES.md`,
  `code/docs/development/PYPI_RELEASE_GUIDE.md`, `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`,
  and `docs/installation/DEVELOPER_SETUP.md`. None of these scripts exist anywhere in the repo.
  This task's scope note restricts fixes to the four named files; this is recorded here as a
  planning input for a likely follow-up task rather than fixed now.

## Context & Scope

Task 147 is a documentation-only correction task (task_type: markdown) covering four files
surfaced by `specs/reviews/review-20260811.md` (issues 2, 14, 16, plus item 4's NixOS
verification-recipe addition, which is not numbered as a review issue but is specified directly
in the task description). The scope note explicitly excludes touching `release.yml` or
`flake.nix`; any doc/code disagreement where the code looks wrong is to be recorded, not fixed,
here. All four target files and their line-number claims were read and cross-checked directly
against `.github/workflows/release.yml`, `code/pyproject.toml`, and the filesystem.

## Findings

### Codebase Patterns

**`.github/workflows/release.yml`** (ground truth, not to be modified) — 198 lines, 5 jobs in
this exact order: `test-and-release` (matrix `os: [ubuntu-latest, macos-latest, windows-latest]`,
`python-version: ['3.10', '3.11', '3.12']` at line 25, comment "Matches requires-python floor in
pyproject.toml"), `build`, `publish-testpypi`, `publish-pypi`, `github-release`. This exactly
matches `.github/RELEASE_SETUP.md`'s "Workflow Overview" section's five-job description (lines
49-72) — that section is accurate and needs no change.

**`code/pyproject.toml:30`**: `requires-python = ">=3.10"` — confirms `ENVIRONMENT_SETUP.md:18`'s
"Python: 3.8 or higher" is stale (task claim verified) and confirms
`BASIC_INSTALLATION.md`'s existing "Python 3.10 or higher" (lines 15, 35, 50) is already correct
and should be left as-is / used as the reference wording for other fixes in this task.

**`.github/workflows/README.md`** (full file read, 82 lines) — every substantive claim is wrong:
- Line 10/53: "Python 3.8 and 3.12" — actual matrix is 3.10/3.11/3.12 (three, not two, versions).
- Lines 16-27: `python code/run_update.py` presented as "Recommended" — `find . -name
  run_update.py` returns zero hits repo-wide.
- Lines 42-47: `PYPI_API_TOKEN` GitHub secret instructions — `RELEASE_SETUP.md` line 46 states
  explicitly "No repository secrets are required for either environment — Trusted Publishing uses
  the workflow's OIDC identity, not a stored credential." Direct contradiction.
- Line 79: `cd Code` — the repo's implementation directory is lowercase `code/` (confirmed via
  `CLAUDE.md`'s documented structure and the live tree).
- Lines 78-81: manual `twine upload dist/*X.Y.Z*` flow — the shipped pipeline publishes via
  `pypa/gh-action-pypi-publish@release/v1` under OIDC (`publish-pypi` job), never via a manual
  local `twine upload`. This isn't just stale, it actively contradicts the Trusted Publishing
  design (a manual upload would need a credential that no longer exists in any documented
  workflow).
- Line 61: "No duplicates: Only one workflow runs per release" — technically still true (single
  `release.yml` file), but this is the only accurate-sounding claim left once everything else is
  wrong, and it adds nothing `RELEASE_SETUP.md` doesn't already state more precisely.

Cross-reference check: no other tracked file links to `.github/workflows/README.md` by path
except task-management artifacts (`specs/TODO.md`, `specs/reviews/review-20260811.md`, and
already-archived task reports/summaries under `specs/archive/`). Deleting it breaks no live
in-repo cross-reference.

**`.github/RELEASE_SETUP.md`** (full file read, 179 lines) — the task's claims are precisely
located:
- Line 54: `**Tests**: Python 3.8 and 3.12 on all platforms` inside the "Workflow Overview"
  numbered list item 1. Needs "3.8 and 3.12" -> "3.10, 3.11, and 3.12".
- Line 77: `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` — file has
  moved to `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`
  (confirmed present at the archive path; absent at the pre-archive path).
  `no-task-references-in-deliverables.md` does not block this — `specs/**` paths are explicitly
  exempted from the "no task number" rule, so citing the numbered archive directory is fine.
- Line 146: `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/` — same fix, and the
  `rehearsal/` subdirectory is confirmed present at the archive path.
- Everything else in the file — the Trusted Publishing / OIDC setup steps, the five-job workflow
  description, the troubleshooting table, the dry-run test-tag recipe, the
  `.claude/rules/pr-prohibition.md` citations gating manual tag pushes — reads as accurate against
  the live `release.yml` and should not be touched.

**`code/docs/development/ENVIRONMENT_SETUP.md`** (full file read, 465 lines) — task's two claims
confirmed exactly:
- Line 18: `**Python**: 3.8 or higher (check pyproject.toml for specific version)` — stale against
  `requires-python = ">=3.10"`.
- Line 103: `ls shell.nix .envrc  # Should exist for NixOS support` — `find . -maxdepth 2 -iname
  "shell.nix"` returns nothing repo-wide; the file was replaced by `flake.nix` (present at repo
  root) and `.envrc` (present, contains `use flake`).
- Additional drift found but **not named in the task description**: lines 39 and 100 both read
  `cd ModelChecker/Code` (wrong casing, same class of bug the task calls out for
  `.github/workflows/README.md`). Since the task scope is explicitly the two named lines, this is
  recorded for the implementer's judgment rather than treated as in-scope by default — but it is
  in the same file already being edited, so folding it in is low-marginal-cost.
- Section "2. Development Shell" (lines 106-116) describes `nix-shell` / "The shell.nix file
  automatically: ..." — this describes the now-removed `shell.nix` workflow rather than
  `flake.nix`/`nix develop`. This is adjacent to the line-103 fix (same root cause: shell.nix no
  longer exists) but the task only names line 103 specifically; flagging for implementer judgment
  on how far to extend the shell.nix cleanup within this file.

**`docs/installation/BASIC_INSTALLATION.md`** (full file read, 227 lines) — the existing
`## NixOS Installation` section (lines 159-182) is accurate for its stated purpose (development
via `nix develop`) and should not be rewritten. There is currently no verification-of-published-
artifact content anywhere in the file. The task's empirically-verified recipe (venv install +
`LD_LIBRARY_PATH` pointed at `nixpkgs#stdenv.cc.cc.lib`) has zero existing counterpart to
reconcile against — it is a pure addition. Natural placement is either a new subsection appended
to `## NixOS Installation` (e.g. "### Verifying a Published Install") or as its own top-level
section directly after it, both immediately after the existing `nix develop` guidance so the
"day-to-day use" vs "one-off verification" framing from the task description reads naturally in
sequence.

### External Resources

Not applicable — this is a pure codebase-consistency correction task; no external documentation
or best-practices research was needed. The Trusted Publishing (OIDC) mechanism referenced in
`RELEASE_SETUP.md` is already correctly documented there and is out of scope to re-verify against
PyPI's own docs per the task's scope note (release.yml itself is off-limits to touch).

### Recommendations

1. **`.github/workflows/README.md`: delete.** The task offers both options, but rewrite is the
   weaker choice here: every single claim in the file is wrong (not partially stale), a fully
   accurate replacement (`RELEASE_SETUP.md`) already exists and is actively maintained, and
   nothing links to this file except task-management history. Keeping two release docs in sync
   going forward is exactly the failure mode that produced this task in the first place — this
   file drifted for an entire release-engineering effort (task 125) without being touched.
   Recommended replacement: delete the file, or reduce it to a one-line pointer (e.g. "See
   `../RELEASE_SETUP.md` for the release process.") if directory convention prefers a README to
   always exist under `.github/workflows/`. Since the file's practical purpose (a GitHub-rendered
   entry point when browsing `.github/workflows/` on the web UI) is served either way, the
   one-line-pointer variant is slightly safer than outright deletion and equally cheap to
   maintain — record this as an open implementation choice rather than a firm recommendation.
2. **`.github/RELEASE_SETUP.md`**: three isolated string fixes (matrix wording at line 54, two
   `specs/archive/` path insertions at lines 77 and 146). No structural changes needed.
3. **`code/docs/development/ENVIRONMENT_SETUP.md`**: fix line 18 (Python floor -> "3.10 or
   higher") and line 103 (drop the `shell.nix` existence check, or replace with a check for
   `flake.nix`/`.envrc` only). Implementer should decide whether to also touch the two `cd
   ModelChecker/Code` casing bugs and the shell.nix-era "Development Shell" prose in the same
   file (flagged above, not in the task's named scope).
4. **`docs/installation/BASIC_INSTALLATION.md`**: add the verification recipe as new content
   after the existing `## NixOS Installation` section, framed explicitly as "verify a published
   install works on NixOS" rather than as install guidance — the task description's framing
   should be preserved verbatim in the new prose (`nix develop` remains the right path for
   ordinary use; the venv+`LD_LIBRARY_PATH` recipe is a one-off verification tool, primarily
   useful for post-publish checks). Include the `PIP_USER=0` rationale (this host's
   `~/.config/pip/pip.conf` sets `install.user=true` globally, which a venv install rejects) so
   the recipe isn't a mystery flag to a future reader.

## Decisions

- No irreversible decisions were made during research; the task explicitly leaves the
  rewrite-vs-delete choice for `.github/workflows/README.md` to be made during planning/
  implementation. This report recommends deletion (or a one-line pointer stub) over rewrite, with
  reasoning given above, but does not treat this as a foreclosed decision.
- Confirmed all four line-number/content claims in the task description are accurate against the
  current tree — no re-scoping of the task is needed.

## Risks & Mitigations

- **Risk**: Deleting `.github/workflows/README.md` outright, with no stub, could look like an
  accidental content loss to a future contributor browsing the directory on GitHub's web UI.
  **Mitigation**: prefer the one-line-pointer variant noted in Recommendation 1, or note the
  deletion explicitly in the commit message / CHANGELOG.
- **Risk**: Folding the unlisted `cd ModelChecker/Code` casing fix and shell.nix-era prose into
  `ENVIRONMENT_SETUP.md` beyond the two named lines could be seen as scope creep beyond the task
  description. **Mitigation**: treated as implementer's judgment call above, not a required fix;
  either choice is defensible and low-risk since it's the same file and same root cause.
- **Risk**: The out-of-scope `run_update.py` drift spans six additional files and represents a
  larger, structurally identical problem to what this task fixes. Leaving it unaddressed means
  a reader following `code/README.md`'s "Production release" instructions (`python
  code/run_update.py`) will hit the same failure mode this task is fixing elsewhere.
  **Mitigation**: explicitly out of this task's named scope (four specific files); recorded here
  so a follow-up task can be spawned rather than silently left undiscovered. No code change or
  doc edit was made to these six files in this research pass.

## Context Extension Recommendations

- **Topic**: repo-wide `run_update.py`/`test_update.py` reference cleanup.
- **Gap**: Six files beyond this task's four-file scope (`code/README.md`,
  `code/docs/development/README.md`, `code/docs/development/PACKAGE_TESTING.md`,
  `code/docs/development/TEST_RELEASES.md`, `code/docs/development/PYPI_RELEASE_GUIDE.md`,
  `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`, `docs/installation/DEVELOPER_SETUP.md`)
  describe `run_update.py`/`test_update.py` as the recommended/automated release mechanism. Both
  scripts are absent from the repository (`find . -iname "run_update.py"` /
  `-iname "test_update.py"` both return nothing). This is the same failure mode issue 2 in the
  review flagged for `.github/workflows/README.md`, just not yet inventoried as a task.
- **Recommendation**: file a follow-up markdown/documentation task (or fold into a broader
  release-doc audit) to either restore a real `run_update.py` script or strip all six files' claims
  down to the actual manual/CI release process described in `.github/RELEASE_SETUP.md`.

## Appendix

- Files read in full: `.github/workflows/README.md`, `.github/RELEASE_SETUP.md`,
  `code/docs/development/ENVIRONMENT_SETUP.md`, `docs/installation/BASIC_INSTALLATION.md`.
- Commands run: `find . -name run_update.py`, `find . -maxdepth 2 -iname shell.nix`, `grep -n
  requires-python code/pyproject.toml`, `sed -n '1,40p' .github/workflows/release.yml`, `ls
  specs/archive/125_release_engineering_and_pypi_rehearsal/`, `grep -rln "workflows/README\|
  RELEASE_SETUP\|run_update" --include="*.md" .`.
- Source: `specs/reviews/review-20260811.md` issues 2, 3 (context only — GitHub Environments/OIDC
  setup, out of scope), 14, 16.
