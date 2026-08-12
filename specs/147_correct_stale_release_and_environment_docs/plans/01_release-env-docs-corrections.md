# Implementation Plan: Task #147

- **Task**: 147 - Correct stale release and environment docs
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/147_correct_stale_release_and_environment_docs/reports/01_release-env-docs-drift.md
- **Artifacts**: plans/01_release-env-docs-corrections.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Four documentation files have drifted from the shipped release pipeline and the current Nix/Python
environment. This plan corrects them file-by-file: `.github/workflows/README.md` is reduced to a
one-line pointer (every substantive claim in it is wrong and `.github/RELEASE_SETUP.md` already
covers the same ground accurately); `.github/RELEASE_SETUP.md` gets three isolated string fixes;
`code/docs/development/ENVIRONMENT_SETUP.md` gets its Python floor, directory casing, and
`shell.nix`-era Nix prose brought in line with `pyproject.toml` and `flake.nix`; and
`docs/installation/BASIC_INSTALLATION.md` gains a new NixOS post-publish verification recipe.
Definition of done: no claim in any of the four files contradicts `release.yml`,
`code/pyproject.toml`, or the live filesystem, and the out-of-scope `run_update.py` drift is
recorded for a follow-up without being fixed here.

This is a documentation-only task. `.github/workflows/release.yml` and `flake.nix` are ground
truth and MUST NOT be modified — where a doc and the code disagree, the doc is wrong.

### Research Integration

Report `01_release-env-docs-drift.md` verified every line-number and "does not exist" claim in the
task description against the live tree; none required re-scoping. Key findings carried into this
plan:

- `release.yml:25` pins `python-version: ['3.10', '3.11', '3.12']` with a comment tying it to
  `requires-python`. Both README.md and RELEASE_SETUP.md say "3.8 and 3.12".
- `RELEASE_SETUP.md:46` states no repository secrets are required (OIDC Trusted Publishing),
  directly contradicting README.md's `PYPI_API_TOKEN` instructions.
- `find . -name run_update.py` returns zero hits repo-wide.
- No tracked file links to `.github/workflows/README.md` except task-management artifacts under
  `specs/`, so changing it breaks no live cross-reference.
- The `specs/125_release_engineering_and_pypi_rehearsal/` paths cited at RELEASE_SETUP.md lines 77
  and 146 both resolve correctly once `archive/` is inserted; the `rehearsal/` subdirectory and
  `PUBLISH-CHECKLIST.md` are both confirmed present at the archive path.
- `docs/installation/BASIC_INSTALLATION.md` already states "Python 3.10 or higher" (lines 15, 35,
  50) — that wording is correct and is the reference phrasing for the ENVIRONMENT_SETUP.md fix.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided).

## Decisions

Two decisions the task description explicitly left open are resolved here so the implementer does
not re-litigate them.

### Decision 1: `.github/workflows/README.md` — reduce to a pointer stub, do not delete outright

**Resolution**: replace the file's entire contents with a short pointer stub (heading plus a
one-line pointer to `../RELEASE_SETUP.md`). Do NOT rewrite it as a maintained second release doc,
and do NOT `git rm` it.

**Reasoning**: rewriting is the worst option — keeping two independently-maintained release docs
in sync is precisely the failure mode that produced this task, and this file drifted through an
entire release-engineering effort without being touched. Between deleting and stubbing, stubbing
wins narrowly: the file's only real function is as a GitHub web-UI entry point when browsing
`.github/workflows/`, a stub serves that function at zero maintenance cost, and an outright
deletion reads as accidental content loss to a contributor who does not check the commit history.
A stub carries no claims, so it cannot drift.

### Decision 2: `ENVIRONMENT_SETUP.md` — include the unlisted casing and `shell.nix`-era fixes

**Resolution**: in scope. Fix every `ModelChecker/Code` casing occurrence and every `shell.nix` /
`nix-shell` reference in the file, not just the two lines the task description names.

**Reasoning**: the unnamed occurrences share a root cause with the named ones (`shell.nix` no
longer exists; the directory is lowercase `code/`) and sit in the same file already being edited.
Fixing line 103's `ls shell.nix .envrc` while leaving the very next subsection instructing readers
to run `nix-shell` and explaining what "the shell.nix file automatically" does would produce a
file that is internally contradictory and still broken for its primary audience. The marginal cost
is a handful of additional line edits with no new risk surface. Confirmed occurrence inventory
(hypothesis — see Phase 3's Scope Hypothesis):

- `ModelChecker/Code` casing: lines 39, 100, 131, 308 (**four**, not the two the research report
  named — the report listed only 39 and 100)
- `shell.nix` / `nix-shell`: lines 103, 110, 112, 336, 337, 423

## Goals & Non-Goals

**Goals**:

- Eliminate every false claim in `.github/workflows/README.md` by reducing it to a pointer stub.
- Correct the three verified inaccuracies in `.github/RELEASE_SETUP.md` (matrix wording, two
  archive paths) and touch nothing else in that file.
- Bring `code/docs/development/ENVIRONMENT_SETUP.md` in line with `requires-python = ">=3.10"`,
  the lowercase `code/` directory, and the `flake.nix` / `nix develop` workflow.
- Add a NixOS post-publish verification recipe to `docs/installation/BASIC_INSTALLATION.md`,
  framed as a verification procedure rather than an install path.
- Record the out-of-scope `run_update.py` drift (seven additional files) in the implementation
  summary so a follow-up task can be filed.

**Non-Goals**:

- Modifying `.github/workflows/release.yml` or `flake.nix`. These are ground truth for this task.
- Fixing the `run_update.py` references in `code/README.md`,
  `code/docs/development/README.md`, `code/docs/development/PACKAGE_TESTING.md`,
  `code/docs/development/TEST_RELEASES.md`, `code/docs/development/PYPI_RELEASE_GUIDE.md`,
  `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`, or `docs/installation/DEVELOPER_SETUP.md`.
  Recorded, not fixed.
- Rewriting `.github/RELEASE_SETUP.md`'s OIDC setup steps, five-job pipeline description, or
  troubleshooting table. All verified accurate.
- Rewriting the existing `## NixOS Installation` section's `nix develop` guidance in
  `BASIC_INSTALLATION.md`. That guidance stays as the recommended path for ordinary use.
- Creating the follow-up task. Recording the finding is in scope; filing the task is not.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drift between planning and implementation, so edits land in the wrong place | M | M | Every phase anchors edits on quoted content strings, not line numbers; line numbers below are navigational hints only. Re-grep before each edit. |
| Stubbing `.github/workflows/README.md` reads as accidental content loss | L | M | Stub retains a heading and an explicit pointer sentence; the commit message states the reduction and its reason. |
| The `ENVIRONMENT_SETUP.md` scope expansion (Decision 2) is read as scope creep | L | L | Decision 2 records the reasoning explicitly and the implementation summary restates it. Same file, same root cause, no new files touched. |
| The `specs/archive/125_...` path citations in a non-`specs/` deliverable trip the task-reference lint | M | L | Verified non-issue: `TASK_PATTERN` in `scripts/lib/task-reference-patterns.sh` matches a literal `task`/`tasks` token adjacent to a number. A bare directory name like `125_release_engineering_and_pypi_rehearsal` contains no such token and does not match. `check-task-references.sh` currently reports no `RELEASE_SETUP.md` finding. |
| The BASIC_INSTALLATION.md recipe is mistaken for a recommended NixOS install path | M | M | The subsection opens by stating it is a verification procedure and that `nix develop` remains correct for ordinary use; it is placed after, not instead of, the existing guidance. |
| Editing `release.yml` or `flake.nix` by reflex while "fixing the mismatch" | H | L | Stated as a Non-Goal and repeated in the Phase 2 and Phase 3 task lists. Phase 5 verifies both files are unmodified in the diff. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1-4 each own exactly one file and
have no shared state, so they are fully independent; Phase 5 is a cross-cutting verification pass
that requires all four.

---

### Phase 1: Reduce `.github/workflows/README.md` to a pointer stub [COMPLETED]

**Goal**: Remove every false claim from the file while preserving a GitHub web-UI entry point for
`.github/workflows/`.

**Tasks**:

- [ ] Read `.github/workflows/README.md` in full (81 lines) to confirm nothing worth preserving
      was missed by the research pass.
- [ ] Replace the entire file contents with a stub: a top-level heading and a single pointer
      sentence directing readers to `../RELEASE_SETUP.md` for the release process. Suggested
      body (adjust wording, keep it claim-free):

      # GitHub Workflows

      The release pipeline is documented in [RELEASE_SETUP.md](../RELEASE_SETUP.md).

- [ ] Confirm the stub asserts nothing about the Python matrix, secrets, directory casing,
      `run_update.py`, or `twine`. A stub that reintroduces any claim has failed this phase.
- [ ] Verify the relative link target resolves: `.github/RELEASE_SETUP.md` exists relative to
      `.github/workflows/`.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: prose

**Verification**:

- `wc -l .github/workflows/README.md` returns a small number (roughly 1-5 lines).
- `grep -inE 'PYPI_API_TOKEN|run_update|twine|3\.8|cd Code' .github/workflows/README.md` returns
  no matches.
- `test -f .github/RELEASE_SETUP.md` succeeds (link target exists).

**Files to modify**:

- `.github/workflows/README.md` - full-content replacement with a pointer stub.

---

### Phase 2: Correct the three verified inaccuracies in `.github/RELEASE_SETUP.md` [COMPLETED]

**Goal**: Fix the stale test-matrix wording and the two pre-archive `specs/` paths, changing
nothing else in the file.

**Tasks**:

- [ ] Fix the matrix wording (near line 54, inside the "Workflow Overview" numbered list item 1).
      Current text reads `cross-platform test matrix (Ubuntu/macOS/Windows, Python 3.8 and
      3.12)`. Change `Python 3.8 and 3.12` to `Python 3.10, 3.11, and 3.12` to match
      `release.yml:25`. Note the phrase wraps across a line break in the source — match on the
      content, not on a single line.
- [ ] Fix the archive path near line 77: insert `archive/` so
      `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` becomes
      `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`.
- [ ] Fix the archive path near line 146: insert `archive/` so
      `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/` becomes
      `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/`.
- [ ] Make no other edits. The OIDC/Trusted Publishing setup steps, the five-job pipeline
      description, the troubleshooting table, the dry-run test-tag recipe, and the
      `pr-prohibition.md` citations were all verified accurate and are out of scope.
- [ ] Do NOT modify `.github/workflows/release.yml`.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts **exactly three** edits in this file and that everything
else is accurate. Confirm at implementation time before closing the phase:
`grep -nE '3\.8' .github/RELEASE_SETUP.md` returns no matches, and
`grep -n 'specs/125_' .github/RELEASE_SETUP.md` returns no matches (all occurrences now carry the
`archive/` segment). If either grep returns an occurrence not enumerated above, the three-edit
hypothesis was an undercount — fix the additional occurrence and record the correction in the
implementation summary rather than silently exceeding the stated scope.

**Verification**:

- `grep -n '3\.10, 3\.11, and 3\.12' .github/RELEASE_SETUP.md` matches.
- `grep -n 'specs/125_' .github/RELEASE_SETUP.md` returns nothing.
- `ls specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` and
  `ls -d specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` both succeed,
  confirming the corrected paths resolve.
- `git diff --stat .github/workflows/release.yml` shows no change.

**Files to modify**:

- `.github/RELEASE_SETUP.md` - three isolated string fixes.

---

### Phase 3: Correct Python floor, directory casing, and Nix prose in `ENVIRONMENT_SETUP.md` [NOT STARTED]

**Goal**: Bring the file in line with `requires-python = ">=3.10"`, the lowercase `code/`
directory, and the `flake.nix` / `nix develop` workflow, per Decision 2.

**Tasks**:

- [ ] Fix line 18: `**Python**: 3.8 or higher (check pyproject.toml for specific version)` becomes
      `**Python**: 3.10 or higher (see `requires-python` in `code/pyproject.toml`)`. Match the
      "3.10 or higher" wording already used in `docs/installation/BASIC_INSTALLATION.md`.
- [ ] Fix every `cd ModelChecker/Code` occurrence to `cd ModelChecker/code` (lines 39, 100, 131 —
      confirm the inventory first, see Scope Hypothesis).
- [ ] Fix the `pwd  # Should show .../ModelChecker/Code` comment near line 308 to lowercase
      `code`.
- [ ] Fix line 103: replace `ls shell.nix .envrc  # Should exist for NixOS support` with a check
      against files that actually exist — `ls flake.nix .envrc` at the repository root (note
      `flake.nix` and `.envrc` live at the repo root, not under `code/`, so verify the working
      directory the surrounding snippet establishes and adjust the path or the `cd` accordingly).
- [ ] Rewrite the `### 2. Development Shell` subsection (lines 106-116): replace `nix-shell` with
      `nix develop`, and replace the `# The shell.nix file automatically:` comment block with an
      equivalent statement about `flake.nix`. Preserve the three bullet points describing what the
      shell provides (PYTHONPATH, dependencies, executable dev scripts) — verify each against
      `flake.nix` before restating it, and drop any bullet the flake does not actually do.
- [ ] Fix the remaining `nix-shell` references near lines 336-337 (`# If not in nix-shell, enter
      it` / `nix-shell`) and line 423 (`source venv/bin/activate  # or enter nix-shell`) to refer
      to `nix develop`.
- [ ] Do NOT modify `flake.nix`. If the flake does not do something the doc claims, correct the
      doc.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts a specific occurrence inventory — **four** `ModelChecker/Code`
casing sites (lines 39, 100, 131, 308) and **six** `shell.nix`/`nix-shell` sites (lines 103, 110,
112, 336, 337, 423). Note this already contradicts the research report, which named only two
casing sites; treat the counts above as the current best hypothesis, not a fact. Confirm at
implementation time by re-running
`grep -nE 'ModelChecker/Code|shell\.nix|nix-shell' code/docs/development/ENVIRONMENT_SETUP.md`
BEFORE editing (to fix the true inventory) and AFTER editing (expecting zero matches). Record any
divergence from the stated counts in the implementation summary.

**Verification**:

- `grep -nE 'ModelChecker/Code|shell\.nix|nix-shell' code/docs/development/ENVIRONMENT_SETUP.md`
  returns no matches.
- `grep -n '3\.8' code/docs/development/ENVIRONMENT_SETUP.md` returns no matches in the
  requirements context.
- `grep -n 'requires-python' code/pyproject.toml` still shows `>=3.10`, confirming the doc now
  agrees with it.
- `test -f flake.nix && test -f .envrc` succeeds, confirming the replacement `ls` check names
  files that exist.
- `git diff --stat flake.nix` shows no change.

**Files to modify**:

- `code/docs/development/ENVIRONMENT_SETUP.md` - Python floor, four casing fixes, and the
  `shell.nix` to `flake.nix` / `nix develop` migration across the NixOS sections.

---

### Phase 4: Add the NixOS post-publish verification recipe to `BASIC_INSTALLATION.md` [NOT STARTED]

**Goal**: Document the empirically-verified venv + `LD_LIBRARY_PATH` recipe for confirming a
published wheel runs on NixOS, framed as a verification procedure and not as an install path.

**Tasks**:

- [ ] Insert a new `### Verifying a Published Release on NixOS` subsection at the END of the
      existing `## NixOS Installation` section — after the `For more details on NixOS development,
      see [Developer Setup](DEVELOPER_SETUP.md#nixos-development).` line (near line 182) and
      before `## Optional: Nix on Other Platforms` (near line 184).
- [ ] Do NOT modify the existing `## NixOS Installation` prose or its `nix develop` block. This is
      a pure addition.
- [ ] Open the subsection with an explicit framing sentence stating this is a verification
      procedure for a published artifact, and that `nix develop` above remains the right path for
      ordinary NixOS use.
- [ ] Include the recipe verbatim in a bash code block:

      python3 -m venv testvenv
      PIP_USER=0 ./testvenv/bin/pip install model-checker
      LD_LIBRARY_PATH=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib \
        ./testvenv/bin/model-checker <project>/examples.py

- [ ] Explain `PIP_USER=0`: it is required when `~/.config/pip/pip.conf` sets
      `install.user = true` globally, because a virtual environment rejects a user-site install.
      Write this as a general condition a reader can check on their own machine, not as a claim
      about one specific host.
- [ ] Explain `LD_LIBRARY_PATH`: the `z3-solver` wheel bundles a prebuilt `libz3.so` that cannot
      resolve `libstdc++.so.6` on NixOS. State explicitly that this is the SOLE blocker the recipe
      works around — nothing else about the published wheel needs special handling on NixOS.
- [ ] Note that `testvenv/` should be removed when the check is finished.
- [ ] Confirm the surrounding heading levels are consistent (`###` under the existing `##
      NixOS Installation`).

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Verification**:

- `grep -n '^#' docs/installation/BASIC_INSTALLATION.md` shows the new `###` heading positioned
  between `## NixOS Installation` and `## Optional: Nix on Other Platforms`.
- `grep -n 'PIP_USER=0' docs/installation/BASIC_INSTALLATION.md` matches once.
- `grep -n 'stdenv.cc.cc.lib' docs/installation/BASIC_INSTALLATION.md` matches once.
- The existing `nix develop` block is byte-identical in `git diff` (only additions appear in the
  NixOS region of the diff).
- Optional spot-check on a NixOS host: run the recipe end-to-end against the currently published
  `model-checker` and confirm it succeeds. Not a gate — the recipe was already verified when the
  task was written — but cheap if the host is available.

**Files to modify**:

- `docs/installation/BASIC_INSTALLATION.md` - new `### Verifying a Published Release on NixOS`
  subsection, pure addition.

---

### Phase 5: Cross-file verification and out-of-scope finding record [NOT STARTED]

**Goal**: Confirm no stale claim survives across all four files, confirm no out-of-scope file was
touched, and record the `run_update.py` drift for a follow-up task.

**Tasks**:

- [ ] Run a repo-wide sweep for the corrected claims within the four touched files and confirm
      each is gone.
- [ ] Confirm `git status --short` lists exactly the four target files plus this task's `specs/`
      artifacts. Any other path in the list is a scope violation to investigate before
      committing.
- [ ] Confirm `.github/workflows/release.yml` and `flake.nix` are unmodified.
- [ ] Run `bash .claude/scripts/check-task-references.sh` and confirm the edited non-`specs/`
      files introduce no new findings (expected: none, since the `specs/archive/125_...` path
      citations contain no `task` token — see Risks).
- [ ] Record in the implementation summary that `run_update.py` (and its `test_update.py` sibling)
      is still cited as the recommended or automated release path in seven files outside this
      task's scope: `code/README.md`, `code/docs/development/README.md`,
      `code/docs/development/PACKAGE_TESTING.md`, `code/docs/development/TEST_RELEASES.md`,
      `code/docs/development/PYPI_RELEASE_GUIDE.md`,
      `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`, and
      `docs/installation/DEVELOPER_SETUP.md`. Neither script exists anywhere in the repository.
      Recommend a follow-up task to either restore a real script or strip the claims down to the
      actual CI release process in `.github/RELEASE_SETUP.md`. Do NOT edit these seven files.
- [ ] Record in the implementation summary the two decisions taken (pointer stub over deletion;
      ENVIRONMENT_SETUP.md scope expansion) and any divergence from the Phase 2 / Phase 3 scope
      hypotheses.

**Timing**: 0.25 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts the touched-file set is exactly four files plus `specs/`
artifacts, and that the out-of-scope `run_update.py` drift spans exactly seven files. Confirm with
`git status --short` and
`grep -rln 'run_update\.py\|test_update\.py' --include='*.md' . | grep -v '^\./specs/'`
respectively. If the second grep returns a different count than seven, record the corrected
inventory in the summary — the follow-up recommendation should carry the true list, not this
plan's estimate.

**Verification**:

- `grep -rn 'PYPI_API_TOKEN' .github/` returns nothing.
- `grep -rn 'run_update' .github/` returns nothing.
- `grep -rnE 'Python 3\.8|3\.8 and 3\.12' .github/ code/docs/development/ENVIRONMENT_SETUP.md`
  returns nothing.
- `grep -rn 'specs/125_' .github/` returns nothing.
- `git diff --stat` lists only: `.github/workflows/README.md`, `.github/RELEASE_SETUP.md`,
  `code/docs/development/ENVIRONMENT_SETUP.md`, `docs/installation/BASIC_INSTALLATION.md`, and
  `specs/` artifacts.
- `bash .claude/scripts/check-task-references.sh` exits 0 with no new findings in the four edited
  files.

**Files to modify**:

- `specs/147_correct_stale_release_and_environment_docs/summaries/01_release-env-docs-summary.md` -
  implementation summary including the out-of-scope finding record.

---

## Testing & Validation

There is no test suite for documentation. Validation is grep-based consistency checking against
ground truth:

- [ ] `grep -rnE 'PYPI_API_TOKEN|run_update|twine upload|cd Code' .github/` returns nothing.
- [ ] `grep -rnE '3\.8 and 3\.12|Python 3\.8' .github/ code/docs/development/ENVIRONMENT_SETUP.md`
      returns nothing.
- [ ] `grep -n "python-version" .github/workflows/release.yml` still shows
      `['3.10', '3.11', '3.12']` (unmodified ground truth).
- [ ] `grep -n 'requires-python' code/pyproject.toml` still shows `>=3.10` (unmodified ground
      truth).
- [ ] `grep -rn 'specs/125_' .github/` returns nothing; the two corrected `specs/archive/125_...`
      paths both resolve on disk.
- [ ] `grep -nE 'ModelChecker/Code|shell\.nix|nix-shell' code/docs/development/ENVIRONMENT_SETUP.md`
      returns nothing.
- [ ] `test -f flake.nix && test -f .envrc` succeeds.
- [ ] `git diff --stat .github/workflows/release.yml flake.nix` is empty.
- [ ] All relative markdown links in the edited regions resolve (`.github/workflows/README.md` to
      `../RELEASE_SETUP.md`; `BASIC_INSTALLATION.md`'s existing `DEVELOPER_SETUP.md` link
      unchanged).
- [ ] `bash .claude/scripts/check-task-references.sh` reports no new findings.

## Artifacts & Outputs

- `.github/workflows/README.md` - reduced to a pointer stub (Phase 1)
- `.github/RELEASE_SETUP.md` - three string corrections (Phase 2)
- `code/docs/development/ENVIRONMENT_SETUP.md` - Python floor, casing, and Nix workflow
  corrections (Phase 3)
- `docs/installation/BASIC_INSTALLATION.md` - new NixOS verification subsection (Phase 4)
- `specs/147_correct_stale_release_and_environment_docs/summaries/01_release-env-docs-summary.md` -
  implementation summary with the out-of-scope `run_update.py` finding recorded (Phase 5)

## Rollback/Contingency

All changes are confined to four markdown files with no build, test, or runtime surface, so
rollback is trivial and carries no risk of leaving the repository in a broken state.

- Per-file revert: `git checkout HEAD -- <path>` for any single file whose changes prove wrong.
- Full revert: `git revert <commit>` on the phase commit, or `git checkout HEAD -- .github/
  code/docs/development/ENVIRONMENT_SETUP.md docs/installation/BASIC_INSTALLATION.md`.
- Contingency for Phase 1: if the pointer stub proves unacceptable (e.g. a directory convention
  requires a fuller README), the fallback is outright deletion via `git rm`, NOT a rewrite. A
  rewritten README reintroduces the two-docs-to-keep-in-sync failure mode this task exists to
  eliminate.
- Contingency for Phase 3: if the `flake.nix` rewrite of the `### 2. Development Shell` subsection
  cannot be verified against the actual flake within the phase budget, narrow the phase to the
  named line-18 and line-103 fixes plus the casing fixes, mark the phase
  `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record naming the deferred prose
  rewrite, and note it in the summary.
