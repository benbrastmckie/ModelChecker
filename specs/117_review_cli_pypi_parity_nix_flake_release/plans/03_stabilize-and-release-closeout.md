# Implementation Plan: Stabilize and Release Close-Out

- **Task**: 117 - review_cli_pypi_parity_nix_flake_release
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Dependencies**: None (blocking subtasks 118-125 all completed)
- **Research Inputs**: reports/03_team-research.md (4-teammate review; + teammate a/b/c/d findings, same directory)
- **Artifacts**: plans/03_stabilize-and-release-closeout.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/pr-prohibition.md
  - .claude/rules/no-task-references-in-deliverables.md
- **Type**: python

## Overview

The `model_checker` restoration effort (subtasks 118-125) is complete and verified: the Nix flake
builds and checks green, the CLI works for standard invocations, the in-package bimodal suite
reproduces its 286/286 baseline, and every claimed deliverable reconciles against git history. A
4-teammate systematic review of that completed work found the restoration solid but surfaced a
bounded set of concrete remaining defects — three of them release-blocking — plus quality gaps and
close-out items. This plan closes task 117 by dispositioning that bounded fix list; it does NOT
re-plan the already-complete restoration. Definition of done: the release pipeline and CI
workflows are correct, the uncommitted soundness fix is dispositioned, the "top-quality release"
quality gaps are closed, the working tree is clean, ROADMAP Phase 1 is seeded, and the repository
is handed to the user for the USER-ONLY publish steps (`/merge`, tag `v1.3.0`, publish).

### Research Integration

The team research report (`reports/03_team-research.md`) supplies every fact used here, verified
by fresh re-execution or independent second-party confirmation:
- **release.yml matrix defect** (Critic finding 1, independently confirmed by synthesis lead):
  `python-version: ['3.8', '3.12']` (release.yml:25) with `fail-fast: true` (line 22) versus
  `requires-python = ">=3.10"` (pyproject.toml:30) — the 3.8 leg cannot install the wheel and
  kills the whole publish pipeline on the first `v1.3.0` tag push.
- **Uncommitted structure.py soundness fix** (found independently by Teammates A and B): a Z3
  UNKNOWN-handling fix in the `solve()`-family methods sits uncommitted and unattributed;
  bimodal 286/286 already passes with it in place.
- **Stale differential-tests.yml** (found independently by Critic and Horizons): path filter and
  pytest target point at pre-relocation paths; the test now lives at
  `oracle/bimodal_logic/tests/`.
- **Bimodal `--maximize` silent failure** (Teammate A, fresh run): dynamic loader in
  `bimodal/semantic/__init__.py` never registers `bimodal_semantic_module` in `sys.modules`,
  breaking ProcessPoolExecutor pickling; 22/22 examples silently report "Maximum N = 0".
- **CHANGELOG, install-docs, and working-tree findings** (Critic findings 3-4, Deliverables
  Audit) and the **post-synthesis addendum**: a new `test_performance_improvement` failure and a
  71-test collection gap (1809 vs baseline 1880) that must be diffed against the committed
  baseline before the "everything-else" suite can be treated as green.

### Prior Plan Reference

The prior plan (`plans/01_restore-model-checker-release.md`, 30 hours) covered the full
restoration of the `model_checker` package identity, theories, tests, Nix flake, docs, and release
engineering — all executed and completed across subtasks 118-125. It is reference context only;
its scope is done. Lessons carried forward: (1) local one-off verification missed the CI/doc
surface a real release hits — this plan explicitly targets that surface; (2) version 1.3.0 is a
carried-forward provisional value that still needs explicit user sign-off; (3) the USER-ONLY
publish boundary (per pr-prohibition.md) held throughout and holds here.

### Roadmap Alignment

`specs/ROADMAP.md` records the durable package-identity decision but its Phase 1 priority list is
empty. `roadmap_flag` is false, so this plan does not add the roadmap review/update wrapper phases;
instead, seeding ROADMAP Phase 1 is normal close-out work in Phase 9 (per research recommendation
P2/10): (a) merge + publish 1.3.0 [USER-ONLY], (b) `nix flake check` as a CI gate, (c) oracle
differential-suite cadence decision, (d) a follow-up task for the 28 documented "everything-else"
failures.

## Goals & Non-Goals

**Goals**:
- Fix all three P0 release-blocking defects (structure.py disposition, release.yml matrix,
  differential-tests.yml).
- Close the P1 quality gaps (bimodal `--maximize`, full-suite delta root-cause, CHANGELOG,
  install docs, working-tree hygiene) so the release is genuinely "top-quality".
- Complete P2 close-out: mark verified PUBLISH-CHECKLIST boxes, seed ROADMAP Phase 1, and hand off
  to the user for USER-ONLY publish steps.
- Preserve the bimodal 286/286 green baseline throughout.

**Non-Goals**:
- Re-planning or re-doing the completed restoration (subtasks 118-125).
- Fixing the 28 documented pre-existing "everything-else" failures (deferred to a follow-up task
  seeded in ROADMAP Phase 1 — this plan only root-causes the NEW delta).
- Any agent-side `git push`, tag creation, PR/`/merge`, PyPI publish, or OIDC/environment setup —
  all USER-ONLY per pr-prohibition.md.
- Widening `checks.default` beyond bimodal, or the imposition `--maximize` memory investigation
  (both explicitly deferred as optional in the research).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| structure.py soundness fix has hidden regressions beyond bimodal | H | L | Add a targeted UNKNOWN-classification test before committing; re-run bimodal 286/286; keep the change scoped and revertable |
| Bimodal `--maximize` `sys.modules` fix breaks single-process CLI paths | M | L | TDD: write a failing `--maximize` bimodal test first; verify logos/exclusion `--maximize` still pass; prefer the minimal registration fix over a broad refactor |
| The 71-test collection gap is a real regression, not environment flake | H | M | Diff collected test IDs against committed `baselines/junit-rest.xml`; if a real regression, do NOT close task 117 — spawn a blocker task instead |
| Working-tree hygiene accidentally stages unrelated user edits (email-draft.md, harness artifacts) | M | M | Targeted per-file staging only; never `git add -A`/`git commit -am`; explicitly keep `specs/116_.../email-draft.md` out of every commit |
| Doc/CHANGELOG edits introduce task-number citations outside specs/ | L | M | Follow no-task-references-in-deliverables.md; cite durable anchors (filenames, headings), not task numbers |
| Version 1.3.0 is wrong and user wants a different bump | M | L | Phase 9 gets explicit user sign-off before any publish; version bump is trivially adjustable and no agent-side tag is created |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4, 6, 7 | -- |
| 2 | 5, 8 | Wave 1 |
| 3 | 9 | Waves 1-2 |

Phases within the same wave can execute in parallel. Phase 5 depends only on Phase 1; Phase 8
depends on the full set of code/doc-fix phases so all scoped fix commits land before the tree is
swept clean. Phase 9 depends on everything.

### Phase 1: Disposition the Uncommitted structure.py Soundness Fix [NOT STARTED]

**Goal**: Attribute, test, and commit the uncommitted Z3 UNKNOWN-handling soundness fix in
`code/src/model_checker/models/structure.py` — or revert it deliberately — so it does not remain
in limbo and ship (or fail to ship) silently.

**Tasks**:
- [ ] Review `git diff code/src/model_checker/models/structure.py` to confirm the exact change:
      Z3 UNKNOWN results must not be misclassified as definitive UNSAT unless
      `reason_unknown() == "timeout"`.
- [ ] Write a failing unit test (TDD, RED) exercising the UNKNOWN-classification branch in the
      `solve()`-family methods before treating the fix as final — asserting non-timeout UNKNOWN is
      not reported as UNSAT.
- [ ] Confirm the working-tree fix turns the test GREEN; adjust the fix minimally if the test
      reveals a gap.
- [ ] Re-run the bimodal suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v` (expect 286/286).
- [ ] Commit the fix + test as a scoped soundness commit (no task-number citation inside the
      source or test files per no-task-references-in-deliverables.md).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/models/structure.py` - the uncommitted UNKNOWN-handling fix (finalize)
- `code/src/model_checker/models/tests/` (or nearest existing test module) - new UNKNOWN-classification test

**Verification**:
- New test passes; bimodal 286/286 still green; `git status` shows structure.py committed, no
  longer in the working tree as uncommitted.

---

### Phase 2: Fix the release.yml Python Matrix [NOT STARTED]

**Goal**: Make the release workflow's Python test matrix consistent with
`requires-python = ">=3.10"` so the first `v1.3.0` tag push does not fail before publishing.

**Tasks**:
- [ ] Edit `.github/workflows/release.yml:25` `python-version: ['3.8', '3.12']` to
      `['3.10', '3.11', '3.12']` (or at minimum `['3.10', '3.12']`).
- [ ] Confirm `fail-fast: true` (line 22) and the `needs:` publish-gating semantics remain intact.
- [ ] Verify no remaining `3.8`/`3.9` reference elsewhere in the workflow contradicts
      `pyproject.toml:30`.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `.github/workflows/release.yml` - Python matrix

**Verification**:
- Matrix contains only Python versions >= 3.10; workflow YAML parses (lint/`yq` or GitHub Actions
  schema check); no version below the `requires-python` floor remains.

---

### Phase 3: Fix or Retire differential-tests.yml [NOT STARTED]

**Goal**: Eliminate the guaranteed-failure time bomb: the workflow's path filter and pytest target
point at pre-relocation paths that no longer exist.

**Tasks**:
- [ ] Decide fix-vs-retire in light of the oracle differential-suite cadence (recorded as a
      ROADMAP item in Phase 9): either repoint or delete.
- [ ] If fixing: update the path filter (`code/src/bimodal_logic/**` never existed under
      `code/src/`) and the pytest target to
      `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.
- [ ] If retiring: delete `.github/workflows/differential-tests.yml` and note in Phase 9 where
      differential coverage will live.
- [ ] Confirm no other workflow references the stale path.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `.github/workflows/differential-tests.yml` - repoint paths or delete

**Verification**:
- Either the workflow references only paths that exist on disk (verify with `ls` on the repointed
  target), or the file is removed; a `theory_lib/bimodal/**` touch no longer triggers a guaranteed
  CI failure.

---

### Phase 4: Fix Bimodal --maximize (sys.modules Registration) [NOT STARTED]

**Goal**: Restore bimodal `--maximize` (currently 22/22 examples silently fail with
`No module named 'bimodal_semantic_module'`) so it works under `ProcessPoolExecutor` pickling.

**Tasks**:
- [ ] Write a failing test (TDD, RED) that exercises bimodal `--maximize` / the comparison
      code path and asserts a non-zero maximum is found (currently reports "Maximum N = 0").
- [ ] Fix `bimodal/semantic/__init__.py`'s dynamic loader: register the module in `sys.modules`
      before `exec_module` (set `sys.modules[spec.name] = module` after `module_from_spec`), OR
      refactor to plain relative imports as exclusion/imposition already do — prefer the minimal,
      lowest-risk change.
- [ ] Confirm the test turns GREEN; verify logos/exclusion `--maximize` still pass (no regression
      in the working single-process paths).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/__init__.py` - dynamic-loader `sys.modules` registration
- Nearest existing bimodal/comparison test module - new `--maximize` regression test

**Verification**:
- New test passes; bimodal `--maximize` reports a non-zero maximum for at least one example;
  logos/exclusion `--maximize` unaffected; bimodal 286/286 still green.

---

### Phase 5: Root-Cause the Full-Suite Delta [NOT STARTED]

**Goal**: Determine whether the addendum's new `test_performance_improvement` failure and the
71-test collection gap (1809 vs baseline 1880) are environment-dependent or a real regression,
before the "everything-else" baseline is treated as still green.

**Tasks**:
- [ ] Re-run the "everything-else" suite (single-threaded is acceptable) producing a JUnit XML:
      `PYTHONPATH=code/src pytest code/ --ignore=<bimodal-in-package> --junitxml=<scratch>.xml`
      (mirror task 122's invocation exactly).
- [ ] Diff collected test IDs against `specs/122_*/baselines/junit-rest.xml` to identify which 71
      tests are no longer collected and whether a missing optional dependency or import error
      explains the gap.
- [ ] Investigate `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetLoaderBehavior::test_performance_improvement`:
      determine if it is a perf-timing flake (environment) or a real behavior regression.
- [ ] Classify the outcome: environment-dependent (document and proceed) vs real regression (do
      NOT close task 117 — record a blocker and spawn a follow-up).

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- None expected (investigation). If a trivial collection-gap cause is found (e.g. an import
  guard), a minimal fix may be applied with a scoped test.

**Verification**:
- A written classification of both anomalies (environment vs regression) grounded in the test-ID
  diff; if environment-dependent, the disposition is recorded for Phase 9; if a regression, a
  blocker is raised rather than silently closing.

---

### Phase 6: Clean the CHANGELOG 1.3.0 Entry [NOT STARTED]

**Goal**: Make the CHANGELOG 1.3.0 entry accurate — GitHub Release notes link to it.

**Tasks**:
- [ ] Split out the stale Issue #73 package-loading content that was folded into the `[1.3.0]`
      entry when `[Unreleased]` was relabeled.
- [ ] Remove or repoint the 3 dead links: `docs/api/builder/loader.md`,
      `docs/guides/project_creation.md`, `docs/migration/package_loading_v2.md` (none exist —
      verify with `ls` and either delete the links or point at real files).
- [ ] Ensure the 1.3.0 entry describes the restoration release honestly, with no internal
      task-number citations (per no-task-references-in-deliverables.md; GitHub issue numbers such
      as #73 are fine).

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `CHANGELOG.md` (project-root changelog carrying the `[1.3.0]` entry) - de-conflate and fix links

**Verification**:
- No dead relative links remain in the 1.3.0 entry (each link target exists on disk); the entry
  contains no stale unrelated content; no task-number citations.

---

### Phase 7: Update Installation Docs and README [NOT STARTED]

**Goal**: Make install documentation match shipped reality (flake-based Nix, correct casing,
correct Python floor).

**Tasks**:
- [ ] Replace retired `shell.nix`/`nix-shell` instructions with `flake.nix` / `nix develop`
      across `docs/installation/*` (7 files) and `README.md:36`.
- [ ] Fix the `ModelChecker/Code` -> `code` casing bug (8 hits across the doc files).
- [ ] Fix "Python 3.8 or higher" -> "Python 3.10 or higher" in
      `docs/installation/BASIC_INSTALLATION.md` and any other occurrence.
- [ ] Verify no doc cites an internal task number (per no-task-references-in-deliverables.md).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `docs/installation/*` (7 files, incl. `BASIC_INSTALLATION.md`) - Nix flake, casing, Python floor
- `README.md` (line ~36) - Nix flake instruction + Python floor

**Verification**:
- `grep -rn "shell.nix\|nix-shell\|ModelChecker/Code\|Python 3.8" docs/installation README.md`
  returns no stale hits; instructions reference `nix develop`/`flake.nix` and Python 3.10+.

---

### Phase 8: Working-Tree Hygiene [NOT STARTED]

**Goal**: Bring the tree to a clean, release-ready state without capturing unrelated user edits.

**Tasks**:
- [ ] `git rm code/specs/state.json` (orphaned tracked file; already deleted; pre-reorg leftover).
- [ ] Commit the 118-125 bookkeeping: the four `.orchestrator-handoff.json` files and the task-121
      plan status line, as a scoped closure commit.
- [ ] Decide track-vs-ignore for untracked harness artifacts (`.claude-extensions.json`,
      `specs/.events.lock`, `specs/.return-meta-multi.json`, `specs/events.jsonl`) and apply:
      add to `.gitignore` (already modified) or track deliberately.
- [ ] Explicitly keep `specs/116_.../email-draft.md` (the user's own unrelated edit) OUT of every
      commit in this task.
- [ ] Use only targeted, per-file staging — never `git add -A` or `git commit -am`.

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4, 6, 7

**Files to modify**:
- `code/specs/state.json` (remove), `.gitignore` (harness-artifact decision), `.orchestrator-handoff.json` files, task-121 plan status line

**Verification**:
- `git status --porcelain` shows a clean tree except for deliberately-untracked-and-ignored
  harness artifacts and the untouched `specs/116_.../email-draft.md`; no unrelated files staged in
  any commit.

---

### Phase 9: Close-Out, ROADMAP Seeding, and User Handoff [NOT STARTED]

**Goal**: Finalize release close-out, seed ROADMAP Phase 1, run final verification, and hand off
the USER-ONLY publish steps.

**Tasks**:
- [ ] Mark the `nix flake check` / `nix build` pre-flight boxes in
      `specs/125_*/PUBLISH-CHECKLIST.md` as done (verified passing this review round).
- [ ] Seed `specs/ROADMAP.md` Phase 1 with: (a) merge branch + publish 1.3.0 [USER-ONLY],
      (b) `nix flake check` as a CI gate job, (c) oracle differential-suite cadence decision
      (coupled with Phase 3's fix-vs-retire outcome), (d) a follow-up task for the 28 documented
      "everything-else" failures (start with the malformed `"A[]"` literal in
      `code/tests/utils/helpers.py::create_test_model()`, which affects 12 tests).
- [ ] Run final verification: bimodal suite (expect 286/286); the new tests from Phases 1 and 4;
      `nix flake check` ONLY if any flake file was changed (none expected).
- [ ] Record the Phase 5 delta classification in the close-out.
- [ ] Prepare the user handoff note: request explicit sign-off that 1.3.0 is the intended bump
      from 1.2.12, and enumerate the remaining USER-ONLY steps (`/merge`, tag `v1.3.0`,
      OIDC/trusted-publisher + environment setup, publish) per pr-prohibition.md. The plan does
      NOT perform any push/tag/publish.

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8

**Files to modify**:
- `specs/125_*/PUBLISH-CHECKLIST.md` - check verified pre-flight boxes
- `specs/ROADMAP.md` - seed Phase 1 items

**Verification**:
- Bimodal 286/286 green; Phase 1 and Phase 4 tests pass; ROADMAP Phase 1 lists the four items;
  PUBLISH-CHECKLIST pre-flight boxes checked; handoff note enumerates USER-ONLY steps and requests
  version sign-off; no agent-side push/tag/publish performed.

## Testing & Validation

- [ ] Bimodal suite green after Phases 1 and 4: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v` (expect 286/286).
- [ ] New UNKNOWN-classification test (Phase 1) passes.
- [ ] New bimodal `--maximize` regression test (Phase 4) passes; logos/exclusion `--maximize` unaffected.
- [ ] Full-suite delta classified via test-ID diff against `specs/122_*/baselines/junit-rest.xml` (Phase 5).
- [ ] `.github/workflows/release.yml` and `differential-tests.yml` YAML parse and reference only valid Python versions / existing paths.
- [ ] `grep` confirms no stale `shell.nix`/`nix-shell`/`ModelChecker/Code`/`Python 3.8` in docs; no dead links in CHANGELOG 1.3.0 entry.
- [ ] `nix flake check` only if a flake file changed (not expected).
- [ ] `git status --porcelain` clean except deliberately-ignored harness artifacts and untouched email-draft.md.

## Artifacts & Outputs

- Committed `code/src/model_checker/models/structure.py` soundness fix + test.
- Corrected `.github/workflows/release.yml` (Python matrix) and `differential-tests.yml` (repointed or removed).
- Fixed `bimodal/semantic/__init__.py` + bimodal `--maximize` regression test.
- Full-suite delta classification (recorded in Phase 9 close-out / task metadata).
- Cleaned `CHANGELOG.md` 1.3.0 entry.
- Updated `docs/installation/*` (7 files) + `README.md`.
- Clean working tree (`code/specs/state.json` removed, bookkeeping committed, harness-artifact decision applied).
- Updated `specs/125_*/PUBLISH-CHECKLIST.md` and seeded `specs/ROADMAP.md` Phase 1.
- User handoff note enumerating USER-ONLY publish steps and requesting version sign-off.

## Rollback/Contingency

- Each phase commits independently and scoped, so any single fix can be reverted in isolation via
  `git revert <sha>` without unwinding the others.
- If Phase 1's UNKNOWN-classification test reveals the fix is incorrect, revert
  `structure.py` to its last committed state and re-derive deliberately (the change is small and
  isolated to the `solve()`-family methods).
- If Phase 4's `sys.modules` fix regresses single-process CLI paths, revert to the working-tree
  state and pursue the alternative relative-imports refactor instead.
- If Phase 5 finds a real regression (not environment flake), do NOT close task 117: mark it
  `[BLOCKED]`, record the finding, and spawn a follow-up task rather than proceeding to handoff.
- No agent-side push/tag/publish occurs, so there is no remote state to roll back — the release
  trigger remains entirely in the user's hands.
