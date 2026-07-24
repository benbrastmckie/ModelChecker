# Research Report: Deliverables Audit and Cross-Task Reconciliation (Task 117, Teammate B)

**Task**: 117 - review_cli_pypi_parity_nix_flake_release (angle: audit tasks 118-125's claimed
deliverables against git history and working-tree state)
**Sources/Inputs**: `specs/118_*` through `specs/125_*` summaries/plans/`.orchestrator-handoff.json`
files; `git log`, `git status --porcelain`, `git diff master...HEAD --stat`; `.gitignore`;
`.github/RELEASE_SETUP.md` history

## Executive Summary

- All 8 spawned subtasks (118-125) are marked `completed` in `specs/state.json`, and each has a
  matching, phase-by-phase commit trail in `git log` — the claimed narrative and the actual
  history line up well; no fabricated or missing commits found.
- **One substantive, undocumented, uncommitted code change is sitting in the working tree**:
  `code/src/model_checker/models/structure.py` has a real semantic fix (Z3 `UNKNOWN` was being
  silently misclassified as `UNSAT` unless `reason_unknown() == "timeout"` exactly) that is not
  mentioned in any of the 118-125 summaries, plans, or handoffs. This must be dispositioned
  (verified, tested, attributed to a task, and committed — or reverted) before release.
- Task 121 and 122 explicitly flagged and then verifiably resolved a cross-task dependency
  (`builder/module.py`'s dead `SequentialSaveManager`/`ConsoleInputProvider` import) — a clean
  example of the handoff chain working correctly.
- Task 122 documents 28 pre-existing, deterministic (non-flaky) test failures and 9 `xfail`s in
  the "everything else" and oracle suites, explicitly deferred to a follow-up task rather than
  fixed. These are known, accepted gaps, not silent regressions — but they are still open.
- Several harmless-looking but uncommitted/untracked artifacts (task-management bookkeeping
  files, one stale tracked file, session-lock files) need routine disposition before a release
  commit, and are listed below.

**Confidence Level**: High for the git-history reconciliation and uncommitted-file findings
(directly verified via `git log`/`git diff`/`git status`); Medium for the completeness of the
"deferred items" enumeration (based on grep + full reads of the 8 summaries, not the full
phase-handoff/plan corpus).

## Deliverables Map (118-125)

| Task | Claimed deliverable | Git evidence |
|------|---------------------|---------------|
| 118 | Branch created; before-state baseline captured; `bimodal_logic` oracle relocated `code/src/bimodal_logic/` → `oracle/bimodal_logic/`; 8 dependent test files reconciled | Commits `618c8f5e`...`dca6e469`; `oracle/bimodal_logic/` exists with README + tests; confirmed |
| 119 | Restored `builder/`, `iterate/`, `jupyter/`, `output/manager.py`+deps from git history; registered `logos` in `AVAILABLE_THEORIES`; 446 logos tests green | Commits `96c93cae`...`1918942c`; matches |
| 120 | Restored + ported `exclusion`/`imposition` (z3_shim, `is_true`/`is_false`); registered both; 253 combined passed, 732 logos+bimodal regression-clean | Commits `71da2978`...`9afa165e`; matches |
| 121 | Restored `model-checker` package identity in `pyproject.toml`; widened `testpaths`; repaired all collection errors (2095 tests/0 errors); added `pytest-xdist` dev extra | Commits `57a49292`...`a789381f`; matches |
| 122 | Root-caused all 5 cross-oracle differential failures (Z3 timeout/UNSAT conflation), fixed `builder/module.py` stale import, established full green baseline (28 pre-existing failures documented, 9 xfails) | Commits `b718cc74`...`d7e40e14`; matches; see "Deferred items" below |
| 123 | Rewrote `flake.nix` multi-system (`packages.default`, `devShells.default`, `checks.default`); deleted `code/shell.nix` | Commits `e726abcb`...`3c79cf01`; `code/shell.nix` absent, confirmed |
| 124 | Refreshed README.md/CLAUDE.md/code/README.md/CHANGELOG.md/ROADMAP.md for restored-framework accuracy | Commits `494ad276`...`8f095d3e`; matches (CLAUDE.md edit not committed — gitignored, expected) |
| 125 | Fixed `release.yml` (casing bug, OIDC trusted publishing), rewrote `RELEASE_SETUP.md`, local build rehearsal, `PUBLISH-CHECKLIST.md` (user-gated, no push/publish performed) | Commits `8b51a94a`...`0cb3890d`; matches |

All 8 summaries' phase counts, commit messages, and file-touch lists correspond to actual commits
in `git log --oneline`. No claimed deliverable was found to be absent from history.

## Working Tree: Items Needing Disposition Before Release

### 1. Undocumented uncommitted code change (highest priority)

`code/src/model_checker/models/structure.py` (modified, uncommitted, mtime 2026-07-24 03:07 —
same day as the rest of this branch's activity) changes both `solve()`-family methods so that
any Z3 `UNKNOWN` result is treated as an inconclusive timeout, instead of the prior logic which
only did so when `reason_unknown() == "timeout"` literally and otherwise silently fell through to
treating an inconclusive `UNKNOWN` as a definitive `UNSAT` (i.e., "formula is valid" — unsound).
The inline comment added by whoever made this change explains the reasoning (Z3 commonly reports
`"canceled"` rather than `"timeout"`, and other reason strings exist too).

- **Not mentioned in any of the 118-125 plans, summaries, or `.orchestrator-handoff.json`
  files** — grepped for `reason_unknown`, `UNKNOWN`, and `structure.py` across every task-118-125
  markdown artifact; zero hits outside baseline log files.
- This is a real correctness/soundness fix, not a formatting change — it changes when the model
  checker reports "no countermodel found" (valid) vs. "search inconclusive" (timeout).
- No test run or verification for this specific change is referenced anywhere in the task
  artifacts. It is unclear whether this was written by a teammate agent in the current live
  session (e.g., during CLI/test re-verification) or is stray uncommitted work from a prior
  session.
- **Recommendation**: before release, either (a) attribute this to a task, run the model-checker
  and `theory_lib` test suites to confirm it doesn't change any test's expected pass/fail status,
  and commit it with a clear message and test coverage, or (b) if unintended/unverified, revert
  it and re-derive it deliberately as a scoped fix.

### 2. Stale orphaned tracked file

`code/specs/state.json` shows as deleted in `git status`. This file's last real history is from
commits `c681f514`/`e70307a1`/`fcd85850` (tasks 65/70, long predating the current top-level
`specs/{NNN}_{SLUG}/` convention); `code/specs/` no longer exists as a directory on disk at all.
This is unrelated to tasks 118-125 — it is a leftover tracked file from a pre-reorg era that
nothing recreated. Safe to `git rm` explicitly as routine cleanup rather than leaving as a
dangling uncommitted deletion.

### 3. Task-management bookkeeping needing a commit (expected, low-risk)

- `specs/120_.../.orchestrator-handoff.json` (modified) and `specs/118_.../`,
  `specs/119_.../`, `specs/121_.../` `.orchestrator-handoff.json` (untracked) — all show the
  expected plan→implement transition content matching each task's summary. Routine — needs
  staging into a task-closure commit, not a defect.
- `specs/121_.../plans/01_restore-package-identity-test-infra.md` (modified) — only the
  `[IMPLEMENTING]` → `[COMPLETED]` status-line header changed. Routine.
- `specs/120_.../.lock/holder.json` (deleted, untracked-removal) — a session lock artifact;
  harmless.
- `specs/TODO.md`, `specs/state.json` — expected task-tracking updates reflecting 118-125
  completion.

### 4. Session/orchestration artifacts that likely should not be committed as-is

`.claude-extensions.json`, `specs/.events.lock`, `specs/.return-meta-multi.json`,
`specs/events.jsonl`, `specs/117_.../.lock/` are untracked files generated by the agent-system
harness during this session's orchestration (extension install manifest, event log, lock files,
multi-task return metadata). None of these were produced as "deliverables" by tasks 118-125; they
are infrastructure bookkeeping. Worth a decision on whether any of these are meant to be
persisted in the repo at all, or should be gitignored/cleaned up (`.gitignore` already covers
`**/.postflight-pending`, `**/.return-meta.json`, `**/specs/tmp/` — the plural/multi variants
above are not currently covered).

### 5. `.gitignore` change (`/.claude` added)

Not attributed to any of the 118-125 tasks. `.claude/` was never git-tracked in this repo (`git
ls-files .claude` returns 0 entries), so this is a no-op formalization, not a behavior change —
low risk, but flag it as an unattributed edit for the record.

### 6. Unrelated dirty file

`specs/116_draft_email_modelchecker_architecture/email-draft.md` (modified) — content is a
personal email draft to "Joel" about ModelChecker, unrelated to the 118-125 restoration work.
Almost certainly the user's own edit outside the scope of this review; flagging only so it isn't
accidentally swept into a release-related commit.

## Follow-Up Items Explicitly Deferred by Tasks 118-125

1. **Task 122 → follow-up task recommended**: 28 pre-existing, deterministic (verified via serial
   rerun) failures in the "everything else" suite, root-caused into 8 categories in
   `specs/122_.../baselines/rest-suite-disposition.md`. Highest-value fix identified: a malformed
   `"A[]"` default formula literal in `code/tests/utils/helpers.py::create_test_model()` affecting
   12 tests. Also flagged: a missing `tests.fixtures.example_data` module, and
   `WitnessRegistryError`/`WitnessConstraintError` not populating `.theory` (plausibly linked to
   task 120's exclusion-theory restoration).
2. **Task 122 → 9 `xfail(strict=True)` tests left unfixed by design**: 5 in
   `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (the oracle's own
   `Z3OracleProvider.find_countermodel()` conflates solver timeout with proven-UNSAT — a bug in
   the oracle harness itself, not the in-package model checker) and 4 from `oracle/`'s lack of
   packaging metadata (entry-point discovery unconditionally empty — reversing this would
   contradict task 118's relocation decision).
3. **Task 123**: `checks.default` in the new flake intentionally covers only the in-package
   `theory_lib/bimodal` suite (286 tests) — the standalone `oracle/` tree and the "everything
   else" suite are explicitly out of scope for the hermetic Nix gate.
4. **Task 124**: one pre-existing dead-link pair in `code/CHANGELOG.md`'s historical Issue #73
   section, left unedited, flagged for a future documentation pass (unrelated to the current
   restoration).
5. **Task 125**: ends deliberately at `PUBLISH-CHECKLIST.md` awaiting the user — no PyPI upload,
   push, tag, or PR performed, per `.claude/rules/pr-prohibition.md`. Version `1.3.0` is carried
   forward from task 121's provisional value; nothing in 122-125 explicitly re-confirms `1.3.0` as
   the final intended version bump from the last published `1.2.12` — worth an explicit user
   sign-off during `/merge`.

## Prior-Art Alignment

- **`RELEASE_SETUP.md`** pre-existed (created under task 16, "fixed workflows"); task 125's
  rewrite reconciles it with the actual single `release.yml` pipeline rather than replacing an
  empty file — good continuity with prior art.
- **`oracle/` tree** is new (task 118) and self-documented via `oracle/bimodal_logic/README.md`;
  no conflicting prior top-level `oracle/` content existed.
- **Top-level `specs/baselines/`** referenced in the root `CLAUDE.md`'s "Specs Directory
  Protocol" (`specs/baselines/` - "Test regression baselines") is a vestigial description of an
  older flat layout; tasks 118-125 instead created baselines nested per-task
  (`specs/122_.../baselines/`, `specs/125_.../rehearsal/`), consistent with the actual
  `.claude/CLAUDE.md` per-task artifact convention (`specs/{NNN}_{SLUG}/...`). This is pre-existing
  documentation drift in the root `CLAUDE.md`, not something introduced by 118-125, but worth
  noting if anyone goes looking for a single top-level baselines directory.

## Recommended Approach

1. Resolve the `structure.py` UNKNOWN-handling change first — it is the one item in this audit
   that is a real, unverified, unattributed code change touching model-checking correctness.
   Attribute it, test it, and commit it (or revert it) before anything else in the release
   checklist proceeds.
2. `git rm code/specs/state.json` as routine orphaned-file cleanup.
3. Stage and commit the task-management bookkeeping files (`.orchestrator-handoff.json` ×4,
   the 121 plan status line) as part of closing out tasks 118-125, following
   `.claude/rules/git-workflow.md`'s task-scoped commit conventions.
4. Decide on disposition for the session/orchestration artifacts (`.claude-extensions.json`,
   `specs/.events.lock`, `specs/.return-meta-multi.json`, `specs/events.jsonl`,
   `specs/117_.../.lock/`) — either gitignore them or confirm they're intentionally tracked.
5. Confirm `specs/116_.../email-draft.md`'s modification is the user's own out-of-scope edit and
   exclude it from any release-related commit.
6. Before `/merge`, get explicit user confirmation that `1.3.0` is the intended version number
   (not just a carried-forward provisional value from task 121).
7. Treat the 28 pre-existing "everything else" failures and 9 `xfail`s as accepted, documented
   release-blockers-that-aren't — but consider spawning the follow-up task task 122 recommended
   (the `"A[]"` literal fix is a cheap, high-value first item) either before or shortly after this
   release.

## Evidence/Examples

- `git diff code/src/model_checker/models/structure.py` — full diff confirms the UNKNOWN-handling
  change in both `solve()`-family methods.
- `git log --oneline -40` — confirms the full 118-125 phase-by-phase commit trail.
- `jq -r '.active_projects[] | select(.project_number>=117 and .project_number<=125) | "\(.project_number) \(.status) \(.task_type)"' specs/state.json` — all 8 subtasks show `completed`.
- `specs/122_.../baselines/rest-suite-disposition.md` — full 8-category, 28-test disposition table
  with an explicit recommended follow-up task.
