# Research Report: Task #117

**Task**: review_cli_pypi_parity_nix_flake_release — Review and stabilize the repo after recent
revisions: verify the CLI works, audit discrepancies with the model-checker package on PyPI,
build a Nix flake for testing on NixOS, complete full testing, and prepare a top-quality release
to push to PyPI
**Date**: 2026-07-24
**Mode**: Team Research (4 teammates: Primary, Deliverables Audit, Critic, Horizons)
**Session**: sess_1784907878_8edab2
**Focus**: "A lot has been done, requiring systematic review." — all 8 blocking subtasks
(118–125) are now completed; this round is the systematic review of that completed work.

## Summary

The restoration effort (tasks 118–125) is **substantially real and verified**: the Nix flake
builds and checks green from scratch, the CLI works for standard invocations, the in-package
bimodal suite reproduces its 286/286 baseline exactly, the 1.3.0 build rehearsal/parity-diff
evidence is internally consistent, and every claimed deliverable in the 8 task summaries
reconciles against actual git history with no fabricated or missing commits.

However, the review surfaced **three release-blocking defects and a set of quality gaps** that
survived the entire 8-task decomposition — the common failure pattern being that all 118–125
verification was local one-off runs, never checked against the CI/doc surface a real user or the
tag-triggered release pipeline would actually hit:

1. **The release pipeline itself is broken**: `release.yml` tests on Python 3.8, which the
   package's `requires-python = ">=3.10"` refuses; with `fail-fast: true` gating all publish
   jobs, the very first `v1.3.0` tag push would fail before publishing anything.
2. **An unattributed, uncommitted soundness fix** sits in the working tree
   (`code/src/model_checker/models/structure.py`): Z3 UNKNOWN results were previously
   misclassified as definitive UNSAT unless `reason_unknown() == "timeout"` exactly. The fix is
   real and correct (286/286 pass with it in place) but belongs to no task and will silently NOT
   ship if a release is cut from HEAD.
3. **`differential-tests.yml` is a live time bomb** (found independently by two teammates): it
   filters on a path that no longer exists and invokes a test file task 118 relocated to
   `oracle/bimodal_logic/tests/`; the next commit touching `theory_lib/bimodal/**` triggers a
   guaranteed CI failure.

The strategic picture (Horizons) is that the remaining *publish* steps are correctly USER-ONLY
gated, so task 117 should close via a **bounded defect-fix list** — not an open-ended polish
cycle — followed by roadmap seeding and user handoff to `/merge` + tag.

## Key Findings

### Primary Verification (Teammate A) — confidence: high

Freshly re-executed, not re-read:
- **Nix flake**: `nix flake show`, `nix build` (produces working
  `/nix/store/...-python3.12-model-checker-1.3.0/bin/model-checker`), and `nix flake check` all
  PASS — this satisfies the two unchecked pre-flight boxes in `PUBLISH-CHECKLIST.md` step 1.
- **CLI**: `--help`, plain runs, `--save`, and `--maximize` for logos/exclusion all work.
- **NEW BUG — bimodal `--maximize` silently broken** (22/22 examples): every bimodal example
  fails with `No module named 'bimodal_semantic_module'`. Root cause:
  `bimodal/semantic/__init__.py`'s dynamic loader (`spec_from_file_location` +
  `exec_module`) never registers the module in `sys.modules`, so
  `builder/comparison.py`'s `ProcessPoolExecutor` cannot pickle the semantics class in worker
  processes. CLI still exits 0 and reports "Maximum N = 0" — silent failure. Pre-existing bug
  (predates task 118); never caught because task 122's `cli-smoke-maximize.txt` only exercised
  logos. Separate minor issue: one imposition example hits `max. memory exceeded` under
  parallelism.
- **Tests**: in-package bimodal 286/286 fresh, matching task 122's baseline exactly. The larger
  1880-test "everything-else" scope was not fresh-re-run (no `pytest-xdist` in this shell;
  single-threaded run exceeded session window) and rests on task 122's well-evidenced baseline
  (28 root-caused pre-existing failures across 8 categories, 9 justified xfails).
- **CRITICAL — uncommitted `structure.py` change**: substantive Z3 UNKNOWN-handling soundness fix
  in both `solve()`-family methods, uncommitted, unattributed (file's last commit predates
  task 118; no 118–125 artifact mentions it).

### Deliverables Audit (Teammate B) — confidence: high (git reconciliation), medium (deferred-item completeness)

- **All 8 task summaries reconcile against git history** — phase counts, commit trails, and
  file-touch lists all correspond to real commits; no claimed deliverable is absent.
- **Corroborates the `structure.py` finding independently**: grepped `reason_unknown`/`UNKNOWN`/
  `structure.py` across every 118–125 artifact — zero hits. Must be dispositioned
  (attribute+test+commit, or revert) before release.
- **Working-tree items needing disposition**: orphaned tracked file `code/specs/state.json`
  (deleted; pre-reorg leftover — safe to `git rm`); four `.orchestrator-handoff.json` files and
  the task-121 plan status line (routine bookkeeping needing a closure commit); untracked
  harness artifacts (`.claude-extensions.json`, `specs/.events.lock`,
  `specs/.return-meta-multi.json`, `specs/events.jsonl`) not covered by `.gitignore` — needs a
  track-or-ignore decision; `specs/116_.../email-draft.md` is the user's own unrelated edit —
  keep out of release commits.
- **Version 1.3.0 is a carried-forward provisional value** from task 121 — nothing in 122–125
  explicitly re-confirms it as the intended bump from 1.2.12; wants explicit user sign-off.
- **Explicitly deferred (not silently dropped) items**: 28 documented "everything-else" failures
  (cheapest high-value fix: malformed `"A[]"` literal in
  `code/tests/utils/helpers.py::create_test_model()` affecting 12 tests), 9 intentional xfails,
  flake's `checks.default` scoped to bimodal only, one dead-link pair in historical CHANGELOG.

### Gaps and Shortcomings (Critic, Teammate C) — confidence: high on findings 1–4, 6

All verified directly against the tree:
1. **`release.yml` Python matrix `['3.8', '3.12']` vs `requires-python = ">=3.10"`** — the 3.8
   leg cannot install the wheel; `fail-fast: true` + `needs:` chaining kills the whole publish
   pipeline. **Verified independently by the synthesis lead** (release.yml:25,
   pyproject.toml:30, fail-fast at release.yml:22). Task 125 edited this exact file without
   catching it, and `PUBLISH-CHECKLIST.md` never asks the runner to inspect the matrix.
2. **`differential-tests.yml` stale** (also found by Teammate D): path filter
   `code/src/bimodal_logic/**` never existed under `code/src/`; pytest target
   `.../bimodal/tests/unit/test_cross_oracle_differential.py` was relocated by task 118 to
   `oracle/bimodal_logic/tests/`. Last touched pre-restoration; next `theory_lib/bimodal/**`
   commit triggers a guaranteed failure.
3. **CHANGELOG 1.3.0 entry conflates releases and has 3 dead links**: task 124 relabeled
   `[Unreleased]` → `[1.3.0]` but left unrelated Issue #73 package-loading content folded in,
   linking to `docs/api/builder/loader.md`, `docs/guides/project_creation.md`,
   `docs/migration/package_loading_v2.md` — none exist. GitHub Release notes link here.
4. **Install docs contradict the shipped reality**: `docs/installation/BASIC_INSTALLATION.md`
   and `README.md:36` still instruct `nix-shell` with the `shell.nix` task 123 deleted; the
   `ModelChecker/Code` casing bug fixed in release.yml persists in 7 doc files (8 hits);
   BASIC_INSTALLATION still claims "Python 3.8 or higher". Task 124 never touched
   `docs/installation/`.
5. **The only automated gate (`checks.default`) covers 286 of ~2716 tests** — the narrowing is
   documented as scope, but never flagged as a residual risk; nothing automatically guards the
   other suites. (Medium confidence — defensible as a first-release scope choice.)
6. **The Nix path cannot verify the PyPI `z3-solver>=4.8.0` bound at all**
   (`pythonRemoveDeps = [ "z3-solver" ]` strips the requirement) — a parity gap between the Nix
   and PyPI verification paths that no artifact discusses.
7. Round-1 items carried on self-report only: `SEMANTICS.md` "no edits needed" and
   `code/scripts/README.md`'s link to deleted `QUANTIFIER_SOLVERS.md` lack second-party
   verification. (Low-medium confidence.)

### Strategic Horizons (Teammate D) — confidence: high on 1–4, medium on 5–6

- **ROADMAP.md Phase 1 is empty** and no 118–125 task attached `roadmap_items`; task 117's
  close is the natural seeding point.
- **Remaining publish steps are correctly USER-ONLY** (push, tag, OIDC trusted-publisher
  registration, environment setup) per `pr-prohibition.md`; task 117 should close as
  "restoration + release engineering complete, handed to user," not accumulate agent-side polish.
- **Branch is 48 commits ahead / 0 behind master** (379 files, ~78K insertions) — clean
  fast-forward today; couple "merge to master" tightly to 117's closure before that risk profile
  changes.
- **The flake should become a standing CI gate** (`nix flake check` in a GitHub Actions job) —
  no workflow currently invokes Nix.
- **Oracle cadence undecided**: where oracle/ lives is settled; when its differential suite runs
  is not — combined with the broken differential-tests.yml, it risks becoming manual-only.
- Vault/archive: no action needed (`next_project_number` = 126).

## Synthesis

### Conflicts Resolved (2)

1. **A's "release.yml checks out on read-verification" vs C's broken-matrix finding.**
   Resolved **in favor of C** — the synthesis lead independently confirmed
   `python-version: ['3.8', '3.12']` (release.yml:25), `fail-fast: true` (line 22), and
   `requires-python = ">=3.10"` (pyproject.toml:30). A's read focused on the OIDC job graph and
   casing fix, which are indeed correct; the matrix bug is additional, not contradictory.
2. **D's "close soon, don't expand scope" vs C's "do not close on rehearsal evidence alone."**
   Reconciled: both are right at different altitudes. C's findings 1–4 are concrete, verified
   defects that directly defeat task 117's stated goals (a broken publish trigger is not
   "polish"), while D's scope discipline correctly bars open-ended review expansion. Resolution:
   close 117 via the **bounded fix list** below, then hand off — no further review rounds.

### Corroborations

- The uncommitted `structure.py` soundness fix was found independently by A (via `git status` +
  diff analysis + fresh test run) and B (via artifact grep proving no task owns it).
- The stale `differential-tests.yml` was found independently by C and D with matching evidence.

### Gaps Identified

- The 1880-test "everything-else" suite was not fresh-re-run this round (environment lacks
  `pytest-xdist`; single-threaded run exceeded the session window) — disposition rests on task
  122's baseline document, which A spot-checked and found reliable.
- No live GitHub Actions execution was possible (no credentials) — release.yml findings are
  static-analysis only, though the matrix defect is unambiguous.
- D's Nix-CI and oracle-cadence suggestions were not cross-checked against
  `02_spawn-analysis.md`/the master plan for pre-existing coverage.

### Recommendations (consolidated remaining work for task 117)

**P0 — release-blocking, fix before anything else:**
1. **Disposition the uncommitted `structure.py` fix**: attribute, test (bimodal 286/286 already
   confirmed green with it in place), and commit it as a scoped soundness fix — or revert and
   re-derive deliberately. It must not remain in limbo.
2. **Fix `release.yml` matrix** to `['3.10', '3.12']` (or add `'3.11'`), keeping `fail-fast`
   semantics intact.
3. **Fix or retire `differential-tests.yml`**: repoint path filters and pytest target at
   `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, or delete the workflow if CI
   coverage for the differential suite is to live elsewhere (couple with the oracle-cadence
   decision).

**P1 — "top-quality release" quality gate:**
4. Fix bimodal `--maximize` (register the dynamically-loaded module in `sys.modules` before
   `exec_module`, or refactor to plain relative imports as exclusion/imposition already use).
5. Clean the CHANGELOG 1.3.0 entry: split out the stale Issue #73 content, remove/fix the 3 dead
   links.
6. Update `docs/installation/*` (7 files) + `README.md:36`: `flake.nix`/`nix develop` instead of
   retired `shell.nix`, fix `ModelChecker/Code` → `code` casing, fix "Python 3.8 or higher" →
   3.10+.
7. Working-tree hygiene: `git rm code/specs/state.json`; commit the 118–125 bookkeeping files;
   decide track-vs-ignore for the harness artifacts (`.claude-extensions.json`,
   `specs/.events.lock`, `specs/.return-meta-multi.json`, `specs/events.jsonl`); keep
   `specs/116_.../email-draft.md` out of all release commits.

**P2 — close-out and handoff:**
8. Mark `PUBLISH-CHECKLIST.md`'s `nix flake check`/`nix build` pre-flight boxes done (verified
   passing this round).
9. Get explicit user sign-off that **1.3.0** is the intended version (it is a carried-forward
   provisional value).
10. Seed `specs/ROADMAP.md` Phase 1: (a) merge branch + publish 1.3.0 [USER-ONLY], (b) `nix
    flake check` as a CI job, (c) oracle differential-suite cadence decision, (d) follow-up task
    for the 28 documented failures (start with the `"A[]"` literal fix).
11. Hand off to the user for the USER-ONLY steps: `/merge`, tag `v1.3.0`, OIDC/environment
    setup, publish.

**Optional/deferred (not blocking):** full fresh 1880-test re-run once `pytest-xdist` is
available; widen `checks.default` or document the narrowed CI gate explicitly; imposition
`--maximize` memory investigation; second-party check of `SEMANTICS.md` and
`code/scripts/README.md` link.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary verification (live re-runs) | completed | high (CLI/Nix/structure.py); medium-high (full-suite disposition) |
| B | Deliverables audit vs git history | completed | high (reconciliation); medium (deferred-item completeness) |
| C | Critic — gaps and dropped risks | completed | high (findings 1–4, 6); medium (5); low-medium (7) |
| D | Horizons — roadmap and strategy | completed | high (1–4); medium (5–6) |

## References

- Teammate findings: `03_teammate-a-findings.md`, `03_teammate-b-findings.md`,
  `03_teammate-c-findings.md`, `03_teammate-d-findings.md` (same directory)
- Prior rounds: `01_team-research.md`, `02_spawn-analysis.md`
- Key evidence: `.github/workflows/release.yml:22,25`; `code/pyproject.toml:30`;
  `.github/workflows/differential-tests.yml:4-9,22`; `git diff
  code/src/model_checker/models/structure.py`; `specs/122_.../baselines/RELEASE-BASELINE.md`;
  `specs/125_.../PUBLISH-CHECKLIST.md`; `specs/125_.../rehearsal/parity-diff.md`;
  `specs/ROADMAP.md`; `git rev-list --left-right --count master...HEAD` → `0 48`
