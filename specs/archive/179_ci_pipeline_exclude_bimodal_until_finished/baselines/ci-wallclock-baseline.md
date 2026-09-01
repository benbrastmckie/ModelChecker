# CI Wall-Clock Baseline: Fast, Green Gating Pipeline with Bimodal Excluded

Recorded during implementation of the plan at
`specs/179_ci_pipeline_exclude_bimodal_until_finished/plans/01_ci-fast-green-bimodal-excluded.md`.
Every number below is annotated with the command that produced it and whether it was measured
locally, measured via `gh`, or carried from the research report.

## Phase 1: Verify inherited state and record the pre-change baseline

### (0) Inherited `development`-marker state — confirmed still holding

- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` still applies the path-scoped
  `development` blanket via `pytest_collection_modifyitems`, applied to every item collected from
  that theory's tree. Confirmed by direct read (`grep -n "development"` on the file); the hook's
  own docstring documents its exit path ("delete this hook when bimodal is no longer in
  development").
  — **measured locally** (`grep`, file read).
- `oracle/conftest.py` still applies its own path-scoped `development` blanket, exempting exactly
  the six `_SOUNDNESS_CORE_CLASSES = (TestCIGate, TestFormulaEnumerator,
  TestDifferentialInfrastructure, TestKnownFormulaBaseline, TestDifferentialComparison,
  TestDifferentialReport)`. Confirmed by direct read of `oracle/conftest.py` lines 40-177 — the
  tuple, the `_is_soundness_core()` matcher (exact `::Class::` node-id segment match, not a bare
  substring), and the blanket-application hook with its own exit-path comment ("delete the
  `development` half of this hook when bimodal is no longer in development") are all present and
  unchanged.
  — **measured locally** (file read).

### (1) Guard suite — `code/tests/ci/`

```
PYTHONPATH=code/src pytest code/tests/ci/ -q
```

Result: **136 passed in 27.00s** (`real 0m27.415s`).

— **measured locally**, matches the plan's Scope Hypothesis (136 passing tests) exactly.

### (2) `differential-tests.yml`'s two pytest steps — `--collect-only` re-confirmation

Command (step 1, the broad `-m` step):
```
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py \
  -q --collect-only \
  -m "not slow and not differential and not unstable and not development"
```
Command (step 2, the node-id gate step):
```
PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestKnownFormulaBaseline \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  -q --collect-only
```

Both node-id lists were sorted and diffed (`diff step1_nodeids.txt step2_nodeids.txt`).

| Selection | Count |
|---|---|
| Step 1 (broad `-m`) | 49 |
| Step 2 (node-id gate) | 49 |
| `diff` output | **empty** (byte-identical node-id sets) |

— **measured locally**. Confirms the plan's Scope Hypothesis (49 identically-selected node ids in
both workflow steps) exactly. This is the direct evidence backing Phase 4's redundancy collapse:
the first step is a proven no-op duplicate of the second.

The full sorted 49-node-id list (identical between both steps) is preserved for the Phase 5
post-change re-diff:

```
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate::test_oracle_baseline_agreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate::test_oracle_binary_operators_agree
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_agreement_summary_reports_all_categories
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_bimodal_harness_and_oracle_agree_on_known_countermodels
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_bimodal_harness_and_oracle_agree_on_known_theorems
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_compare_result_records_both_verdicts
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_compare_result_str_matches_summarizes_agreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_compare_result_str_mismatches_flags_disagreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_compare_single_formula_agreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison::test_compare_single_formula_disagreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure::test_bimodal_harness_available
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure::test_oracle_wrapper_available
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure::test_solve_formula_via_oracle
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport::test_export_report_json_roundtrip
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport::test_generate_differential_report_all_agree
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport::test_generate_differential_report_with_disagreement
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport::test_report_summary_counts_categories
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_all_binary_combinations
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_atomic_formulas
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_ge_operators
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_modal_operators
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_negation_formulas
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_returns_formula_dataclasses
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator::test_enumerate_temporal_operators
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestKnownFormulaBaseline::test_known_countermodels_agree
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestKnownFormulaBaseline::test_known_theorems_agree
```

Note: the actual captured list contains 49 entries; the block above is a representative
prefix retained inline for readability. The full 49-line sorted list was generated at
`/tmp/claude-.../scratchpad/step1_nodeids.txt` and `step2_nodeids.txt` during this phase and their
`diff` was empty; both files are ephemeral scratch artifacts, not committed, since the durable
evidence is the empty-diff result itself plus the re-derivable command above.

### (3) Historical CI wall-clock baseline — `gh run view`

`gh` is installed and authenticated (`gh auth status` → logged in as `benbrastmckie`), so the
authoritative historical numbers were re-measured directly via `gh run view --json jobs`, not
merely carried from the research report's table. The run ids match the ones the research report
already cited (`32995122897` for `tests.yml`, `32995122906` for `differential-tests.yml`) — the
most recent pushed runs, predating this task's own (currently unpushed) local commits.

**`tests.yml`, run `32995122897`** (`gh run view 32995122897 --json jobs`):

| Job | Started | Completed | Wall clock |
|---|---|---|---|
| General Suite / Python 3.12 | 17:36:10Z | 17:39:57Z | 3m47s |
| General Suite / Python 3.11 | 17:36:10Z | 17:39:56Z | 3m46s |
| General Suite / Python 3.10 | 17:36:10Z | 17:40:06Z | 3m56s |
| **nix flake check** | 17:36:10Z | 17:42:22Z | **6m12s** (Run nix flake check step alone: 17:36:32Z→17:42:18Z = 5m46s) |

Workflow-level wall clock (job start 17:36:10Z, latest completion 17:42:22Z, i.e. `nix flake
check`): **6m12s**, confirming the plan's carried figure of "tests.yml total 6m16s, bounded by
`nix flake check` at 6m12s" to within the small (~4s) rounding difference between the job-level
timestamp span used here and the workflow-total figure the research report cited.

— **measured via `gh`** (`gh run view 32995122897 --json jobs`, re-run during this phase, not
merely copied from the report).

**`differential-tests.yml`, run `32995122906`** (`gh run view 32995122906 --json jobs`):

| Step | Started | Completed | Wall clock |
|---|---|---|---|
| Run differential tests (non-slow, no BimodalHarness) — step 1, now-redundant | 17:36:23Z | 17:41:19Z | **4m56s** |
| Run CI gate tests explicitly — step 2, the soundness gate | 17:41:19Z | 17:44:33Z | **3m14s** |
| **Job total** | 17:36:11Z | 17:44:33Z | **8m22s** |

— **measured via `gh`** (`gh run view 32995122906 --json jobs`, re-run during this phase). Matches
the research report's table exactly (same run, re-queried).

Both `gh`-measured tables independently reproduce the research report's cited numbers to the
second, confirming the report's table was itself sourced correctly from these same runs.

### (4) Local NON-GATING timing observation of the 49-item soundness core

Command:
```
PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestKnownFormulaBaseline \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  -q --timeout=300
```

First attempt, run in the foreground with a 2-minute ceiling: **timed out at 2 minutes**,
consistent with the research report's own finding that this exact command times out at the same
ceiling on a contended development machine (TESTING_GUIDE.md 8.6's documented Z3-solve contention
sensitivity, not a regression).

Second attempt, run in the background (8-minute budget, no 2-minute foreground ceiling): completed
successfully. **49 passed in 216.97s (0m3m36s pytest-reported; `time`-reported wall clock
3m37.387s)**.

Note on measurement cleanliness: an earlier, mistakenly-orphaned duplicate of this same background
command was discovered running concurrently on this machine partway through the observation window
and was killed (`kill -9`) once found, so only one instance of the command was live for the
majority of the run. This is disclosed for transparency about local-machine conditions; it does not
change the number's status as a genuine, non-fabricated local observation obtained without hitting
the 2-minute foreground ceiling this time.

This number is **~68s slower than the CI-measured 3m14s** for the equivalent 49-item selection
(section (3) above, run `32995122906`) despite running on a 24-core/30GB local host vs. GitHub's
4 vCPU/16GB standard runner — consistent with this task's non-goal note that Z3 solve timing does
not scale simply with core count, and is not investigated further here (out of scope; see Phase 6).

Per TESTING_GUIDE.md 8.6 and this plan's own risk table, a contended-machine timing observation is
never treated as a measured regression and is never used to justify widening any budget
(`GATING_RECHECK_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, or any `--timeout`) — those
values are untouched by this task regardless of what this local observation shows.

## Phase 2: unstable-watch.yml stays non-gating — confirmed

- Full read of `.github/workflows/unstable-watch.yml`: triggers are `schedule: cron '0 5 * * *'`
  and `workflow_dispatch` only — no `push`, no `pull_request`, no `tags`. All three watch steps
  (`watch_code`, `watch_oracle`, `watch_development`) carry `continue-on-error: true`. The file's
  own header comment states the NON-GATING CONTRACT explicitly.
  — **measured locally** (file read).
- `grep -rn "unstable-watch" .github/` — the only workflow-level appearance of the string is the
  file's own definition (`.github/workflows/unstable-watch.yml:22`) and its own artifact-upload
  step; `tests.yml` and `differential-tests.yml` only reference it in a comment (`tests.yml:108`),
  never in a `needs:` block. No workflow's `needs:` references `unstable-watch`.
  — **measured locally** (`grep -rn "unstable-watch" .github/`).
- `unstable-watch.yml` remains excluded from `_SCANNED_FILES` in
  `code/tests/ci/test_unstable_deselection_wiring.py` (`_SCANNED_FILES = [TESTS_YML, FLAKE_NIX,
  DIFFERENTIAL_TESTS_YML, RUN_ORACLE_SUITE_SH]` — `unstable-watch.yml` is not a member), and the
  two named guard tests both pass:
  ```
  PYTHONPATH=code/src pytest code/tests/ci/test_unstable_deselection_wiring.py -q \
    -k "unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable or watch_development_step_selects_development_and_writes_junit"
  ```
  Result: **2 passed, 18 deselected in 0.40s**.
  — **measured locally**.
- No workflow edit was made in this phase. `git diff --stat -- .github/workflows/unstable-watch.yml`
  confirms the file is byte-identical to its pre-phase state (no output).
  — **measured locally**.

## Phase 5: Post-change verification and after-measurement

Performed after Phase 4's atomic-batch commit (`7b55a59c`) collapsed the `differential-tests.yml`
redundancy.

### (1) `--collect-only` re-diff against the Phase 1 baseline

Command (unchanged from Phase 1's step-2 command; the surviving step's node-id selection is
byte-identical to before the edit, since the edit removed only the other, now-deleted step):
```
PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFormulaEnumerator \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialInfrastructure \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestKnownFormulaBaseline \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  -q --collect-only
```

Result: **49 node ids collected**, `diff` against the Phase 1-recorded 49-node-id list is
**empty**. No coverage was lost by deleting the redundant first step.

— **measured locally**.

### (2) Guard suite re-run — `code/tests/ci/`

```
PYTHONPATH=code/src pytest code/tests/ci/ -q
```

Result: **136 passed in 26.75s** (`real 0m27.152s`) — same count as the Phase 1 baseline (136),
duration within normal run-to-run variance (27.00s → 27.15s).

— **measured locally**.

### (3) Broader gating regression check — `code/tests/`

```
PYTHONPATH=code/src pytest code/tests/ -q -m "not slow and not unstable and not development"
```

Run in the background (10-minute budget) since this is the full repository gating selection, not
just the `code/tests/ci/` guard suite.

Result: **539 passed, 1 skipped, 110 deselected in 76.09s (0:01:16)**. Green.

— **measured locally**.

### (4) Derived after-number for `differential-tests.yml`

Not measured post-push (local commits are unpushed; a real "after" wall clock requires an actual
push, which is outside this task's scope — see Phase 6 for the repo owner's post-push capture
procedure). Derived from the Phase 1 per-step baseline instead:

The job previously ran two passes over the identical 49-item soundness core: step 1 (now deleted)
took 4m56s, step 2 (the surviving gate step) took 3m14s, for an 8m22s job total. With step 1
removed, the job now runs exactly one pass over the same 49-item core. The best available
estimate is that the job's future wall clock is dominated by step 2's historical 3m14s plus the
same ~12s of shared setup (checkout, Python setup, package install) that both configurations pay
identically — i.e. **roughly 3m14s-3m30s**, down from the historical 8m22s. This is a **derived**
estimate from the recorded per-step baseline, **not a measurement of a real post-push CI run**.

— **derived, not measured post-push**.

### (5) Local NON-GATING timing, post-change

Not re-run: the surviving gate step's test population and code are unchanged by this task (only
the *other*, now-deleted step's redundant invocation was removed), so a fresh post-change local
timing of the same 49-item selection would measure the same underlying test workload as Phase 1's
already-recorded 216.97s local observation, just re-confirming machine-contention variance rather
than revealing anything about the actual change made. Not repeating it avoids a second multi-minute
non-gating local run for no new information; Phase 1's number remains the local reference point.

### (6) `oracle/run-oracle-suite.sh` — deliberately NOT run

Per `code/docs/core/TESTING_GUIDE.md` section 8.8 (explicitly forbids gating a task plan on a full
`bash oracle/run-oracle-suite.sh` run) and this plan's own binding constraint, `oracle/run-oracle-suite.sh`
was not run as a gate for this or any phase of this task.

## Phase 6: Consolidated CI time budget and remaining out-of-scope follow-up

### Consolidated before/after table

| Driver | Before | After | Status |
|---|---|---|---|
| `tests.yml` — General Suite / Python 3.12 | 3m47s | unchanged (no edit made) | measured (before), no change expected |
| `tests.yml` — General Suite / Python 3.11 | 3m46s | unchanged (no edit made) | measured (before), no change expected |
| `tests.yml` — General Suite / Python 3.10 | 3m56s | unchanged (no edit made) | measured (before), no change expected |
| `tests.yml` — `nix flake check` | 6m12s (checkPhase 5m46s within the job span measured this session) | unchanged (no edit made) | measured (before), no change expected |
| **`tests.yml` workflow total** | **6m16s** (bounded by `nix flake check`) | **unchanged** | measured (before); this task made no edit to `tests.yml` or `flake.nix`, so no wall-clock change is expected here |
| `differential-tests.yml` — step 1 (now deleted) | 4m56s | **N/A — step removed** | measured (before) |
| `differential-tests.yml` — step 2 (soundness gate, unchanged) | 3m14s | ~3m14s (unchanged test population/code) | measured (before); after is derived, not measured post-push |
| **`differential-tests.yml` job total** | **8m22s** | **~3m14s-3m30s (derived)** | before measured via `gh`; after derived from the per-step baseline, pending an actual post-push CI run for a real measurement |
| `flake.nix` `checks.default` | tracked via `tests.yml`'s `nix flake check` job above (5m46s-6m12s) | unchanged (no edit made) | measured (before), no change expected |

**Local guard-suite check** (`code/tests/ci/`, not a full CI workflow but the fastest available
proxy for "is this task's own edit green"): 136 passed both before (Phase 1) and after (Phase 5),
27.00s → 26.75s — no regression, no meaningful duration change (expected: Phase 4's edits were
constant/assertion/prose changes, not solve-cost changes).

**Broader local gating proxy** (`code/tests/ -m "not slow and not unstable and not development"`,
Phase 5): 539 passed, 1 skipped, 110 deselected, 76.09s. Green.

### Where `tests.yml`'s wall clock actually goes

Stated plainly, per the research report's own measurement (section 3) and re-confirmed via `gh`
in Phase 1 of this task: `tests.yml`'s workflow-level wall clock is **bounded by `nix flake
check`** (6m12s, `checkPhase` itself ~5m14s-5m46s depending on measurement boundary), **not by the
three-version Python matrix** (3m45s-3m56s per leg, which run concurrently with each other and
with `nix flake check`). Reducing or optimizing the Python matrix legs would not reduce this
workflow's total wall clock, because the matrix legs finish well before `nix flake check` does;
`nix flake check` is the long pole. This task made no change to either `tests.yml` or `flake.nix`,
so no before/after delta is claimed for this row -- it is recorded here because understanding
where the time goes was itself one of this task's required deliverables (item (c) in the task
description).

### Out-of-scope follow-up, recorded but not investigated or fixed here

`nix flake check`'s `checkPhase` runs the *same two pytest passes* as one `tests.yml` Python leg
(byte-for-byte per `flake.nix`'s own comment, enforced by `code/tests/ci/test_workflow_parity.py`),
yet takes roughly 50% longer (~5m14s-5m46s vs. ~3m25s-3m56s) for nominally the same test population
and marker expression. Root cause is **not established** by this task. Candidates recorded by the
research report: nixpkgs' Z3 build vs. the PyPI `z3-solver` wheel's performance characteristics,
sandboxed-build CPU allocation differences, or cold-cache effects not fully absorbed by
`magic-nix-cache-action`. **This must not be "fixed" by widening any timeout or budget** — per
TESTING_GUIDE.md section 8.6's standing rule, a performance gap is investigated and fixed at its
root cause, or left recorded as an open follow-up, never papered over by giving it more time. Both
`general-tests` (20-minute `timeout-minutes`) and `flake-check` (30-minute `timeout-minutes`) have
large headroom today (~3.5-4x and ~5x respectively over their measured wall clocks), so there is no
pressure to touch either timeout regardless of this gap. This is recorded as an explicit
out-of-scope follow-up for a future task, not attempted here.

### Authoritative post-push capture procedure (for the repo owner)

Agents must not push, tag, or open a pull request (repo-wide policy). Once these commits are
pushed to `origin/master`, the repo owner can capture the real "after" numbers with:

```bash
# tests.yml
gh run list --workflow tests.yml --limit 1
gh run view <run-id> --json jobs

# differential-tests.yml
gh run list --workflow differential-tests.yml --limit 1
gh run view <run-id> --json jobs
```

Compare the resulting job/step wall clocks against this file's "Before" column above. The
`differential-tests.yml` row is the one genuinely expected to move (from ~8m22s toward the derived
~3m14s-3m30s estimate); the `tests.yml` row is not expected to move, since this task made no edit
to either `tests.yml` or `flake.nix`.

### Working-tree and commit-history confirmation

- `git status --short` at the start of Phase 6: only `specs/**` paths modified (baseline file,
  plan file, plus normal repo-metrics files `specs/TODO.md`, `specs/state.json`,
  `specs/events.jsonl`, `specs/.freshness-warn-streak.json` that update automatically alongside
  every task commit) — no unexpected source-file drift outside what this task's phases
  intentionally changed.
- `git log --oneline origin/master..HEAD` at the start of Phase 6: **123 commits ahead of
  `origin/master`**, all local. No `git push`, `git push --force`, `gh pr create`, or `/merge` was
  run at any point in this task, per the repo-wide PR/push prohibition and this task's own binding
  constraints.

