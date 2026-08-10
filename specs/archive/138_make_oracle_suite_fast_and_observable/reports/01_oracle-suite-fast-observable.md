# Research Report: Make the oracle suite fast and observable

- **Task**: 138 - make_oracle_suite_fast_and_observable
- **Started**: 2026-08-06T00:00:00Z
- **Completed**: 2026-08-06T00:00:00Z
- **Effort**: ~2 hours (research)
- **Dependencies**: Task 133 (find_countermodel contract fix, status: implementing/partial)
- **Sources/Inputs**: see Appendix
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context (optional)

- **Upstream Dependencies**: Task 133's `find_countermodel`/`OracleTimeoutError` contract
  (`oracle/bimodal_logic/provider.py`, `errors.py`) — the three-way SAT/UNSAT/TIMEOUT
  classification this task's speed/observability work must preserve, not weaken.
- **Downstream Dependents**: Task 137 (13 resolved-and-wrong MC/BH disagreements) and the
  still-blocked Task 127 (oracle regression baseline) both depend on the suite being runnable
  and its verdicts trustworthy; neither is otherwise entangled with this task's structural fixes.
- **Alternative Paths**: None identified — the six problems are independent structural defects
  in the same two files (`oracle/run-oracle-suite.sh`, `oracle/conftest.py`) plus one test module
  (`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`).
- **Potential Extensions**: The heartbeat/JSON-artifact/completion-marker pattern developed here
  could generalize to other long-running suites in this repo (none currently exist at this scale).

## Executive Summary

- **Confirmed defect 1** (gating never deselects `slow`): `run-oracle-suite.sh` pass 1 runs
  `pytest "$repo_root/oracle" -n 6 -m "not xdist_serial" "$@"` — no `-m "not slow"`. Unlike
  `code/pyproject.toml`'s `addopts = "... -m \"not slow\""`, `oracle/` has no ini file of its own
  reachable from an `oracle/`-rooted or repo-root-rooted invocation (`oracle/conftest.py`'s own
  docstring documents this ini-discovery gap), so nothing deselects `@pytest.mark.slow` by
  default. `TestFullScanReport` (2 test methods, both `@pytest.mark.slow`, one is the 274-formula
  x2-solve self-consistency scan) therefore runs on every gating invocation. Task 133 Phase 7
  measured this scan alone at **3606.39s (1:00:06)**, and the two-pass suite *with* the scan
  included at **~76.7 minutes** total.
- **Confirmed defect 2** (no incremental output): `_generate_differential_report()` (the function
  `TestFullScanReport` uses) loops over all 274 formulas silently — no `print()`, no flush, no
  progress signal. Pytest itself only reports at test-function granularity, so even `-v` cannot
  show progress *inside* one 60-minute test. The only prior art for per-formula progress is an
  ad hoc, un-integrated script in the Task 133 evidence directory
  (`specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_instrumented.py`) — exactly
  what this task's description calls "proven ad hoc" and asks to promote into real tooling.
- **Confirmed defect 3** (no completion detectability): no JSON result artifact, no completion
  marker file, anywhere in `oracle/`. Task 133's own `evidence/verification-results.md` documents
  the concrete failure mode this produces: "Detach long runs and detect completion from the
  summary line, never from process liveness — a vanished PID is not a verdict," after the gating
  suite's own ~19-minute combined wall clock was measured as long enough to be mis-truncated by
  a naive 10-minute-timeout verification harness.
- **Confirmed defect 4** (no per-pass timeout): `run-oracle-suite.sh` has no `timeout` wrapper on
  either pytest invocation. The Nix devShell (`flake.nix`) ships `pytest` + `pytest-xdist` only —
  no `pytest-timeout` — but GNU coreutils `timeout` is present in the devShell's `$PATH`
  independent of Python packaging, making a bash-level wrap the lowest-friction fix.
- **Confirmed defect 5** (168/274 formulas burn full budget every run for zero information): the
  deployed constants in `test_cross_oracle_differential.py` (`SELF_SCAN_SOLVE_TIMEOUT_MS = 10000`,
  `MIN_CONCLUSIVE_SCAN_FORMULAS = 90`) are already annotated with the exact measurements the task
  description cites — 101/274 conclusive at 5000ms, 106/274 at 10000ms, 0 disagreements both
  times, and a code comment explicitly stating conclusiveness is "essentially budget-independent
  in this range." No population-level "known inconclusive" record exists yet — every gating (and
  exhaustive) run re-solves and re-times-out on the same ~168 formulas.
- **Confirmed defect 6** (undocumented split): `code/docs/core/TESTING_GUIDE.md` section 8.6
  ("Solver Timing Budgets and Machine Variance") is cited by both `conftest.py` and
  `run-oracle-suite.sh` for the *contention* mechanism, but the file contains **zero** mentions of
  "oracle" — the gating/exhaustive split itself, and the forthcoming three-way split (fast gating
  / conclusive-only assertion / periodic exhaustive re-derivation) have no documentation home yet.

## Context & Scope

Task 138 is one of two direct follow-ups from Task 133 (find_countermodel contract fix; the other
is Task 137, a soundness investigation, out of scope here). File scope is `oracle/` and
`code/docs/core/TESTING_GUIDE.md`. The task's hard constraint — speed must come from running less
redundant work, never from weakening assertions — means the soundness tooth (zero disagreements
among conclusive results, `_assert_scan_report`'s first assertion) and the conclusiveness floor
(`MIN_CONCLUSIVE_SCAN_FORMULAS`) must both survive unmodified in whatever gating variant emerges.

Current suite size: **559 tests** collected under `PYTHONPATH=code/src pytest oracle -q
--collect-only` (1.35s). Per Task 133's `evidence/verification-results.md`, the two gating passes
*excluding* `slow` take **~19 minutes combined** (541 passed/4 skipped/4 xfailed in 13:04 for pass
1, 7 passed in 6:02 for pass 2); the *exhaustive* complexity-5 scan alone adds up to ~60-90
minutes on top when not deselected.

## Findings

### 1. `run-oracle-suite.sh` gating/exhaustive split (Problem 1)

- File: `oracle/run-oracle-suite.sh`. Two passes, hard-coded:
  - Pass 1: `pytest "$repo_root/oracle" -n 6 -m "not xdist_serial" "$@"`
  - Pass 2: `pytest "$repo_root/oracle" -m "xdist_serial" "$@"`
  - Neither filters `slow`. Extra positional args (`"$@"`) are forwarded to both passes, so a
    caller *can* pass `-m "not slow"` manually today, but the script's own default does not.
- `oracle/bimodal_logic/README.md` (lines 73-99, "Running the Test Suite") documents exactly this
  two-pass invocation and the `xdist_serial` marker's purpose, but says nothing about `slow` —
  this README will need a parallel update alongside the script (it is inside `oracle/`, in scope).
- Two `@pytest.mark.slow` usages exist in the whole tree, both in
  `test_cross_oracle_differential.py`:
  - `test_temporal_only_agreement_complexity_5` (line ~1192) — conditional on BimodalHarness
    being importable (skips via `setup_method` otherwise); also carries the Task 137 strict
    `xfail`.
  - `class TestFullScanReport` (line 1693) — both its methods (`test_complexity_5_scan_self_consistent`,
    `test_report_writes_to_file`) inherit the class-level `@pytest.mark.slow`. Only the first is
    the expensive 274x2-solve scan; `test_report_writes_to_file` runs a cheap complexity-3 scan
    and is class-scoped under `slow` seemingly just by co-location, not by cost — worth flagging
    to the planner as a candidate to un-mark if the class is restructured.
- The task description's phrase "give the exhaustive sweep its own explicitly-invoked runner"
  most directly maps onto adding `-m "not slow"` to both passes in `run-oracle-suite.sh` (mirroring
  `code/pyproject.toml`'s own default) and creating a **separate** script (e.g.
  `oracle/run-oracle-exhaustive-scan.sh`) that explicitly selects `-m slow` (or invokes the scan
  logic directly, see Finding 2) — never bundled into the default gating invocation.

### 2. No per-formula progress signal exists inside pytest (Problem 2)

- `_generate_differential_report()` (`test_cross_oracle_differential.py:1374-1451`) is the
  function `TestFullScanReport.test_complexity_5_scan_self_consistent` calls. Its `for formula_json
  in formulas:` loop has no print, no flush, no counter — a 60-minute run inside this function is
  completely silent from pytest's perspective (one dot/line appears only when the *entire* test
  function returns).
- **Structural constraint the planner must account for**: pytest's own reporter grain is
  test-function-level, not sub-step-level. Making an in-progress 274-formula sweep observable
  through pytest's own output requires either (a) running with `-s` (disables output capture) plus
  in-loop `print(..., flush=True)`, (b) writing progress to a side-channel file (JSONL/log) that
  an external process tails, or (c) both — see next bullet.
- **Existing, proven-but-unintegrated prior art**:
  `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_instrumented.py`. It
  reimplements the same enumerate-and-solve-twice loop as a **standalone script** (not a pytest
  test), and already does exactly what Problem 2 + Problem 3 ask for:
  - Writes one JSONL record per formula (`idx`, `complexity`, both results/elapsed times/verdict,
    running disagreement/timeout counts) with `fh.flush()` after every line.
  - Prints a "loud line" for every formula that disagrees, times out, or takes >5s, plus a
    heartbeat every 10th formula and on the first — so a healthy run is never silent for more than
    ~10 formulas' worth of wall clock.
  - Ends with a single `# DONE total=... agreements=... disagreements=... timeouts=... wall=...`
    line — the closest existing thing to a completion marker, though it is a stdout print, not a
    file-based marker (see Problem 3).
  - This script imports directly from the pytest test module
    (`test_cross_oracle_differential._enumerate_primitive_formulas`, `_formula_complexity`), so it
    is not a parallel reimplementation of the enumerator — only of the report-generation loop
    (`_generate_differential_report`'s counterpart). Promoting it into `oracle/` proper likely
    means either (a) making `_generate_differential_report` itself accept an optional progress
    callback/heartbeat and reusing it from both the pytest test and a new standalone runner, or (b)
    keeping the standalone script as the sole exhaustive-scan entry point and reducing
    `TestFullScanReport` to a thin marker/compatibility shim. This is a design decision for the
    plan, not settled by research.

### 3. No completion marker, no JSON result artifact (Problem 3)

- No file matching `*.done`, `DONE_MARKER`, `completion.marker`, or similar exists anywhere under
  `oracle/`, `code/scripts/`, or `.claude/scripts/` — there is no precedent pattern in this repo to
  reuse; the design needs to be established here.
- `_write_report_json()` (line 1454) already exists and is used by
  `TestFullScanReport.test_report_writes_to_file` and several `TestDifferentialReport`/`TestCIGate`
  tests — but only against a `tempfile.NamedTemporaryFile` inside the test, deleted at the end.
  Nothing persists a report to a stable, discoverable path after a real run.
- `_generate_differential_report()`'s return dict already has exactly the fields Problem 3 asks
  for as a JSON artifact: `total_formulas`, `agreements`, `disagreements`, `timeout_count`,
  `timestamp`, plus per-entry detail. It is missing only wall-clock duration (start/end
  timestamps are the closest primitive already present via `timestamp`, but no elapsed-seconds
  field is computed).
- **The concrete "false completion via PID liveness" incident** the task description cites is
  documented in `specs/133_fix_oracle_self_consistency_disagreements/evidence/verification-results.md`'s
  "Note on run duration": the gating suite's own combined ~19-minute wall clock was long enough
  that "[a]ny verification harness that truncates a run at 10 minutes will cut pass 1 off
  mid-flight at roughly 91% and produce a misleading partial result," and the write-up's own
  fix-forward guidance is "[d]etach long runs and detect completion from the summary line, never
  from process liveness — a vanished PID is not a verdict." Task 133 Phase 7
  (`plans/02_find-countermodel-contract.md` lines 837-844) separately narrates tracking a
  multi-hour run "by PID and polled with bounded waits" as the *sanctioned* discipline at the
  time — i.e., PID-based polling was the only tool available, and it is exactly what this task is
  asked to replace with a marker-file-based contract.

### 4. No per-pass timeout on a stall (Problem 4)

- `run-oracle-suite.sh` invokes `pytest ...` directly with no `timeout` wrapper, and `pass1_status`
  / `pass2_status` are only ever set by that invocation's own exit code — an actual hang (Z3 wedged,
  a deadlocked xdist worker, etc.) blocks forever with zero signal to the caller.
- No `pytest-timeout` plugin is installed: `flake.nix`'s `devPython` package list is `[nixZ3
  setuptools pip networkx pytest pytest-xdist]` — no `pytest-timeout`. Adding it would mean a
  `flake.nix` change (out of this task's declared file scope, `oracle/` + `TESTING_GUIDE.md`).
- GNU coreutils `timeout` (9.11) is present in `$PATH` already (verified: `which timeout` /
  `timeout --version`), and the devShell's `shellHook` puts nothing special on `PATH` that would
  remove it — this is the lowest-friction mechanism: wrap each pytest invocation in
  `run-oracle-suite.sh` (and any new exhaustive-runner script) with `timeout <duration>s pytest
  ...`, check for exit code 124 (GNU `timeout`'s SIGTERM-fired-the-limit code) specifically so a
  timeout is reported distinctly from a genuine test failure, matching the "fails loudly" language
  in the task description.
- Precedent for "fails loudly" already exists in Task 133's own evidence: the retry-4 log
  (`specs/133_fix_oracle_self_consistency_disagreements/run/full-suite-retry4-1785988733.log`)
  shows pass 1 exiting **143** (128+15, SIGTERM) — some external mechanism already killed a stalled
  or over-budget run once before; this task's timeout wrapper should make that mechanism explicit
  and owned by `run-oracle-suite.sh` itself rather than an ad hoc external kill.

### 5. Known-inconclusive population (Problem 5)

- The complexity<=5 primitive-formula population is **fully deterministic and reproducible**:
  `_enumerate_primitive_formulas(5, ["p"])` (line 206) and its recursive helper
  `_enumerate_at_complexity` (line 229) are pure functions of `max_complexity`/`atoms` with a fixed
  enumeration order (complexity ascending; within a complexity, box/imp/untl/snce in that literal
  order) — the same 274-formula list is produced on every call, in every process, given unchanged
  source. This means a "known inconclusive set" can be recorded either as a formula-content
  manifest (canonical JSON per formula) or, more cheaply, as an index/id list into the existing
  enumeration order, without needing any new hashing/identity scheme.
- The two real (non-sampled) full-274 measurements already exist and are cited directly in the
  `SELF_SCAN_SOLVE_TIMEOUT_MS`/`MIN_CONCLUSIVE_SCAN_FORMULAS` code comments
  (`test_cross_oracle_differential.py:50-106`): 101/274 conclusive at 5000ms (pre-fix baseline),
  106/274 at 10000ms (deployed budget), 0 disagreements both times. The 10000ms run's raw JSONL is
  **not** currently persisted anywhere in the repo (only the 5000ms pre-fix run's JSONL survives,
  in `evidence/scan_5s_baseline.jsonl`, plus three unrelated 30-formula bounded samples at
  10/15/20s). A first exhaustive run under the new tooling will need to regenerate the canonical
  106/274 conclusive set from scratch and persist it — there is no existing artifact to
  grandfather in directly.
- Design tension the plan must resolve, not settled here: the task description asks the gating
  variant to "assert on the conclusive population and that the inconclusive set has not grown."
  Asserting the *conclusive* population's zero-disagreement property only requires re-solving the
  ~106 known-conclusive formulas (roughly 2x speedup over 274, since the other ~168 no longer burn
  their full budget). Asserting the inconclusive set "has not grown" is representationally
  cheaper still if read as a structural invariant (total population count == 274 given unchanged
  enumerator code, known-conclusive count >= a floor) rather than as "re-solve every known-timeout
  formula to confirm it still times out" — the latter would reproduce exactly the ~56-minute cost
  this problem exists to eliminate. The exhaustive variant remains the sole place that re-derives
  the whole 274-formula population and can therefore detect genuine drift (a previously-inconclusive
  formula newly resolving, or vice versa).
- `_assert_scan_report()` (line 549) already implements the two-tooth assertion (disagreements ==
  0 among conclusive; conclusive count >= floor) against an arbitrary report dict — this function
  is reusable as-is for a "gating, conclusive-subset-only" variant; it does not need to change, only
  what set of formulas is fed into `_generate_differential_report()` upstream of it.

### 6. TESTING_GUIDE.md documentation gap (Problem 6)

- Section 8.6 ("Solver Timing Budgets and Machine Variance", lines 587-634) is the section both
  `oracle/conftest.py`'s `xdist_serial` marker docstring and `run-oracle-suite.sh`'s header comment
  cite for the CPU-contention mechanism behind the *existing* two-pass split — but the actual text
  of 8.6 is generic Z3-variance guidance with no mention of `oracle/`, `run-oracle-suite.sh`, or the
  gating/exhaustive split at all (`grep -i oracle TESTING_GUIDE.md` returns nothing).
- The Table of Contents (lines 19-28) stops at "8. Best Practices and Patterns" with 8.1-8.7 as
  subsections; a new **8.8** subsection (e.g. "Oracle Suite: Gating vs. Exhaustive Split") fits the
  existing numbering scheme immediately after 8.7 ("Regression Testing") and is the natural home
  for documenting: the `not slow` gating default, the separate exhaustive-scan runner, the
  known-conclusive-population assertion strategy, the completion-marker/JSON-artifact contract, and
  the per-pass timeout.
- `oracle/bimodal_logic/README.md` and `oracle/run-oracle-suite.sh`'s own header comment are two
  additional in-`oracle/`-scope places that already describe the two-pass split and will need
  parallel updates once a third pass/split concept (gating vs. exhaustive) exists, to avoid the
  same drift risk this task's Finding 1 identified between `code/pyproject.toml`'s ini-scoped
  default and `oracle/`'s lack of one.

## Decisions

- None made by this research pass — task 138 file scope (`oracle/`, `code/docs/core/TESTING_GUIDE.md`)
  and the hard constraint (speed from doing less redundant work, never weaker assertions) are
  taken as fixed inputs to planning, not decisions of this report.

## Recommendations

1. **Add `-m "not slow"` to both `run-oracle-suite.sh` passes** (mirroring `code/pyproject.toml`'s
   own default), closing the ini-discovery gap `oracle/conftest.py` already documents but does not
   itself close for the `slow` marker.
2. **Create a separate, explicitly-invoked exhaustive-scan runner** (e.g.
   `oracle/run-oracle-exhaustive-scan.sh`) that selects `-m slow` (or invokes the scan logic
   directly) and is never part of the default gating path.
3. **Give `_generate_differential_report()` (or a new wrapper) an optional heartbeat/progress
   hook**, reusing the proven shape from `evidence/scan_instrumented.py` (flushed per-formula JSONL
   + periodic console heartbeat) rather than re-deriving from scratch, and decide whether
   `TestFullScanReport` keeps calling the shared loop or is retired in favor of the standalone
   script — a plan-level decision, not resolved here.
4. **Persist a JSON result artifact + a distinct completion-marker file** (e.g.
   `<result>.json` written, then a zero-byte or content-bearing `<result>.done` created last) at a
   stable, documented path after the exhaustive scan, and update any runner/verification tooling
   to poll for the marker's existence rather than a PID — directly resolving the incident
   documented in Task 133's `verification-results.md`.
5. **Wrap both `run-oracle-suite.sh` pytest invocations (and the new exhaustive runner) in GNU
   `timeout`**, distinguishing exit code 124 (timeout fired) from a genuine test failure in the
   script's final summary output — no new Nix dependency required.
6. **Record the known-conclusive-formula population from a fresh exhaustive run** (the 10000ms/106-
   conclusive run's raw data does not currently exist in the repo) as the input to a new,
   fast gating assertion that reuses `_assert_scan_report()` unchanged against a filtered formula
   subset, while leaving the full 274-formula re-derivation to the exhaustive variant only.
7. **Add TESTING_GUIDE.md section 8.8** documenting the gating/exhaustive split, the
   known-conclusive-population strategy, and the completion-marker contract, and update
   `oracle/bimodal_logic/README.md` + `run-oracle-suite.sh`'s header comment in the same pass to
   avoid the three docs drifting relative to each other (the same drift class as Finding 1).

## Risks & Mitigations

- **Risk**: A "known-inconclusive set" implemented as a hard-coded skip list could silently mask a
  real regression if a previously-timing-out formula starts disagreeing once it becomes solvable
  (e.g. after a future contract or solver change). **Mitigation**: keep the exhaustive variant as
  the sole source of truth that re-derives the full population "periodically" (task description's
  own phrase) and treat any exhaustive-run population change as a signal requiring the gating
  manifest to be regenerated — not something the gating pass silently absorbs.
- **Risk**: Moving the exhaustive scan out of pytest into a standalone script risks losing pytest's
  existing `_assert_scan_report`/`_write_report_json` reuse and duplicating logic (the exact
  drift `scan_instrumented.py` already represents). **Mitigation**: factor the shared
  enumerate-solve-compare loop into one function usable from both a thin pytest test and a
  standalone CLI entry point, rather than maintaining two independent implementations.
- **Risk**: `timeout`-wrapping a pytest-xdist parallel pass (`-n 6`) may leave orphaned worker
  processes if `timeout` SIGTERMs the parent without cleanly propagating to workers.
  **Mitigation**: verify worker cleanup behavior in the plan's testing phase (e.g. `ps aux | grep
  pytest` after a deliberately-triggered timeout), and consider `timeout --kill-after=Ns` as a
  fallback SIGKILL if SIGTERM does not propagate.

## Appendix

- References:
  - `oracle/run-oracle-suite.sh` — current two-pass gating runner (no `slow` filter, no timeout)
  - `oracle/conftest.py` — marker registration; documents the ini-discovery gap for `oracle/`
  - `oracle/bimodal_logic/README.md` (lines 60-111) — documents the current two-pass convention
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — `SELF_SCAN_SOLVE_TIMEOUT_MS`/
    `MIN_CONCLUSIVE_SCAN_FORMULAS` (lines 50-106), `_enumerate_primitive_formulas`/
    `_enumerate_at_complexity` (206-276), `_reference_verdict` (489-518), `_assert_scan_report`
    (549+), `_generate_differential_report`/`_write_report_json` (1374-1462), `TestFullScanReport`
    (1693-1756), `TestCIGate` (1762-1892)
  - `oracle/bimodal_logic/provider.py` (170+) / `errors.py` — `find_countermodel`/
    `OracleTimeoutError` contract this task must not weaken
  - `code/pyproject.toml` (lines 82-110) — `addopts = "... -m \"not slow\""` default that `oracle/`
    lacks an equivalent of
  - `code/docs/core/TESTING_GUIDE.md` (Table of Contents lines 19-28; section 8.6 lines 587-634,
    8.7 lines 635-656) — documentation gap and insertion point
  - `flake.nix` (lines 55-124) — devShell package list (`pytest`, `pytest-xdist`, no
    `pytest-timeout`); confirms `oracle/` is outside `checks.default`'s hermetic gate
  - `specs/133_fix_oracle_self_consistency_disagreements/evidence/verification-results.md` — the
    ~19-minute gating wall clock, the PID-liveness false-completion risk, the 101/274 vs 106/274
    conclusiveness measurements
  - `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_instrumented.py` — the ad
    hoc progress-reporting script this task is asked to promote into real tooling
  - `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_5s_baseline.jsonl` /
    `scan_5s_baseline_complete.log` — pre-fix baseline run data (274/274 "agree" under the old
    timeout-conflated contract; illustrates why this data cannot be reused as-is for the
    known-inconclusive manifest)
  - `specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`
    (Phase 7, lines 830-end) — PID-tracking discipline narrative, full-suite failure breakdown,
    "floor not adjusted" deviation
  - `specs/133_fix_oracle_self_consistency_disagreements/run/full-suite-retry4-1785988733.log` —
    observed exit 143 (SIGTERM) on a prior run, evidence some external kill mechanism already
    exists informally
