# Implementation Plan: Make the oracle suite fast and observable

- **Task**: 138 - make_oracle_suite_fast_and_observable
- **Status**: [IMPLEMENTING]
- **Effort**: 11 hours agent work (plus ~2 hours unattended wall clock for the Phase 4 exhaustive derivation run)
- **Dependencies**: Task 133 (`find_countermodel`/`OracleTimeoutError` contract) — its three-way SAT/UNSAT/TIMEOUT classification is a fixed input this plan must preserve, never weaken
- **Research Inputs**: specs/138_make_oracle_suite_fast_and_observable/reports/01_oracle-suite-fast-observable.md
- **Artifacts**: plans/01_oracle-suite-fast-observable.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The `oracle/` suite is a ~76-minute black box: its gating runner never deselects the `slow`
marker, so a 274-formula x 2-solve exhaustive sweep runs on every invocation; the sweep emits
nothing until it finishes; completion is undetectable except by PID liveness (which already
produced one false completion report); there is no per-pass timeout; and ~168 of the 274
formulas exhaust their full solve budget every run to rediscover the same timeouts. This plan
splits the suite into a fast gating variant and an explicitly-invoked exhaustive variant, promotes
the ad hoc per-formula progress reporting into the shared scan core, adds a JSON result artifact
plus a definitive completion marker, wraps every pass in a bounded `timeout`, and records a
persisted known-conclusive baseline so the gating variant asserts on the conclusive population
instead of re-deriving the timeout set. Definition of done: `run-oracle-suite.sh` completes in
roughly 20 minutes with both assertion teeth intact, the exhaustive sweep is a separate script
that streams progress and lands machine-readable artifacts, and the split is documented.

### The hard constraint, restated as an implementation rule

**Speed comes only from running less redundant work, never from weakening assertions.** Concretely,
for the duration of this task:

- `_assert_scan_report()` (test_cross_oracle_differential.py:549) is **not modified**. Both its
  teeth — `disagreements == 0` among conclusive results (soundness) and `conclusive >=
  min_conclusive` (performance floor) — survive verbatim. Only the *set of formulas fed into it*
  changes for the gating variant.
- `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` and `MIN_CONCLUSIVE_SCAN_FORMULAS = 90` are **not raised,
  lowered, or otherwise retuned**. The exhaustive variant keeps asserting against them unchanged.
- No test is deleted, skipped, or `xfail`-ed to make a run green. Tests move between the gating
  and exhaustive passes; nothing leaves the suite.
- The new gating floor (Phase 5) is derived from measurement and set *tight*, not loose. If a
  gating run misses it, the response is to investigate — never to lower the floor.

Any phase that cannot meet its verification criteria without touching one of the above must stop
and report, not proceed.

### Research Integration

All six defects were confirmed with file/line evidence; this plan adopts the research
recommendations with three plan-level decisions the research explicitly left open (see Decisions
below). Load-bearing findings carried into the phases:

- `run-oracle-suite.sh` pass 1 is `-m "not xdist_serial"` with no `slow` filter, and `oracle/` has
  no reachable ini file, so nothing deselects `slow` (Finding 1).
- `_generate_differential_report()` (line 1374) loops over all formulas with no print/flush/counter;
  pytest's reporter grain is test-function-level, so in-loop flushed prints plus a side-channel
  file are the only mechanisms that can make an in-flight sweep observable (Finding 2).
- `_generate_differential_report()`'s return dict already carries `total_formulas`, `agreements`,
  `disagreements`, `timeout_count`, `timestamp`; only elapsed wall clock is missing (Finding 3).
- GNU `timeout` 9.11 is on `$PATH` in the devShell; `pytest-timeout` is not installed and adding it
  would require a `flake.nix` change outside file scope (Finding 4).
- The complexity<=5 enumeration is a pure, deterministic function of `max_complexity`/`atoms` with a
  fixed order, so a baseline can be recorded as indices into that order — but see Decision D3 for
  why indices alone are not safe (Finding 5).
- `evidence/scan_instrumented.py` is the proven prior art: flushed per-formula JSONL, loud lines for
  slow/disagreeing/timing-out formulas, periodic heartbeat, terminal `# DONE` summary (Finding 2).

**Quantified prize** (computed during planning from `evidence/scan_5s_baseline.jsonl`, the surviving
274-formula run): the 101 formulas that solved fast account for **101 seconds** of total solve time,
while all 274 account for **1868 seconds (31.1 min)** at the 5000ms budget. At the deployed 10000ms
budget the ~168 inconclusive formulas burn ~168 x 2 x 10s ~= 56 minutes — matching the task
description's measurement exactly. The conclusive subset is therefore roughly **2 minutes of solve
time**, and the maximum single fast solve observed was 4.62s. This is the measured basis for
expecting the gating scan to cost ~2 minutes while removing ~56.

### Prior Plan Reference

No prior plan exists for this task. Task 133's plan
(`specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`) is
referenced only as the source of the effort calibration and the PID-liveness incident narrative
this task exists to fix; none of its phases are reused.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` in delegation context, no
`roadmap_flag`). No roadmap phases added.

## Decisions

Three design questions the research deliberately left to planning, settled here so implementation
does not relitigate them:

- **D1 — One scan core, two entry points.** The instrumentation lands *inside*
  `_generate_differential_report()` as optional, default-`None` parameters (`progress_path`,
  `heartbeat_every`, `artifact_dir`). Defaults preserve current behaviour exactly, so the ~30
  existing call sites are untouched. Both the pytest exhaustive test and the new standalone CLI
  call this one function. This directly answers the research's duplication risk: there is never a
  second enumerate-solve-compare loop to drift.
- **D2 — The exhaustive runner drives pytest, not a reimplementation.** Because D1 puts artifact
  emission in the shared core, `pytest oracle -m slow -s` produces the progress stream, JSONL,
  JSON artifact and completion marker on its own. The standalone CLI (`oracle/scan_runner.py`)
  exists as a thin second entry point for bounded/ad-hoc runs (`--limit`, `--timeout-ms`,
  `--out-dir`) — the capability that proved essential during the contract work — not as the
  primary path.
- **D3 — Baseline identity is (index, canonical formula JSON), not index alone.** Recording bare
  indices would silently misalign if the enumerator ever changes. The manifest stores the total
  population count, and for each known-conclusive formula both its index and its canonical
  formula JSON. The gating test re-enumerates and cross-checks both before solving anything; a
  mismatch fails loudly with "re-derive the baseline", never silently proceeds.

## Goals & Non-Goals

**Goals**:

- `oracle/run-oracle-suite.sh` deselects `slow` on both passes and finishes in ~20 minutes.
- An explicitly-invoked `oracle/run-oracle-exhaustive-scan.sh` runs the full 274-formula sweep.
- Every long run streams per-formula progress with a bounded-interval heartbeat, so no run is ever
  silent for more than a known interval.
- Every scan run emits a machine-readable JSON result (total / conclusive / disagreements /
  inconclusive / wall clock) and a completion marker written last; runners detect completion from
  the marker, never from PID liveness.
- Every pytest pass and the exhaustive scan are wrapped in a bounded `timeout` that fails loudly
  and distinguishes a timeout from a test failure.
- A persisted known-conclusive baseline lets the gating variant assert the soundness tooth over the
  conclusive population, and assert the inconclusive set has not grown, without re-solving the
  known-timeout set.
- The split is documented in TESTING_GUIDE.md section 8.8, `oracle/bimodal_logic/README.md`, and
  `run-oracle-suite.sh`'s own header comment, so the three cannot drift.

**Non-Goals**:

- Changing `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_SCAN_FORMULAS`, or `_assert_scan_report()`.
- Investigating *why* ~168 formulas are inconclusive, or making them conclusive (that is a solver
  performance question, out of scope).
- Resolving the 13 MC/BH disagreements (Task 137) or unblocking the oracle regression baseline
  (Task 127).
- Adding `pytest-timeout` or any other dependency (would require a `flake.nix` change outside the
  declared file scope of `oracle/` + `code/docs/core/TESTING_GUIDE.md`).
- Reducing the exhaustive sweep's runtime. The exhaustive variant is allowed to be slow; it is
  simply no longer on the gating path.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A hard-coded known-conclusive list masks a real regression if a previously-timing-out formula becomes solvable and then disagrees | H | M | The exhaustive variant remains the sole re-deriver of the full population and is the only place drift can be detected; Phase 7 documents that any exhaustive-run population change requires regenerating the gating manifest, never silent absorption. The gating test additionally asserts total population == baseline total, so an enumerator change is caught immediately. |
| Baseline derived under contention or a wedged machine bakes in an artificially small conclusive set, permanently weakening gating coverage | H | M | Phase 4 derives the baseline from a **serial** run (no `-n`), with no competing pytest processes (checked via `ps aux \| grep pytest` per TESTING_GUIDE 8.6), and records the run's wall clock and budget in the manifest. Phase 4 verification requires the conclusive count to land within a stated tolerance of the documented 106/274; a materially smaller result is a stop-and-report condition, not a new baseline. |
| Extracting the scan into a standalone script duplicates logic and drifts from the pytest path | M | L | Decision D1: instrumentation lives in the single shared `_generate_differential_report()`; the CLI is a thin entry point with no loop of its own. Phase 2 verification explicitly greps that the CLI contains no `for formula` solve loop. |
| `timeout` SIGTERM on a `-n 6` xdist parent leaves orphaned workers | M | M | Use `timeout --kill-after=60s`; Phase 6 verification deliberately triggers a timeout with a tiny budget and confirms via `ps aux \| grep pytest` that no workers survive. |
| The gating conclusive scan runs under `-n 6` contention and erodes the conclusive rate, causing flaky floor misses | M | H | Mark the gating scan `xdist_serial` so it runs in pass 2 with zero sibling workers — the same mechanism the suite already uses for budget-sensitive tests. Costs ~2 minutes serial (measured basis above) and makes the floor deterministic rather than contention-dependent. This is a strengthening. |
| Adding a gating scan pushes the gating suite back over its timeout budget | M | L | Phase 6 measures the real post-change wall clock before fixing timeout values, and sets each budget at ~2x the measured time. |
| Artifact/marker files get committed as noise or collide between concurrent runs | L | M | Output goes to a per-run subdirectory under `oracle/scan-results/`, ignored via a new `oracle/.gitignore` (inside file scope; the repo-root `.gitignore` is not touched). |
| Writing the marker before the JSON artifact is durable would reintroduce false completion | H | L | The core writes `report.json` first, flushes and closes it, then writes the marker via write-temp-and-rename. Phase 1 verification asserts the ordering by checking the marker's mtime is not earlier than the report's and that the report parses whenever the marker exists. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 3, 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. Phases 2 and 3 both touch
`test_cross_oracle_differential.py`; if executed in parallel they must observe the territory split
noted in each phase (Phase 2 adds a new module and a new script and does not edit the test module;
Phase 3 edits only the `TestFullScanReport` class body and `run-oracle-suite.sh`).

---

### Phase 1: Instrument the shared scan core [COMPLETED]

**Goal**: Per-formula progress, a bounded heartbeat, wall-clock measurement, a JSON result
artifact, and a completion marker — all inside the one function both entry points call, with
default behaviour byte-for-byte unchanged for existing callers.

**Tasks**:

- [x] Write the tests first (TDD, per CLAUDE.md): add a `TestScanInstrumentation` class in
      `test_cross_oracle_differential.py` exercising the new behaviour against the existing
      Z3-free `_StubOracle` (the same technique `TestDifferentialReport` already uses), so these
      tests are fast and belong in the gating pass. Cover: JSONL written with one record per
      formula; JSONL is flushed incrementally (readable mid-run); heartbeat fires at the configured
      interval and on the first and last formula; `report.json` contains the new fields; the marker
      exists only after a parseable `report.json` exists; default-`None` parameters produce no files
      at all.
- [x] Add three optional, default-`None`/`0` parameters to `_generate_differential_report()`:
      `progress_path: Path | None`, `heartbeat_every: int = 0`, `artifact_dir: Path | None`.
      When all are unset, behaviour is exactly as today.
- [x] In the formula loop, when `progress_path` is set, append one JSON record per formula and
      `flush()` after every line. Record shape follows the proven
      `evidence/scan_instrumented.py` schema: `idx`, `complexity`, `ref_result`, `ref_elapsed_s`,
      `mc_result`, `mc_elapsed_s`, `verdict`, running `cum_disagreements`/`cum_timeouts`,
      `elapsed_s`, and `formula_json`.
- [x] Emit a flushed stdout line for every formula that disagrees, times out, or exceeds a 5s
      solve, plus a heartbeat every `heartbeat_every` formulas and unconditionally on the first and
      final formula — so a healthy run is never silent for more than `heartbeat_every` formulas'
      worth of wall clock.
- [x] Add `started_at`, `completed_at`, and `wall_clock_seconds` to the returned report dict
      (the only fields Problem 3 asks for that the dict lacks today). Do not rename or remove any
      existing field.
- [x] When `artifact_dir` is set, after the loop: write `report.json` via the existing
      `_write_report_json()`, close it, then write the completion marker `SCAN_COMPLETE` **last**,
      via write-to-temp-then-`os.replace` so it is atomic. Marker content is JSON:
      `{status, total_formulas, conclusive, disagreements, timeout_count, wall_clock_seconds,
      report_path}`.
- [x] Add a module-level docstring paragraph on the marker contract: the marker's existence is the
      *only* sanctioned completion signal; PID liveness is never a verdict.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — new optional params and
  instrumentation inside `_generate_differential_report()` (line ~1374); new wall-clock fields in
  the returned dict; new marker/artifact writer helper; new `TestScanInstrumentation` class.

**Verification**:

- [x] `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -k "ScanInstrumentation or DifferentialReport" -v` passes.
      (22 passed, 46 deselected.)
- [x] The full gating suite still passes with no behavioural change to existing tests:
      `nix develop --command bash oracle/run-oracle-suite.sh -m "not slow"` (temporary manual
      deselect; Phase 3 makes it the default). (Confirmed green; see Phase 3 for the recorded run.)
- [x] A stub-oracle run with `artifact_dir` set produces a `report.json` that parses and a
      `SCAN_COMPLETE` marker whose mtime is >= the report's.
      (`test_artifact_dir_writes_report_and_marker` asserts this directly.)
- [x] Grep confirms `_assert_scan_report`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, and
      `MIN_CONCLUSIVE_SCAN_FORMULAS` are unchanged: `git diff` shows no edits to those three.
      (Confirmed: `git diff` shows zero hunks touching those three names.)

---

### Phase 2: Standalone scan runner and exhaustive runner script [COMPLETED]

**Goal**: An explicitly-invoked exhaustive entry point that streams progress, lands artifacts, is
bounded by a timeout, and detects its own completion from the marker.

**Tasks**:

- [x] Create `oracle/scan_runner.py`: a thin CLI that imports `_enumerate_primitive_formulas`,
      `_reference_verdict`, `_generate_differential_report`, `_assert_scan_report`,
      `SELF_SCAN_SOLVE_TIMEOUT_MS`, and `MIN_CONCLUSIVE_SCAN_FORMULAS` from the test module (the
      import path `evidence/scan_instrumented.py` already proved works) and calls the shared core.
      Flags: `--timeout-ms` (default `SELF_SCAN_SOLVE_TIMEOUT_MS`), `--max-complexity` (default 5),
      `--limit` (default none), `--out-dir` (default a timestamped dir under `oracle/scan-results/`),
      `--heartbeat-every` (default 10), `--min-conclusive` (default
      `MIN_CONCLUSIVE_SCAN_FORMULAS`). It MUST contain no solve loop of its own.
- [x] Exit code contract: `0` on a clean scan meeting both assertion teeth; `1` on a disagreement
      or floor miss; `2` on an operational error. Print the `# DONE ...` summary line last.
- [x] Create `oracle/run-oracle-exhaustive-scan.sh`: wraps `pytest "$repo_root/oracle" -m slow -s`
      (serial, no `-n`, so streaming output is not captured by xdist and solve times are not
      contention-inflated) in `timeout --kill-after=60s "${ORACLE_EXHAUSTIVE_TIMEOUT:-7200}"`.
      Distinguish exit 124 (timeout fired) and 137 (SIGKILL after `--kill-after`) from a genuine
      test failure in the summary, matching the "fails loudly" requirement.
- [x] The exhaustive script reports completion by checking for the `SCAN_COMPLETE` marker under the
      run's output directory, and states explicitly in its summary when the marker is absent
      ("scan did not reach completion") — never inferring completion from the process having exited.
- [x] Add a header comment to the new script mirroring `run-oracle-suite.sh`'s style: why this is
      separate, what it costs (~60-90 min), and that it is never part of the gating path.
- [x] Create `oracle/.gitignore` ignoring `scan-results/` (repo-root `.gitignore` is outside file
      scope and is not touched).
- [x] Point the exhaustive script's output dir at a per-run timestamped subdirectory so concurrent
      or repeated runs cannot collide.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:

- `oracle/scan_runner.py` (new)
- `oracle/run-oracle-exhaustive-scan.sh` (new, executable)
- `oracle/.gitignore` (new)

**Verification**:

- [x] `python oracle/scan_runner.py --max-complexity 3 --limit 5 --out-dir /tmp/scan-smoke` completes
      in seconds, streams heartbeat lines, and writes `progress.jsonl`, `report.json`, and
      `SCAN_COMPLETE`. (Ran in ~25s — one formula hit the 10s timeout budget on both solves; all
      three artifacts confirmed written and parseable.)
- [x] `grep -c "find_countermodel" oracle/scan_runner.py` returns 0 — the CLI delegates, it does not
      re-implement the loop.
- [x] `ORACLE_EXHAUSTIVE_TIMEOUT=5 bash oracle/run-oracle-exhaustive-scan.sh` exits reporting a
      timeout (exit 124/137 path), not a test failure, and reports the marker as absent.
      (Confirmed: "pytest: TIMED OUT (exit 124, budget 5s)" / "completion marker: ABSENT".)
- [x] `bash -n` clean on the new script; `chmod +x` applied.

---

### Phase 3: Deselect `slow` from the gating runner and add per-pass timeouts [COMPLETED]

**Goal**: The gating runner stops running the exhaustive sweep and can no longer hang indefinitely.

**Tasks**:

- [x] `run-oracle-suite.sh` pass 1: `-m "not xdist_serial and not slow"`. Pass 2:
      `-m "xdist_serial and not slow"`. The two passes still partition the non-slow suite exactly;
      confirm by comparing collected counts (see Verification).
- [x] Wrap both passes in `timeout --kill-after=60s`, budgets from env vars with defaults
      (`ORACLE_PASS1_TIMEOUT`, `ORACLE_PASS2_TIMEOUT`) — provisional values here, calibrated against
      real measurement in Phase 6.
- [x] Capture exit 124/137 per pass and report `TIMED OUT (exit N)` distinctly from
      `FAILED (exit N)` in the existing summary block, so a stall is never mistaken for a test
      failure or for success.
- [x] Move `test_report_writes_to_file` out of the `TestFullScanReport` class into a new
      non-`slow` class (it runs a cheap complexity-3 scan and is `slow` only by class co-location,
      per research Finding 1). This *adds* coverage to the gating pass at no cost — no test leaves
      the suite. (Relocated to `TestComplexity3ScanReportWriting`; also wired
      `test_complexity_5_scan_self_consistent` to the `ORACLE_SCAN_OUT_DIR` env var so
      `run-oracle-exhaustive-scan.sh` gets artifacts by driving pytest directly, per Decision D2 —
      within this phase's declared "TestFullScanReport class body" territory.)
- [x] Update `run-oracle-suite.sh`'s header comment to describe the gating/exhaustive split and
      point at the new exhaustive script (fuller documentation lands in Phase 7).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:

- `oracle/run-oracle-suite.sh` — marker expressions, `timeout` wrappers, exit-code classification,
  header comment.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — relocate
  `test_report_writes_to_file` out of the `slow`-marked class. (Territory note: this phase edits
  only the `TestFullScanReport` class body.)

**Verification**:

- [x] Collection partition is exact and nothing is silently dropped:
      `pytest oracle --collect-only -q -m "not slow"` count equals
      `-m "not xdist_serial and not slow"` count plus `-m "xdist_serial and not slow"` count.
      (Measured: 566 = 559 + 7.)
- [x] `pytest oracle --collect-only -q -m "slow"` collects exactly the two remaining slow items
      (`test_complexity_5_scan_self_consistent`, `test_temporal_only_agreement_complexity_5`) —
      confirming `test_report_writes_to_file` moved into the gating pass. (Confirmed via
      `--collect-only`; `TestComplexity3ScanReportWriting::test_report_writes_to_file` appears in
      the `not slow` collection.)
- [x] `ORACLE_PASS1_TIMEOUT=5 nix develop --command bash oracle/run-oracle-suite.sh` reports
      `TIMED OUT`, not `FAILED`, and exits non-zero. Confirmed from the terminal summary line:
      "pass 1 (parallel, -n 6, not xdist_serial and not slow, budget 5s): TIMED OUT (exit 124)";
      pass 2 ran independently and PASSED (not `set -e`, as designed).
- [x] Full gating run `nix develop --command bash oracle/run-oracle-suite.sh` completes green and
      its wall clock is recorded for Phase 6 (expected ~20 min, down from ~76). Measured: pass 1
      (parallel, -n 6) 649.09s (10:49), pass 2 (serial, xdist_serial) 318.57s (5:18); total wall
      clock ~16.1 min, both passes PASSED. Down from the ~76.7-minute baseline.

---

### Phase 4: Re-derive and persist the known-conclusive baseline [COMPLETED]

**Goal**: Establish the ground-truth conclusive/inconclusive population from a fresh, observable,
serial exhaustive run — because the 106/274-at-10000ms measurement was never persisted and the
surviving pre-fix 5000ms JSONL is unusable as ground truth (it predates the timeout-conflation fix).

**Tasks**:

- [x] Pre-flight per TESTING_GUIDE 8.6: confirm no competing pytest processes
      (`ps aux | grep pytest`) and that the machine is otherwise idle. Record what was checked.
      (Confirmed clean immediately before launch: `ps aux | grep pytest` returned no matches.)
- [x] Run the exhaustive scan serially at the deployed budget, detached, with progress streaming to
      a log: `python oracle/scan_runner.py --timeout-ms 10000 --out-dir
      specs/138_make_oracle_suite_fast_and_observable/baselines/derivation-run/`. Expected ~60-90
      minutes wall clock. Poll for the `SCAN_COMPLETE` marker — **never** for PID liveness.
      (Actual wall clock 3640.955s = 60.7 min. Completion established from `SCAN_COMPLETE`'s
      presence, polled via log content/mtime, never via PID liveness.)
- [x] From the run's `progress.jsonl`, derive the known-conclusive set: every formula where neither
      solve returned `TIMEOUT`.
- [x] Write the manifest `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` with:
      schema version; `max_complexity`; `atoms`; `total_formulas` (expected 274);
      `solve_timeout_ms` (10000); `derived_at`; `wall_clock_seconds`; `conclusive_count`;
      `disagreements` (expected 0); and `conclusive` as a list of `{index, formula_json}` pairs
      (Decision D3 — index *and* canonical JSON, never index alone). Index is 0-based (matches
      direct Python list indexing `all_formulas[index]`), converted from progress.jsonl's
      1-based `idx`.
- [x] Copy the raw `progress.jsonl` and `report.json` into
      `specs/138_make_oracle_suite_fast_and_observable/baselines/` as durable evidence, so the next
      person does not face the same "the measurement was never persisted" problem. (Written
      directly to `baselines/derivation-run/` by `--out-dir`, so already durable evidence under
      `baselines/`; no separate copy needed.)
- [x] Record in the manifest and in the task evidence: the measured conclusive count, and how it
      compares to the documented 106/274. (103/274, recorded in the manifest's `notes` field: within
      ordinary run-to-run variance of 106 and above the ~95 stop-and-re-run tolerance floor.)

**Timing**: 1 hour agent work; ~1.5-2 hours unattended wall clock for the run itself

**Depends on**: 2

**Files to modify**:

- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` (new)
- `specs/138_make_oracle_suite_fast_and_observable/baselines/` (new; raw JSONL + report evidence)

**Verification**:

- [x] The `SCAN_COMPLETE` marker exists and its `report.json` parses — completion established from
      the marker, with the polling method recorded. (Marker present, `report.json` parsed
      successfully with `total_formulas=274`.)
- [x] `total_formulas == 274` and `disagreements == 0`. A non-zero disagreement count is a
      **stop-and-report** condition (it would be a genuine soundness finding, not a baseline to
      record). (Both confirmed: `total_formulas=274`, `disagreements=0` — no stop-and-report
      needed.)
- [x] `conclusive_count` is within a stated tolerance of the documented 106 (treat a drop below ~95
      as evidence of a contended or degraded run: re-run rather than baking it in). Record the
      actual number and the tolerance judgement in the summary. (Measured 103/274 — 3 below the
      documented 106, comfortably above the ~95 re-run floor; judged ordinary run-to-run variance,
      not a degraded run. Baseline recorded as-is.)
- [x] The manifest round-trips: a script re-enumerates complexity<=5 and confirms every manifest
      entry's `formula_json` equals the enumerated formula at that `index`. (Confirmed: 274
      enumerated == manifest total_formulas; all 103 conclusive entries matched, 0 mismatches.)

---

### Phase 5: Gating conclusive-population assertion [NOT STARTED]

**Goal**: A gating test that asserts the soundness tooth over the known-conclusive population and
that the inconclusive set has not grown — without re-solving the ~168 known-timeout formulas.

**Tasks**:

- [ ] Write the test first: `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
      in `test_cross_oracle_differential.py`, marked `@pytest.mark.xdist_serial` (so it runs in the
      contention-free serial pass — see the Risks table; this makes the floor deterministic rather
      than contention-dependent, a strengthening, not a relaxation). Not marked `slow`.
- [ ] Structural drift guard, before any solving (cheap, no Z3): re-enumerate complexity<=5; assert
      `len(all_formulas) == manifest["total_formulas"]`; assert every manifest entry's
      `formula_json` matches the enumerated formula at its `index`. On mismatch, fail with an
      explicit "the enumerator changed — re-derive the baseline via
      oracle/run-oracle-exhaustive-scan.sh" message. This is the "inconclusive set has not grown"
      structural invariant: population size fixed, known-conclusive membership fixed, therefore the
      inconclusive complement cannot have grown without one of these assertions firing.
- [ ] Solve only the manifest's conclusive subset at `SELF_SCAN_SOLVE_TIMEOUT_MS` via
      `_generate_differential_report()`, then pass the report to `_assert_scan_report()`
      **unchanged**.
- [ ] Introduce `MIN_CONCLUSIVE_GATING_FORMULAS` as a **separate** constant — do not touch
      `MIN_CONCLUSIVE_SCAN_FORMULAS`, which the exhaustive variant keeps using. Set it tight,
      just below the manifest's `conclusive_count`, with only enough slack for ordinary run-to-run
      variance (the gating subset is conclusive by construction, so this floor should be near
      100% of the subset — materially stricter proportionally than the exhaustive 90/274).
      Document the derivation in a code comment in the same style as the existing constants,
      including the explicit instruction never to lower it to make a run green.
- [ ] Add a docstring stating the division of labour: this test detects soundness regressions in the
      decidable population every run; the exhaustive variant is the sole re-deriver of the full
      population and the sole detector of drift in the inconclusive set.

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — new `TestGatingConclusiveScan`
  class, manifest loader, `MIN_CONCLUSIVE_GATING_FORMULAS` constant.

**Verification**:

- [ ] The gating test passes serially and its wall clock is ~2 minutes (measured planning basis: the
      conclusive subset totalled 101s of solve time in the surviving 274-formula run). Record the
      actual time.
- [ ] Negative control — the drift guard actually fires: temporarily corrupt one manifest entry's
      `formula_json` in a scratch copy and confirm the test fails with the "re-derive the baseline"
      message rather than passing or erroring obscurely. Revert.
- [ ] Negative control — the soundness tooth is still live: run the test against a stub oracle
      injected to disagree on one formula and confirm `_assert_scan_report` fails it. This proves
      speed did not come from a dead assertion.
- [ ] `git diff` confirms `_assert_scan_report`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, and
      `MIN_CONCLUSIVE_SCAN_FORMULAS` remain unmodified.

---

### Phase 6: Integrate, measure, and calibrate timeouts [NOT STARTED]

**Goal**: The assembled gating suite runs green end to end, with timeout budgets set from real
measurement and verified worker cleanup.

**Tasks**:

- [ ] Run the full gating suite and record its true wall clock per pass:
      `nix develop --command bash oracle/run-oracle-suite.sh`.
- [ ] Set `ORACLE_PASS1_TIMEOUT` / `ORACLE_PASS2_TIMEOUT` defaults to ~2x the measured per-pass wall
      clock, and document the measured basis in the script's header comment so a future reader can
      tell a deliberate budget from a guess.
- [ ] Verify xdist worker cleanup on a fired timeout (the research's explicit open risk): trigger a
      timeout with a tiny `ORACLE_PASS1_TIMEOUT`, then confirm via `ps aux | grep pytest` that no
      orphaned workers survive. If SIGTERM does not propagate, confirm `--kill-after` reaps them and
      record the observed behaviour.
- [ ] Confirm the end-to-end speedup against the ~76.7-minute baseline and record the actual
      before/after numbers.
- [ ] Confirm the exhaustive path still works end to end and still asserts the *unchanged*
      `MIN_CONCLUSIVE_SCAN_FORMULAS = 90` floor over the full 274 population.

**Timing**: 1.5 hours agent work (plus exhaustive-path wall clock if re-run in full; a
`--limit`-bounded run is acceptable for the smoke check since Phase 4 already exercised the full
sweep)

**Depends on**: 3, 5

**Files to modify**:

- `oracle/run-oracle-suite.sh` — calibrated timeout defaults and measured-basis comment.

**Verification**:

- [ ] Full gating suite green, wall clock recorded, and materially below the ~76.7-minute baseline
      (target ~20 min).
- [ ] `ps aux | grep pytest` shows no orphans after a deliberately-triggered timeout.
- [ ] `pytest oracle --collect-only -q` total still accounts for every test: gating count + slow
      count equals the pre-change total of 559 plus the tests added in Phases 1 and 5. No test was
      lost.
- [ ] Both assertion teeth demonstrated live in the gating path (carried forward from Phase 5's
      negative controls).

---

### Phase 7: Document the split [NOT STARTED]

**Goal**: The gating/exhaustive split, the baseline strategy, the marker contract, and the timeouts
are documented in all three places that describe how to run this suite, so they cannot drift.

**Tasks**:

- [ ] Add TESTING_GUIDE.md section **8.8 "Oracle Suite: Gating vs. Exhaustive Split"** immediately
      after 8.7 (the file currently contains zero mentions of "oracle" despite 8.6 being cited by
      both `conftest.py` and `run-oracle-suite.sh`). Cover: the `not slow` gating default and why
      `oracle/` needs it explicitly (no reachable ini file); the separate exhaustive runner and its
      cost; the known-conclusive-population strategy and the rule that a population change requires
      regenerating the manifest; the JSON-artifact and completion-marker contract, stating plainly
      that a vanished PID is not a verdict; and the per-pass timeout with its exit-124 semantics.
- [ ] State the hard constraint in the guide: the two assertion teeth are non-negotiable, and speed
      is only ever bought by running less redundant work.
- [ ] Update the Table of Contents if 8.x subsections are listed there.
- [ ] Update `oracle/bimodal_logic/README.md`'s "Running the Test Suite" section: the two-pass
      gating invocation now excludes `slow`, plus the new exhaustive script, plus how to observe a
      long run (tail the JSONL, watch the heartbeat) and how to detect completion (the marker).
- [ ] Confirm `run-oracle-suite.sh`'s header comment (updated in Phases 3 and 6) is consistent with
      both documents — this is the specific drift class research Finding 6 flagged.
- [ ] Per `.claude/rules/no-task-references-in-deliverables.md`: cite durable anchors (file names,
      section headings) in all three deliverables — no task numbers anywhere outside `specs/**`.

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:

- `code/docs/core/TESTING_GUIDE.md` — new section 8.8, ToC entry.
- `oracle/bimodal_logic/README.md` — "Running the Test Suite" section.
- `oracle/run-oracle-suite.sh` — header comment consistency pass.

**Verification**:

- [ ] `grep -i oracle code/docs/core/TESTING_GUIDE.md` now returns the new section (it returned
      nothing before).
- [ ] `grep -rn "task [0-9]" code/docs/core/TESTING_GUIDE.md oracle/` returns no task-number
      citations in the files this task authored.
- [ ] All three descriptions of the suite (guide 8.8, oracle README, script header) name the same
      two runners, the same marker path, and the same timeout env vars — checked by reading them
      side by side.
- [ ] Every command shown in the docs is one actually run during this task, not an untested
      invocation.

---

## Testing & Validation

- [ ] `nix develop --command bash oracle/run-oracle-suite.sh` completes green in ~20 minutes
      (baseline: ~76.7 minutes).
- [ ] The gating pass no longer collects `TestFullScanReport::test_complexity_5_scan_self_consistent`.
- [ ] The exhaustive runner streams per-formula progress; a healthy run is never silent longer than
      the heartbeat interval.
- [ ] Every scan run emits `report.json` with total / conclusive / disagreements / inconclusive /
      wall clock, plus a `SCAN_COMPLETE` marker written strictly after the report.
- [ ] Completion is established from the marker in every runner; no runner polls PID liveness.
- [ ] A deliberately-triggered timeout reports `TIMED OUT` distinctly from `FAILED`, exits non-zero,
      and leaves no orphaned xdist workers.
- [ ] `_assert_scan_report`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, and `MIN_CONCLUSIVE_SCAN_FORMULAS` are
      unmodified in the final diff.
- [ ] Negative controls prove both teeth are live in the gating path: an injected disagreement fails
      the run, and a corrupted baseline entry fails the drift guard.
- [ ] Total collected test count is not lower than before (559 plus additions); no test was skipped
      or deleted to gain speed.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` shows no collateral regressions outside `oracle/`.

## Artifacts & Outputs

- `oracle/scan_runner.py` — standalone instrumented scan CLI (thin entry point over the shared core)
- `oracle/run-oracle-exhaustive-scan.sh` — explicitly-invoked exhaustive sweep runner
- `oracle/run-oracle-suite.sh` — gating runner: `slow` deselected, bounded timeouts, loud failures
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — instrumented shared scan core,
  `TestScanInstrumentation`, `TestGatingConclusiveScan`, relocated `test_report_writes_to_file`
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` — persisted baseline manifest
- `oracle/.gitignore` — ignores `scan-results/`
- `oracle/bimodal_logic/README.md` — updated "Running the Test Suite"
- `code/docs/core/TESTING_GUIDE.md` — new section 8.8
- `specs/138_make_oracle_suite_fast_and_observable/baselines/` — raw derivation-run JSONL and report
  (durable evidence, so the "measurement was never persisted" failure does not recur)
- `specs/138_make_oracle_suite_fast_and_observable/summaries/01_oracle-suite-fast-observable-summary.md`

## Rollback/Contingency

- Each phase is committed separately per `.claude/rules/git-workflow.md`, so any single phase can be
  reverted without disturbing the others. The two new scripts and the new data file are additive:
  deleting them plus reverting `run-oracle-suite.sh` restores the current behaviour exactly.
- The Phase 1 instrumentation is default-off (all new parameters default to `None`/`0`), so even if
  it is left in place it cannot change existing callers' behaviour.
- If Phase 4's derivation run reveals a non-zero disagreement count, stop: that is a genuine
  soundness finding, not a baseline. Report it, leave Phases 5-7 unstarted, and let the gating suite
  keep running with `slow` deselected (Phase 3's win is independent and already banked) while the
  finding is triaged separately.
- If the Phase 4 conclusive count lands materially below the documented ~106, do not record it —
  re-run on an idle machine first. A contended baseline would permanently shrink gating coverage,
  which is precisely the assertion-weakening this task's hard constraint forbids.
- If the gating conclusive scan proves flakier than expected in practice, the correct response is to
  investigate the variance (or run it serially, as already planned), never to lower
  `MIN_CONCLUSIVE_GATING_FORMULAS`.
