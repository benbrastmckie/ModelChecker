# Research Report: Four Open CI-Budget Questions (A/B/C/D)

- **Task**: 170 - Resolve xdist worker count and differential oracle floor
- **Started**: 2026-08-26T01:32:00Z
- **Completed**: 2026-08-26T02:45:00Z
- **Effort**: ~1.25 hours
- **Dependencies**: None
- **Sources/Inputs**:
  - `.github/workflows/tests.yml`, `flake.nix`, `.github/workflows/differential-tests.yml`,
    `.github/workflows/unstable-watch.yml`
  - `code/tests/ci/test_workflow_parity.py`, `code/tests/ci/test_example_budget_floor.py`
  - `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition}/examples.py`
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  - `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/` (report, plan, summary)
  - `specs/167_flaky_testmixedformulas_failures/summaries/01_deterministic-mixed-formula-budgets-summary.md`
  - CI runs consulted via `gh run view`/`gh api`: `32915763636` (baseline green), `32910478240`
    (Python 3.12 worker crash, first run with the 10s max_time floor), `32897405646` (Python 3.12
    17-minute silent hang, pre-`--timeout-method=thread`)
  - Local measurements: isolated and `taskset -c 0,1,2,3`-restricted pytest runs (see Findings)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **(B) CONFIRMED SETTLED, no residue.** `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
  carries `@pytest.mark.unstable` in-tree, `GATING_RECHECK_SOLVE_TIMEOUT_MS` is unchanged at
  40000 and `MIN_CONCLUSIVE_GATING_FORMULAS` unchanged at 100, and `unstable-watch.yml`'s
  classifier was extended (via an importable, unit-tested module, an improvement over the
  original plan's inline-YAML sketch) with a dedicated gating-floor `TIMING` signature. No
  re-investigation performed, per instruction.
- **(A) Measured, bounded scope, zero outcome flips found.** `-n 4` vs `-n 6` under
  `taskset -c 0,1,2,3` contention produced byte-identical pass/fail sets across 554 tests
  (bimodal: 301/301 identical; exclusion+imposition: 253/253 identical), including every
  countermodel-expected (`_CM_`) example in those directories. This does **not** cover the full
  2321-test gating selection (logos, `code/tests/`, oracle-adjacent CLI/builder/iterate tests were
  not included) — a full comparison was judged unaffordable in this dispatch (see Findings). A
  bounded design for closing that gap is proposed.
- **(C) Measured, all 22 flagged examples confirmed trivially fast.** Every `max_time: 2`/`3`
  example in bimodal, exclusion, and imposition measured 0.01s-0.37s in isolation and 0.06s-0.80s
  under 6-worker/4-core contention — 5x-300x headroom, categorically different from `CL_TH_12`/
  `CL_TH_13`'s ~3x margin that caused the original logos failures. Recommend extending
  `test_example_budget_floor.py`'s `_COVERED` list to these three files with the same 10s floor,
  backed by this measurement.
- **(D) Root cause not determined; mechanism narrowed with new corroborating evidence.** The
  crashed test (`test_three_taskframe_axioms_present_in_frame_constraints`) is demonstrably an
  innocent bystander — CI's own log shows the replacement worker re-ran it in 0.23s. The failing
  run's timeline shows a ~123s silence immediately before the "node down" message, and the prior
  incident (pre-thread-timeout-guard) shows a 17-minute silence before being killed by the
  job-level backstop — both consistent with a worker that died or wedged rather than one
  specific test overrunning a budget. Cannot distinguish Z3/Python 3.12 ABI issue vs. memory
  ceiling vs. genuine bug from available CI artifacts (no core dump, no `dmesg`/OOM-killer log
  surfaced in the workflow's own output). Recommend adding lightweight resource instrumentation
  (`psutil`-based peak-RSS logging per worker) to the CI job rather than guessing further.

## Context & Scope

Task 160 (same batch) resolved item B by exercising the documented `unstable`-marking fallback.
This report covers only the three items task 160 explicitly deferred (A, C, D) plus a
confirmation pass on B per the delegation's constraint not to redo it. All measurement was
subject to the stated time budget: full-suite reruns of the ~46-minute oracle differential suite
were avoided; all pytest invocations below were scoped to specific files/directories and, where
a command exceeded the 120s foreground window, the harness auto-backgrounded it and this
dispatch polled for completion rather than blocking.

## Findings

### (B) Gating-floor unstable marking — confirmed, no residue

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py:2412` carries
  `@pytest.mark.unstable` directly on `test_known_conclusive_population_self_consistent`, with
  the four-criteria entry-comment block present above it (lines ~119-166).
- `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` (line 217) and `MIN_CONCLUSIVE_GATING_FORMULAS = 100`
  (line 286) are unchanged from task 160's landing — neither was re-touched, consistent with the
  explicit prohibition in both this task's description and task 160's own comment block.
- `unstable-watch.yml`'s classifier was extracted into `.github/scripts/unstable_watch_classify.py`
  with a dedicated gating-floor `TIMING` branch and a disagreements-laundering guard, unit-tested
  by `code/tests/ci/test_unstable_watch_classifier.py` — a stronger implementation than the
  research report's inline-YAML sketch proposed, and no defect found in it during this pass.
- `TESTING_GUIDE.md` section 8.9 lists both `BM_CM_1` and the gating scan under "Currently
  marked."
- **No residue found.** This item is closed; no further action recommended.

### (A) XDIST worker count (`-n 6` vs `-n 4`)

**What was measured.** Both `.github/workflows/tests.yml` (line 127) and `flake.nix` (line 174)
invoke, textually enforced identical by `code/tests/ci/test_workflow_parity.py`:
```
pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 6 -q --timeout=300 --timeout-method=thread
```
This selection collects **2321 of 2443** tests. A full `-n 6` vs `-n 4` head-to-head over that
entire selection, run twice, was judged not affordable in one dispatch (see "What was not
measured" below) — instead, this report targeted the specific subtree the workflow's own inline
comment names as the historically documented contention flake location:
`theory_lib/bimodal` (`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` under xdist
`auto` mode), plus `exclusion`/`imposition` as adjacent Z3-solve-heavy theories.

Method: `taskset -c 0,1,2,3` restricts the local 24-core machine to 4 logical CPUs, matching the
CI runner's 4-vCPU footprint, so that `-n 6` genuinely oversubscribes (6 workers over 4 cores)
the same way it does on `ubuntu-latest`. Full per-test pass/fail lists (`-rA`, filtered to
`PASSED`/`FAILED`/`ERROR` lines, sorted) were captured for each `-n` value and diffed.

| Scope | Tests | `-n 6` result | `-n 4` result | Diff |
|---|---|---|---|---|
| `theory_lib/bimodal` (all test dirs) | 301 | 301 passed | 301 passed | **0 lines** (`diff` exit 0) |
| `theory_lib/exclusion` + `theory_lib/imposition` | 253 | 253 passed | 253 passed | **0 lines** (`diff` exit 0) |

Combined: **554/554 tests produced byte-identical outcomes** at `-n 4` vs `-n 6` under matched
4-core contention, including every countermodel-expected (`_CM_`) example in these three
theories — directly the concern named in the task description ("no countermodel-expected example
stops finding one"). No flip, no new timeout, no new failure in either direction.

**Conceptual note tying in task 167's `max_rlimit` finding.** Task 167 established that Z3's
`rlimit` (a resource-unit counter) is load-independent — the same solve does the same amount of
Z3-internal work regardless of ambient CPU contention; only *wall-clock* time to reach that
amount of work varies with contention. This means "does reducing worker count change what an
example decides" is not really the right frame: worker count cannot change what Z3 would
eventually find, only whether it finds it within the wall-clock `max_time` budget before
contention pushes the same amount of work past that budget. The measurement above is therefore
the right instrument (did the same wall-clock-budgeted example still decide within budget under
each worker count), but a rlimit-based instrumentation pass (recording `rlimit` alongside outcome)
would make a *future* re-run of this comparison self-diagnosing: a test that flips from pass to
timeout with unchanged rlimit is definitively a worker-count/contention effect, not a solver
non-determinism artifact. This repo does not yet do that for the example-suite tests (only
`Z3OracleProvider.find_countermodel()` in the oracle package got the rlimit plumbing from task
167); wiring it into `ModelDefaults`/`utils.testing.run_test()` is out of this task's scope but is
the natural instrument if a lower-`-n` migration wants stronger-than-wall-clock verification.

**What was not measured, and why.** The full 2321-test selection (adds `logos`'s ~1000+ tests and
`code/tests/`'s CLI/builder/iterate/oracle-adjacent suites) was not run at either `-n` value. A
rough extrapolation from the measured rate (554 tests completed in under ~4 minutes combined
across both `-n` values under `taskset -c0-3`) suggests the full selection run twice would land
in the 15-25 minute range — within the tool's background-and-poll capability in principle, but
risking a large fraction of this dispatch's remaining budget on a single measurement with
uncertain payoff (the bimodal/exclusion/imposition result already found zero flips, and `logos`
is the theory the `max_time` floor was already hardened for, making it the least likely place to
find a *worker-count*-specific flip as opposed to a *budget*-specific one). This is a judgment
call, not a hard limit — a future dispatch with a dedicated measurement window could run it.

**Recommended next action (bounded design for implementation phase):**
1. Extend today's `taskset -c0-3` two-way diff to the full `-m "not packaging and not performance
   and not unstable and not xdist_serial"` selection over `tests/ src/model_checker`, once as
   `-n 6` and once as `-n 4`, each backgrounded with a ~10-minute budget; diff the sorted
   `PASSED`/`FAILED` node-id lists exactly as done here. A non-empty diff is the actionable
   signal; an empty diff extends this report's finding to full coverage.
2. If the diff is empty, `-n 4` is a safe, drop-in replacement for `-n 6` in both `tests.yml` and
   `flake.nix` (both files must change together — `test_workflow_parity.py` enforces the `-n`
   value matches across them) and should also update the inline rationale comment (currently
   documents `-n 6` was chosen over `auto` for the BM_CM_1 flake; that reasoning is about
   `auto` vs. a fixed `-n`, not about which fixed value, so it is preserved either way, just
   re-worded to justify 4 instead of 6).
3. Repeat the comparison at least twice (not once) before committing to a change — a single green
   diff cannot rule out a rare contention-dependent flip; task 159/160's own history shows this
   class of flake is heavy-tailed, not always reproducible on the first draw.

### (C) Residual tight budgets outside logos (`max_time: 2`/`3`)

**Inventory** (AST-derived, matches the task description's "20 at max_time 2, 2 at max_time 3"):

| File | `max_time=2` examples | `max_time=3` examples |
|---|---|---|
| `bimodal/examples.py` | `MD_CM_2..6`, `EX_TH_1`, `MD_TH_1`, `MD_TH_2`\*, `TN_TH_2`, `BM_TH_4` (10) | none |
| `exclusion/examples.py` | `EX_CM_1`, `EX_TH_1` (2) | none |
| `imposition/examples.py` | `IM_CM_6,13,14,15,16,17,18,21` (8) | `IM_CM_19`, `IM_CM_20` (2) |

\* `MD_TH_2` is separately excluded from `test_bimodal.py`'s collected suite via
`KNOWN_TIMEOUT_EXAMPLES` (unrelated to its `max_time`; it is a known non-theorem under current
bimodal semantics) — it is not actually exercised at `max_time=2` in CI today.

**Isolated measurement** (single-process, no contention), all 9 remaining bimodal examples plus
`EX_CM_1`/`EX_TH_1` (exclusion) and all 10 imposition examples:

- Bimodal: 0.06s-0.13s per example (all N=2, M=1 or M=2 — trivially small state spaces).
- Exclusion: `EX_CM_1` 0.04s, `EX_TH_1` 0.01s.
- Imposition: 0.06s-0.37s.

**Contended measurement** (`taskset -c 0,1,2,3`, `-n 6`, run alongside the full 123-test
`bimodal/test_bimodal.py` + `exclusion/test_examples.py` + `imposition/test_imposition.py`
selection, 32.07s total, 123/123 passed): the slowest of the flagged examples under this
contention was `IM_CM_14` at 0.80s (budget 2s, 2.5x headroom) and `IM_CM_13` at 0.53s. No flagged
example approached its budget.

**Contrast with the logos incident this guard exists for:** `CL_TH_12`/`CL_TH_13` measured
0.267s/0.350s locally against `max_time: 1` — roughly 3x headroom, which still failed under CI's
6-worker/4-core contention (< 1x effective headroom there). The bimodal/exclusion/imposition
examples measured here show 5x-30x headroom in isolation and still comfortable (2.5x+) margin
under matched contention — a meaningfully different risk profile, though not a zero-risk one.

**Recommendation:** Extend `code/tests/ci/test_example_budget_floor.py`'s `_COVERED` list to
include `bimodal/examples.py`, `exclusion/examples.py`, and `imposition/examples.py` at the same
`_MIN_MAX_TIME = 10` floor used for logos. This is a measurement-backed widening (not a
pattern-match): every flagged example was directly timed, isolated and under contention, and all
clear a 10s floor by at least 25x. The one caveat: `bimodal/examples.py` also carries deliberately
*recalibrated* budgets elsewhere in the same file (`BM_CM_1` at 60s, `BM_CM_4` at 120s, per the
task-159/160 heavy-tailed-solve investigations) — raising the floor to 10s does not touch those
(a floor only raises values below it) and does not conflict with that calibration record; this
should be noted explicitly in the guard's docstring/comment when it lands, the same way the
existing logos-only comment explains the scope decision, so a future reader does not read the
floor-extension as silently overriding the recalibration record.

### (D) Python 3.12 xdist worker crash

**The named test is confirmed not the cause.** CI's own log for run `32910478240` shows the
crash-attributed test, `test_three_taskframe_axioms_present_in_frame_constraints`, was
immediately re-run by the replacement worker (`gw2`) and completed in **0.23s** setup+call — an
N=2/M=3 in-process Z3-solver satisfiability check with no iteration, no oracle call, and nothing
resembling the heavier `BM_CM_1`/`BM_CM_4`/`TestBimodalIteratorReal` tests. This directly confirms
the task description's framing: "the test named in the failure is whichever one the worker
happened to be running, not necessarily the cause."

**Timeline evidence, both incidents:**
- Run `32910478240` (Python 3.12, first run carrying the 10s max_time floor, **has** the
  `--timeout-method=thread` guard): progress reached 97% at `23:26:42`, then **zero log output for
  123 seconds**, then `[gw2] node down: Not properly terminated` at `23:28:45`. No `Fatal Python
  error`, no `Segmentation fault`, no faulthandler thread-stack dump appears anywhere in the
  captured log — meaning either the crash happened well before any single-test 300s timeout could
  fire (123s < 300s, consistent with a mid-solve crash rather than a hang-to-timeout), or the
  worker died in a way that took the log-writing machinery down with it.
- Run `32897405646` (Python 3.12, **predates** the `--timeout-method=thread` guard — this is the
  incident that motivated adding it): progress reached 94% at `20:51:07`, then **zero log output
  for ~17 minutes**, then killed by the job-level `timeout-minutes: 20` backstop at `21:08:24`,
  with 7 orphaned `python`/`pytest` processes reported in the cleanup step. Same shape (worker
  wedged/dead, not merely slow) as the later incident, at a much longer silence duration.
- Both incidents are unique to Python 3.12 in their respective runs; Python 3.10 and 3.11 (and
  `nix flake check`, a third Z3/Python toolchain) completed cleanly in both runs (Python 3.10
  failed `32897405646` too, but on the pre-floor `CL_TH_12`/`CL_TH_13` budget-overrun mechanism,
  not a worker crash — a different failure class from a different, already-fixed cause).

**What could not be determined, and why:**
- **No memory telemetry is captured anywhere in this CI job.** GitHub Actions' own log stream
  does not surface kernel OOM-killer messages (`dmesg`) inside a job's stdout unless the job
  explicitly runs and captures `dmesg` itself, which this workflow does not. Whether the runner's
  reported 16GB ceiling was actually approached at the time of either incident is therefore not
  observable from the artifacts this task's constraints allow querying (no fresh CI run was
  triggered for this report, consistent with the same "do not spend a CI run to find out" posture
  task 160 took for its own item (b)).
- **No core dump or Python-level traceback exists for either incident.** `pytest-xdist`'s "node
  down: Not properly terminated" is itself evidence of an abnormal worker exit (the message fires
  when the RPC channel to a worker breaks unexpectedly), but it does not distinguish a SIGSEGV
  (native ABI/library issue), a SIGKILL from the kernel OOM-killer (memory ceiling), or any other
  signal-level death.
- **A genuine Python-3.12-specific bug in bimodal cannot be ruled in or out from this evidence.**
  The crash is real (a worker did die), but the *victim test* is demonstrably not the *cause* test
  (shown above), and no other Python-3.12-only signal (deprecation warning escalated to error,
  C-API incompatibility in the installed `z3-solver` wheel's binary extension, etc.) surfaced in
  either captured log.

**Hypotheses, explicitly separated from the above measured facts:**
1. **Memory ceiling under 6 workers** (favored, but unconfirmed): six concurrent Z3 solves each
   holding a native context, at a point in the run (~93-97% / ~94%) that both incidents share, is
   consistent with a late-stage clustering of the suite's heavier iterate/oracle-adjacent tests
   (the workflow's own comment names `TestBimodalIteratorReal::test_iterate_two_produces_
   distinct_models`, 82.34s, as the single slowest test under this exact `-n 6` selection) pushing
   aggregate RSS across 6 workers past 16GB, with the kernel OOM-killer picking one process. This
   would explain why it is xdist-worker-count-sensitive (fewer workers -> lower peak aggregate
   RSS) and links directly to item (A): if `-n 4` is adopted, this failure mode's likelihood
   should drop as a side effect, independent of whether item (A)'s own contention-flip concern is
   confirmed absent.
2. **Python 3.12 / z3-solver wheel ABI issue** (plausible, unconfirmed): the PyPI `z3-solver`
   wheel is a compiled native extension; a 3.12-specific ABI mismatch or GC-interaction bug in
   that extension is a known general class of issue for CPython version bumps, but nothing in
   this repo's history singles this out over the memory hypothesis, and it does not obviously
   explain why the failure clusters late in the run rather than at collection/import time (where
   an ABI mismatch would more typically surface, immediately and deterministically, not
   probabilistically at ~94-97% progress).
3. **Genuine bimodal bug** (disfavored but not excluded): nothing in either incident points at a
   semantic defect — the crashed worker's assigned test re-ran and passed instantly, and no
   assertion failure or Z3 UNKNOWN result appears anywhere in either log; the signature is
   entirely a process-death signature, not a logic-error signature. This is the least likely of
   the three but cannot be formally excluded without reproducing the crash directly.

**Recommended next action:** do not guess further from log archaeology; add direct instrumentation
instead. Concretely: add a lightweight `psutil`-based peak-RSS-per-worker logger (a `pytest`
plugin hook or a wrapper script around the `pytest ... -n 6` invocation that samples
`/proc/<worker-pid>/status` `VmRSS` every few seconds and writes to a small log) to
`tests.yml`'s Python 3.12 job specifically, gated to run only on that job (cheap, only needed
while this is unresolved), and let it run passively across normal CI traffic until it either
captures a peak-RSS reading near the 16GB ceiling at the next occurrence (confirms hypothesis 1)
or the incident recurs with RSS comfortably below the ceiling (rules out hypothesis 1, redirects
investigation toward hypothesis 2). This is strictly better than a synthetic local reproduction
attempt: the incident is intermittent (2 occurrences observed across many runs) and CI-hardware-
specific (16GB/4vCPU; this report's local machine has 24 cores and far more memory, so it cannot
reproduce a memory-ceiling effect even under `taskset` CPU restriction).

## Decisions

- Item B: no action — confirmed settled, disposition stands.
- Item A: no workflow change made in this research dispatch (per scope: research only). Bounded
  local evidence (554/554 identical outcomes) supports `-n 4` as directionally safe for the
  measured subtrees; full-suite confirmation is recommended before changing `tests.yml`/
  `flake.nix`.
- Item C: recommend extending `test_example_budget_floor.py`'s `_COVERED` list to bimodal,
  exclusion, and imposition at the existing 10s floor, backed by the measurements above.
- Item D: root cause not determined; recommend adding CI-side RSS instrumentation rather than
  further speculation, and note the item-A `-n 4` migration (if adopted) is independently
  expected to reduce this failure mode's likelihood as a side effect.

## Recommendations

1. (C) Extend `_COVERED` in `code/tests/ci/test_example_budget_floor.py` with the three files
   above; keep `_MIN_MAX_TIME = 10` unchanged; add a docstring note distinguishing "floor" from
   the bimodal per-example recalibration record so the two are not read as conflicting.
2. (A) Run the bounded full-selection `-n 6` vs `-n 4` diff (design given above) in a follow-up
   dispatch with a dedicated measurement window (~20-30 minutes), ideally repeated twice, before
   editing `tests.yml`/`flake.nix`. If confirmed clean, change both files together (parity-guard
   enforced) and preserve/reword the `auto`-vs-fixed-`-n` rationale comment.
3. (D) Add `psutil`-based peak-RSS-per-worker logging to the Python 3.12 job in `tests.yml`, scoped
   narrowly to that one job, and leave it running until the next occurrence (or long enough to
   gain confidence the memory hypothesis is wrong) rather than attempting further static analysis
   or local reproduction (infeasible — this machine cannot reproduce a 16GB ceiling).
4. Track A and D together in implementation: if `-n 4` is adopted for (A), re-observe whether (D)
   recurs before investing in dedicated RSS instrumentation — the fix for one may retire the need
   to fully investigate the other, and the recommended order is A first (cheaper, already
   partially measured) then D (only if it still recurs post-A).

## Risks & Mitigations

- **Risk**: (A)'s bounded measurement (bimodal/exclusion/imposition only) misses a flip that only
  manifests in `logos` or `code/tests/`. **Mitigation**: explicitly flagged as unmeasured above;
  the follow-up full-selection run closes this gap before any workflow file is edited.
- **Risk**: (C)'s floor extension could be premature if a not-yet-observed example in these three
  files has a heavier tail than measured here (single-draw measurement, not the seeded-multi-draw
  campaign task 167 used for its two targets). **Mitigation**: the 10s floor is generous relative
  to every measured value (25x+ headroom) even allowing for run-to-run variance of the kind task
  167 found (0% rlimit spread across draws) — the floor is not measuring these examples' typical
  cost tightly, so ordinary variance is not expected to threaten it.
- **Risk**: (D)'s RSS-instrumentation recommendation adds CI complexity for an intermittent issue.
  **Mitigation**: scope it to the Python 3.12 job only, and treat it as removable once the
  hypothesis is confirmed or ruled out — not a permanent addition.

## Appendix

- CI runs referenced: `32915763636` (baseline green, used for job-duration context),
  `32910478240` (Python 3.12 worker crash under the 10s floor), `32897405646` (Python 3.12
  17-minute hang, pre-thread-timeout-guard), both fetched via `gh run view <id> --log` /
  `--log-failed` and `gh api .../jobs`.
- Local measurement commands (representative; full commands used `taskset -c 0,1,2,3` to match
  the CI runner's 4-vCPU footprint):
  - `pytest code/src/model_checker/theory_lib/bimodal -m "not packaging and not performance and
    not unstable and not xdist_serial" -n {6,4} -q --timeout=300 --timeout-method=thread -rA`
  - `pytest code/src/model_checker/theory_lib/exclusion code/src/model_checker/theory_lib/imposition
    -m "not packaging and not performance and not unstable and not xdist_serial" -n {6,4} -q
    --timeout=300 --timeout-method=thread -rA`
  - Isolated per-example timing via `pytest ... -k "<name>" -v --durations=N` on the specific
    node ids listed in the (C) findings table.
