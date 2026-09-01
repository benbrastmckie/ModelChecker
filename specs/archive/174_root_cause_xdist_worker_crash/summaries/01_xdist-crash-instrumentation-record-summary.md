# Implementation Summary: xdist worker crash instrumentation and honest record

- **Task**: 174 - root_cause_xdist_worker_crash
- **Status**: [COMPLETED]
- **Started**: 2026-09-01T07:00:00Z
- **Completed**: 2026-09-01T08:35:00Z
- **Effort**: ~4 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_xdist-crash-instrumentation-record.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The root cause of the recurring `[gwN] node down: Not properly terminated` xdist worker crash
(item D) was **not identified** by this task, and this summary does not claim otherwise. Per the
task's exit condition's second branch, the plan's five phases landed instrumentation that will
make the *next* recurrence diagnosable on first observation, and left a durable, executable,
honest record of the current hypothesis ledger. No speculative fix for an unidentified cause was
implemented.

## What Changed

- `.github/scripts/worker_rss_sample.py`: added `parse_xdist_worker_id`/`read_xdist_worker_id`
  (reading `PYTEST_XDIST_WORKER` from `/proc/<pid>/environ`, exact-key-matched against
  `PYTEST_XDIST_WORKER_COUNT`); `PeakTracker` gained `pid_to_worker` and an optional `worker_ids`
  parameter on `record()`; `summary()` gained `pid_to_worker` and `per_worker_id_peak_kb`;
  `DEFAULT_INTERVAL_S` tightened `2.0 -> 0.5` on measured overhead; module docstring rewritten
  with the current 4-incident hypothesis ledger, containment-expiry note, and deferred-next-step
  note.
- `.github/workflows/tests.yml`: sampler `--interval 2 -> --interval 0.5` (only argument
  changed); telemetry comment block updated to carry the same ledger and expiry note.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`: added an
  "innocent bystander" header note (no marker, no test change; collected count unchanged at 14).
- `code/tests/ci/test_worker_rss_sampler.py`: 21 new hermetic tests across four new classes
  (`TestParseXdistWorkerId` x5, `TestReadXdistWorkerId` x3, `TestPeakTrackerWorkerAttribution` x6,
  `TestSamplerIntervalIsSubSecond` x1, `TestRecordIntegrityItemDStaysOpen` x6); all 22
  pre-existing tests untouched and passing.

## Decisions

- Kept `sample_once()`'s return shape (`dict[int, int]`) unchanged rather than switching to
  `(rss_kb, worker_id)` tuples, to avoid modifying pre-existing/Phase-1 tests; worker-id
  attribution instead flows as a parallel map threaded through `PeakTracker.record()`'s new
  optional `worker_ids` parameter.
- Chose `--interval 0.5` (the plan's designated fallback) over `0.25`, because `0.25`'s measured
  overhead (6.375% of one core, via `resource.getrusage` deltas across a real local run of the
  gating parallel command) exceeded the plan's ~2% target; `0.5` measured at 3.28%.
- Lead (d) (a file-level `xdist_serial` experiment) recorded as moot rather than run — the entire
  `theory_lib/bimodal` tree is already excluded from gating, so isolating one file tests nothing
  the current configuration doesn't already guarantee.
- Recommendation 2 (a worker-side `pytest_runtest_logstart` log) deliberately deferred, not
  built: it requires a `conftest.py` edit outside this task's declared file scope. Named as the
  next step in both edited records rather than silently dropped.

## Plan Deviations

- Phase 1's Scope Hypothesis assumed 20 pre-existing sampler tests; the actual count (confirmed
  by `--collect-only`) was 22. Recorded per the hypothesis's own instruction rather than silently
  adjusted; carried consistently through every later phase's counts.
- Phase 4's checklist and its handoff briefly miscounted the `TestRecordIntegrityItemDStaysOpen`
  guard class as 7 tests; Phase 5's constraint audit caught this via `--collect-only` (the actual
  count is 6) when the +21-item arithmetic across both gating passes required it to reconcile
  exactly. Corrected in both artifacts; not amended into the already-committed Phase 4 commit.
- No other deviations. `sample_once()`'s shape preservation (see Decisions) is a deliberate
  interface choice, not a deviation from plan intent — the plan itself offered "a parallel
  worker-id map" as an accepted alternative shape.

## Impacts

- The next `[gwN] node down` recurrence will produce a `worker-rss-summary.json` with per-pid
  `gwN` attribution and sub-second-interval peaks, closing the diagnostic gap that made both
  confirmed incidents' telemetry uninformative.
- The hypothesis ledger now lives in two places a future investigator will actually find
  (`worker_rss_sample.py`'s docstring, `tests.yml`'s telemetry comment) and is guarded against
  silent downgrade to "resolved" by six executable tests.
- `theory_lib/bimodal`'s current gating exclusion is now explicitly documented, in the sampler's
  own record, as containment rather than a fix, with its expiry condition named — future work
  re-admitting bimodal to gating has a concrete pre-condition list to check against.
- Item D remains OPEN. This task changes what is known and what is instrumented; it does not
  close the item.

## Follow-ups

- When `theory_lib/bimodal` is re-admitted to gating (see task `ci_pipeline_exclude_bimodal_until_finished`'s
  stated intent), confirm the deferred worker-side `pytest_runtest_logstart` hook (or equivalent)
  is built before or alongside that re-admission, per the containment-expiry note.
- On the next `[gwN] node down` recurrence, read the `pid_to_worker`/`per_worker_id_peak_kb`
  fields in the emitted JSON summary first — this is the concrete first-response instruction the
  record leaves for whoever handles it.
- Hypothesis 1b (chunk-contiguous heavy-Z3 concentration) remains untested; the deferred
  worker-side log is the direct test for it.

## References

- `specs/174_root_cause_xdist_worker_crash/plans/01_xdist-crash-instrumentation-record.md`
- `specs/174_root_cause_xdist_worker_crash/reports/01_xdist-worker-crash-root-cause.md`
- `specs/174_root_cause_xdist_worker_crash/handoffs/phase-{1..5}-handoff-*.md`
- `.github/scripts/worker_rss_sample.py`
- `.github/workflows/tests.yml`
- `code/tests/ci/test_worker_rss_sampler.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`
