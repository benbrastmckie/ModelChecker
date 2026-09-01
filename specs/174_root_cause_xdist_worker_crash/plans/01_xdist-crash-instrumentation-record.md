# Implementation Plan: Task #174

- **Task**: 174 - root_cause_xdist_worker_crash
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/174_root_cause_xdist_worker_crash/reports/01_xdist-worker-crash-root-cause.md
- **Artifacts**: plans/01_xdist-crash-instrumentation-record.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The root cause of the recurring `[gwN] node down: Not properly terminated` xdist worker crash is
**NOT identified**, and this plan does not pretend otherwise. It executes the second branch of the
task's exit condition: land the instrumentation that would make the *next* recurrence diagnosable
on first observation (per-PID-to-`gwN` correlation via `PYTEST_XDIST_WORKER`, and a tightened
sampling interval), and leave a durable, executable written record of the hypothesis ledger, the
eliminated/weakened hypotheses, and the fact that bimodal's current absence from gating CI is an
*incidental and temporary* containment rather than a fix. No speculative "fix" for an
unidentified cause is planned or permitted here.

Definition of done: the sampler emits worker-id-attributed peaks at a sub-second interval on
every matrix leg; the honest record and its expiry condition are written where a future
investigator will actually find them and are guarded by executable tests; the full gate suite is
green; and none of the task's hard constraints has been violated.

### Research Integration

Findings carried directly into phases:

- **Finding 1** -> Phases 1-2: `xdist/remote.py` sets `PYTEST_XDIST_WORKER=gwN` inside each
  worker's own environment, readable via `/proc/<pid>/environ` using the same `/proc`-only,
  dependency-free discovery pass the sampler already runs over `/proc/<pid>/status`. This closes
  lead (a) exactly as specified.
- **Recommendation 3** -> Phase 3: tighten the 2s interval toward ~0.25s so a transient spike is
  not structurally invisible.
- **Findings 0, 2, 3 + the updated hypothesis table** -> Phase 4: the durable record — 4 incidents
  (not 2), two *different* workers (`gw2` and `gw0`), the newly articulated and untested
  hypothesis 1b (chunk-contiguous heavy-test concentration), the weakening of the fixed-worker-
  binding and 3.12-ABI readings, the negative/moot result for lead (d), and the containment-expiry
  note.
- **Recommendation 6** -> the whole plan: item D stays OPEN. Nothing here closes it.

Deliberately **not** implemented: Recommendation 2 (a worker-side per-test `conftest.py` logging
hook). It requires editing a `conftest.py`, which is outside this task's declared `file_scope`.
Phase 4 records it as the named next step for whoever picks this up, so the deferral is a
documented decision rather than an omission.

### Prior Plan Reference

No prior plan for this task. Two *adjacent* tasks touched the same file scope while this task was
open (173's `development` marker rollout, 179's bimodal gating exclusion); their effect is treated
here as inherited context (Finding 0), not as a template.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` in the delegation context).

## Goals & Non-Goals

**Goals**:
- Tag every sampled PID with its `PYTEST_XDIST_WORKER` id (`gwN`) in the sampler's JSON summary,
  so the next incident's RSS asymmetry is attributable to a named worker rather than a bare PID.
- Tighten the sampling interval from 2s to sub-second, with the sampler's own overhead measured
  rather than assumed.
- Leave an executable, durable record: the updated hypothesis ledger, what was eliminated and by
  what evidence, and the containment's expiry condition.
- Keep item D **open** and honestly labelled as open in every place its status is stated.

**Non-Goals**:
- Identifying the root cause. This plan does not claim to, and no phase asserts one.
- Any speculative remediation (worker recycling, `--max-worker-restart`, memory caps, retries,
  scheduler changes). An unidentified cause does not get a fix.
- Reverting `-n 4`, widening `timeout-minutes`, marking any test `unstable`/`development` to make
  red go green, or re-gating the sampler to Python 3.12. All four are hard constraints; Phase 5
  audits them explicitly.
- Rebuilding the sampler or its 20 existing hermetic unit tests. They exist; this extends them.
- Editing any `conftest.py` (out of declared file scope) — see the deferral note above.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A prose/comment edit to `tests.yml` accidentally trips `TestSamplerIsNotMatrixGated`, whose scan flags any line containing all of `matrix.python-version`, `if`, and `=` | M | M | Phase 4 must not write those three tokens into one comment line; run `code/tests/ci/` after every `tests.yml` edit, not only at phase end |
| A `tests.yml` edit duplicates or reshapes the single literal parallel-pass `pytest` line, breaking `test_workflow_parity.py`'s "exactly one" extraction | H | L | Phase 3 changes only the `--interval` argument on the sampler line; the `pytest` line is not touched at all |
| A 0.25s interval makes the sampler's own `/proc` rescan a measurable CPU competitor to 4 workers on a 4-CPU runner, perturbing the very run it observes | M | M | Phase 3 measures the sampler's own CPU over a real local run before committing the value; fall back to 0.5s and record the measurement if overhead is non-trivial |
| `/proc/<pid>/environ` is unreadable for a descendant (permissions, process exited mid-read) | L | M | Mirror the existing `read_vm_rss_kb` tolerance exactly: return `None`, omit the tag, never raise — a missing tag must degrade to today's untagged behavior, not to a crash |
| The record is written in a way that reads as "item D resolved" | H | L | Phase 4 states OPEN explicitly in each edited location and is verified by an executable guard test in Phase 4 |
| Treating the one clean post-quarantine run as evidence of a fix | H | M | The record states it as one data point in a non-hermetic environment; the failure RATE is the signal, per the task's standard |
| Scope creep into a speculative fix once the instrumentation lands | M | L | Non-Goals above are binding; Phase 5's constraint audit fails the task if a behavioral CI change beyond interval-tagging appears in the diff |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully serial by design: Phases
1-2 are a TDD RED/GREEN pair on the same two files, and Phases 3-4 both edit `tests.yml`, so
parallelism would only produce conflicts.

---

### Phase 1: RED — failing tests for `PYTEST_XDIST_WORKER` PID attribution [COMPLETED]

**Goal**: Write the hermetic unit tests for worker-id attribution *before* any sampler change,
per mandatory TDD. At the end of this phase the new tests fail for the right reason (the
functions/keys do not exist yet), and every pre-existing test still passes.

**Tasks**:
- [x] Extend `code/tests/ci/test_worker_rss_sampler.py` with a synthetic `/proc/<pid>/environ`
      fixture helper, mirroring the existing synthetic `/status` fixture style (NUL-separated
      `KEY=VALUE\0` byte content, written with `write_bytes`).
- [x] Add `TestParseXdistWorkerId`: extracts `gw2` from realistic NUL-separated environ bytes;
      returns `None` when `PYTEST_XDIST_WORKER` is absent; is not confused by
      `PYTEST_XDIST_WORKER_COUNT` (prefix-collision guard — this one matters, both keys are set
      by `xdist/remote.py`); tolerates a trailing NUL and non-UTF8 bytes without raising.
- [x] Add `TestReadXdistWorkerId`: reads a tagged synthetic PID; returns `None` for a missing
      PID directory; returns `None` on an unreadable/`PermissionError` environ file.
- [x] Add tracker/summary tests: `per_pid_peak_kb` entries gain a worker-id association; the
      summary exposes a PID -> `gwN` mapping and a per-worker-id peak; an untagged PID is still
      recorded (degrades to `null`/untagged, never dropped); the summary stays JSON-serializable
      and still carries no threshold/ceiling of any kind.
- [x] Add a worker-replacement test: `gw0` dying and being replaced by a new PID *also* tagged
      `gw0` keeps both PIDs' peaks distinct while both map to `gw0` — this is the exact D
      scenario and must not conflate pids.
- [x] Run `PYTHONPATH=code/src pytest code/tests/ci/test_worker_rss_sampler.py -v` and confirm:
      new tests RED, the pre-existing tests still GREEN. **Deviation**: the Scope Hypothesis
      below assumed 20 pre-existing tests; `pytest --collect-only -q` before this phase's edits
      showed the actual pre-existing count is **22** (3 `TestParseVmRss` + 3 `TestReadVmRssKb` +
      4 `TestDiscoverDescendantPids` + 2 `TestSampleOnce` + 8 `TestPeakTracker` +
      2 `TestSamplerIsNotMatrixGated`). Recorded here per the Scope Hypothesis's own instruction
      rather than silently adjusted; all 22 passed unchanged after this phase's additions, and 14
      new tests failed RED for the correct reason (`AttributeError`/`TypeError` on the
      not-yet-implemented functions/kwarg, not an import or fixture error).

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts roughly 10-12 new test functions across 3-4 new test
classes, and that the existing suite contains exactly 20 tests. Confirm at implementation time by
running the file and comparing collected counts before/after (`pytest --collect-only -q`); if the
existing count is not 20, record the actual number rather than adjusting the claim silently.

**Files to modify**:
- `code/tests/ci/test_worker_rss_sampler.py` - add synthetic `/proc/<pid>/environ` fixture helper
  and the new test classes; do not modify or delete any existing test.

**Verification**:
- New tests fail with `AttributeError`/`KeyError` (function or summary key absent), not with an
  import error or a fixture bug.
- All 20 pre-existing tests still pass.
- `TestSamplerIsNotMatrixGated` untouched and passing.

---

### Phase 2: GREEN — implement `/proc/<pid>/environ` worker-id tagging in the sampler [COMPLETED]

**Goal**: Make Phase 1's tests pass with the minimum sampler change, using the same `/proc`-only,
stdlib-only, no-new-dependency approach the module already commits to.

**Tasks**:
- [x] Add `parse_xdist_worker_id(environ_bytes) -> str | None`: split on `\0`, find the entry
      whose key is exactly `PYTEST_XDIST_WORKER` (exact key match, not `startswith`, so
      `PYTEST_XDIST_WORKER_COUNT` cannot match), decode with `errors="replace"`.
- [x] Add `read_xdist_worker_id(proc_root, pid) -> str | None` reading
      `proc_root/<pid>/environ` via `read_bytes()`, with the identical
      `(FileNotFoundError, ProcessLookupError, PermissionError) -> None` tolerance as
      `read_vm_rss_kb`. Fail-fast applies to programmer errors, not to the normal
      process-exited-mid-read race, which the module already treats as expected.
- [x] Extend `sample_once` to return per-PID `(rss_kb, worker_id)` (or a parallel worker-id map),
      keeping the "raced away -> omit, never record 0" behavior unchanged. **Deviation**:
      `sample_once`'s own return shape (`dict[int, int]`) is left byte-identical instead — several
      Phase-1 (and pre-existing) tests assert against that exact shape and Phase 1 explicitly
      forbids modifying existing tests. Worker-id attribution is instead a parallel map, produced
      by the new `_sample_worker_ids()` helper and threaded into `PeakTracker.record()`'s new
      optional `worker_ids` parameter inside `run()`. Net effect is identical to the plan's intent
      (per-PID RSS and worker-id both flow into the tracker every sample) via a different call
      shape.
- [x] Extend `PeakTracker` with `pid_to_worker: dict[int, str | None]`, recording the first
      non-`None` id seen for a PID and never overwriting it with a later `None`.
- [x] Extend `summary()` with `pid_to_worker` and `per_worker_id_peak_kb` (max per `gwN` across
      the PIDs that carried that id). Keep every existing key and its meaning unchanged, and add
      no threshold, ratio, or ceiling.
- [x] Update the sampler docstring's "What the sampler records" paragraph to name the new fields
      and state that worker-id attribution is best-effort (absent under a non-xdist or
      permission-restricted run).
- [x] Run `PYTHONPATH=code/src pytest code/tests/ci/test_worker_rss_sampler.py -v` — all GREEN
      (36 passed).

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Files to modify**:
- `.github/scripts/worker_rss_sample.py` - new environ parse/read helpers; `sample_once`,
  `PeakTracker`, and `summary()` extended with worker-id attribution.

**Verification**:
- Full `code/tests/ci/` suite green (the sampler's summary shape is consumed by that directory's
  guards, which is why this phase is `interface`, not `local`).
- Importing the module still has zero side effects (no loop, no writes, no `sys.exit`) — assert
  by the existing import-inertness expectations in the test module.
- A manual smoke run against a real local xdist invocation shows at least one `gwN` tag populated
  in the emitted JSON (`--root-pid` of a backgrounded `pytest -n 2`), confirming the mechanism
  works against a real `/proc`, not only synthetic fixtures.

---

### Phase 3: Tighten the sampling interval, with the sampler's own overhead measured [COMPLETED]

**Goal**: Reduce the sampling interval from 2s to sub-second so a transient spike is no longer
structurally invisible — but only after measuring that the sampler does not become a meaningful
CPU competitor to the 4 workers it observes.

**Tasks**:
- [x] Measure first: run the gating parallel command locally with the sampler attached at
      `--interval 0.25`, and record the sampler process's own CPU time (`/usr/bin/time -v` or
      `ps -o cputime`) as a fraction of wall clock. Record the number in the commit message and
      in the Phase 4 record. **Measurement note**: `/usr/bin/time` is not present on this host
      (NixOS); measured instead via `resource.getrusage(RUSAGE_SELF)` deltas taken inside the
      sampler's own Python process across a real local run of the gating `-n 4` parallel command
      (`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable
      and not xdist_serial and not development" -n 4`). **Result at `--interval 0.25`: sampler
      CPU = 6.134s (3.941s user + 2.193s sys) over a 96.207s wall run = 6.375% of one core**
      (361 samples taken). This is well above the plan's ~2% target.
- [x] Choose the interval on that measurement: `0.25` if the sampler's own CPU is a small
      fraction (target: under ~2% of one core); otherwise `0.5`. Record which was chosen and why
      — an unmeasured choice is not acceptable here. **Chosen: `0.5`**, per the plan's own
      fallback, because 0.25's measured 6.375%-of-one-core overhead exceeds the ~2% target. For
      comparison, `--interval 0.5` was also measured on an identical local run: sampler CPU =
      2.749s (1.783s user + 0.966s sys) over an 83.782s wall run = **3.28% of one core** (163
      samples) — smaller but still not clearly under 2% on this (shared, non-CI-dedicated) local
      host; 0.5 is taken as the designated fallback per the plan's explicit two-value choice
      rather than iteratively searched for a value that clears 2% on this particular host, whose
      CPU contention does not necessarily represent the dedicated `ubuntu-latest` runner. Honest
      framing carried into Phase 4's record: this is a measured, not assumed, choice, and the
      absolute numbers are host-local, not CI-runner numbers.
- [x] Update `DEFAULT_INTERVAL_S` in `.github/scripts/worker_rss_sample.py` to the chosen value.
- [x] Update the `--interval` argument on the single sampler invocation line in
      `.github/workflows/tests.yml`. Change **only** that argument. Do not touch the `pytest`
      lines, `-n 4`, the `-m` expressions, or `timeout-minutes`. Verified via
      `git diff .github/workflows/tests.yml`: exactly one line changed, `--interval 2` ->
      `--interval 0.5`.
- [x] Add a guard test to `code/tests/ci/test_worker_rss_sampler.py` asserting the `--interval`
      value in `tests.yml` is <= 0.5, with a docstring explaining that a coarse interval is what
      made the two confirmed incidents' RSS traces uninformative.
- [x] Run the full `code/tests/ci/` suite, especially `test_workflow_parity.py` and
      `test_unstable_deselection_wiring.py`. 151 passed (150 + the new interval guard);
      `test_workflow_parity.py`'s `test_worker_count_matches` and
      `test_parallel_pass_marker_expression_matches` confirm `-n 4` and both `-m` expressions are
      byte-identical to before.

**Timing**: 0.75 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: This phase assumes `tests.yml` contains exactly one `worker_rss_sample.py`
invocation line carrying `--interval 2` (as `TestSamplerIsNotMatrixGated` already asserts).
Confirm with `grep -n 'worker_rss_sample.py' .github/workflows/tests.yml` before editing; if more
than one line matches, stop and re-plan rather than editing both.

**Files to modify**:
- `.github/scripts/worker_rss_sample.py` - `DEFAULT_INTERVAL_S`.
- `.github/workflows/tests.yml` - the `--interval` argument on the sampler line only.
- `code/tests/ci/test_worker_rss_sampler.py` - the interval guard test.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/ -v` green.
- `git diff .github/workflows/tests.yml` shows changes confined to the `--interval` argument (plus
  Phase 4's comments, if phases are committed together — they should not be).
- `-n 4`, both `-m` expressions, and every `timeout-minutes` value are byte-identical to before.

---

### Phase 4: The durable, executable honest record [NOT STARTED]

**Goal**: Satisfy the exit condition's second branch. Write, where a future investigator will
actually land, (a) the updated hypothesis ledger with what was eliminated and by what evidence,
(b) the 4-incident count and the two distinct worker ids, (c) the newly articulated untested
hypothesis 1b, (d) the moot/negative result for lead (d), (e) the deferred worker-side per-test
log as the named next step, and (f) the containment-expiry note — that bimodal's absence from
gating is incidental, temporary, and not a fix.

**Tasks**:
- [ ] Rewrite the hypothesis paragraph in `.github/scripts/worker_rss_sample.py`'s module
      docstring: it currently describes a "Python 3.12-only" crash and three hypotheses. Replace
      with the current ledger — 4 observations, `gw2` x2 / `gw0` x1 / one confounded, observed on
      both 3.11 and 3.12; hypothesis 2 (3.12-only ABI) weakened; fixed-worker-index binding
      weakened by the verified `LoadScheduling` algorithm; hypothesis 1b (chunk-contiguous
      heavy-Z3 concentration within one worker) newly articulated and **untested**. State
      explicitly: root cause NOT identified, item D OPEN.
- [ ] Add the containment-expiry note to the same docstring and to the `tests.yml` telemetry
      comment block: `theory_lib/bimodal` is currently out of every gating `-m` expression via a
      blanket `development` marker applied for an unrelated reason ("bimodal is unfinished"),
      which incidentally removes the confirmed trigger sites. **This is containment, not a fix, and
      it expires when bimodal is re-admitted to gating.** Name the instrumentation that must be in
      place by then (this task's Phases 2-3, plus the deferred per-test log).
- [ ] Record lead (d) as moot with its reasoning: a file-level `xdist_serial` experiment is
      superseded because the entire theory is already out of both gating passes; the broader
      before/after comparison already ran with a single clean post-quarantine run, which is weak
      evidence and is reported as such, not as resolution.
- [ ] Record the deferred next step: a worker-side `pytest_runtest_logstart` hook writing
      `(timestamp, nodeid)` to a per-worker log keyed by `PYTEST_XDIST_WORKER`, which is what
      would test hypothesis 1b directly. Note it was deferred because `conftest.py` is outside
      this task's declared file scope.
- [ ] Add a short header comment to
      `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` noting
      it is a confirmed *innocent bystander* (two incidents killed two different tests in this
      file; its own fixtures are `N=2, M=2`, one `solver.check()` per test, and the replacement
      worker re-ran the named test in 0.23s), pointing at the sampler docstring for the record.
      **Add no marker and change no test** — the file's collected test count and markers must be
      byte-for-byte equivalent afterwards.
- [ ] Add an executable guard test to `code/tests/ci/test_worker_rss_sampler.py` asserting the
      sampler docstring still contains the containment-expiry note and an explicit
      root-cause-open statement, so a future edit cannot quietly downgrade the record to
      "resolved".
- [ ] Re-run `code/tests/ci/` after **each** `tests.yml` comment edit (not just at phase end) —
      `TestSamplerIsNotMatrixGated` scans every line for the `matrix.python-version` + `if` + `=`
      token combination, and a careless comment can trip it.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts the record must land in exactly three files (the sampler
docstring, the `tests.yml` comment block, the bystander note) plus one guard test. Confirm at
implementation time that no *other* in-scope location states item D's status (e.g. a stale
"Python 3.12-only" claim elsewhere in `tests.yml`); `grep -rn "3.12-only\|item D\|node down"` over
the four in-scope files before declaring the record complete.

**Files to modify**:
- `.github/scripts/worker_rss_sample.py` - module docstring: hypothesis ledger, root-cause-open
  statement, containment-expiry note, deferred-next-step note.
- `.github/workflows/tests.yml` - telemetry comment block: same ledger summary and expiry note.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - innocent-
  bystander header comment only; no marker, no test change.
- `code/tests/ci/test_worker_rss_sampler.py` - the record-integrity guard test.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/ -v` green.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py --collect-only -q`
  reports the same collected count as before the edit.
- `grep -c "development\|unstable" code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`
  is unchanged (no marker added).
- Reading the sampler docstring cold, a new investigator can state: what was eliminated, what is
  open, why the crash is not currently reproducing in gating, and what to do first on the next
  recurrence.

---

### Phase 5: Full-gate verification and hard-constraint audit [NOT STARTED]

**Goal**: Run the complete gate set and prove, mechanically, that none of the task's six hard
constraints was violated anywhere in the diff.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — full green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ci/ -v` — the CI-guard suite specifically, green.
- [ ] Reproduce both gating `--collect-only` invocations from the research report and confirm the
      selected counts are unchanged from the pre-task baseline (the record edits must not have
      altered selection).
- [ ] Constraint audit against `git diff` for the whole task:
      - `-n 4` present and unchanged in `tests.yml`; no reversion to `-n 6`.
      - Every `timeout-minutes` value byte-identical; none widened.
      - No `unstable` or `development` marker added to `test_frame_class_mapping.py` or any other
        test.
      - No `matrix.python-version` gate around the sampler step;
        `TestSamplerIsNotMatrixGated` passing.
      - The sampler's 20 original tests all still present and passing (none rewritten or deleted).
      - No speculative remediation in the diff: no worker-recycling flag, no
        `--max-worker-restart`, no memory cap, no retry wrapper, no scheduler/`--dist` change.
- [ ] Confirm item D is stated as OPEN in every location the record touches, and that no artifact
      produced by this task claims a root cause or a fix.

**Timing**: 0.5 hours

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- None (verification only).

**Verification**:
- Full suite green; every audit bullet above explicitly checked and its result recorded in the
  implementation summary, not merely asserted.
- Any audit failure blocks completion — it is not a note-and-proceed.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/ci/test_worker_rss_sampler.py -v` — original 20 tests
      plus the new attribution, interval-guard, and record-integrity tests, all green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — full suite green.
- [ ] `test_workflow_parity.py` and `test_unstable_deselection_wiring.py` green after every
      `tests.yml` edit.
- [ ] A real local `pytest -n 2` smoke run produces a JSON summary with at least one populated
      `gwN` tag — the mechanism is verified against a live `/proc`, not only synthetic fixtures.
- [ ] `test_frame_class_mapping.py`'s collected test count and marker set are unchanged.
- [ ] Sampler overhead at the chosen interval measured and recorded (a number, not an assurance).
- [ ] TDD order honored: Phase 1 RED committed before Phase 2 GREEN.

## Artifacts & Outputs

- `.github/scripts/worker_rss_sample.py` — worker-id attribution via `/proc/<pid>/environ`;
  tightened default interval; rewritten hypothesis-ledger docstring carrying the honest record and
  the containment-expiry note.
- `.github/workflows/tests.yml` — `--interval` reduced; telemetry comment block updated with the
  current ledger and expiry note. No behavioral change beyond the interval.
- `code/tests/ci/test_worker_rss_sampler.py` — new attribution tests, the interval guard, and the
  record-integrity guard, alongside the untouched original 20.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` — innocent-
  bystander header comment only.
- `specs/174_root_cause_xdist_worker_crash/summaries/01_*-summary.md` — implementation summary
  recording the measured overhead number, the audit results, and item D's status: **OPEN**.

## Rollback/Contingency

Every change here is additive instrumentation or comment text, so rollback is per-phase and cheap:

- **Phases 1-2 (attribution)**: revert the two files. The sampler returns to its current
  untagged-but-working behavior; nothing else depends on the new summary keys.
- **Phase 3 (interval)**: revert `--interval` and `DEFAULT_INTERVAL_S` to `2`, and drop the guard
  test. If the measurement in Phase 3 shows the sampler perturbs the run at 0.25s, the plan's own
  fallback is 0.5s — take it and record the measurement; do not ship an unmeasured interval.
- **Phase 4 (record)**: comment-only; revertible without any behavioral effect. If a `tests.yml`
  comment trips a guard test, shorten the comment rather than weakening the guard.
- **If the sampler proves to cost more than it informs**: the whole instrumentation is removable
  in one piece, exactly as its docstring already documents — delete the script, its test module,
  and the workflow step. But do not remove it while item D is open; the point of this task is that
  the next incident must be diagnosable on first observation.
