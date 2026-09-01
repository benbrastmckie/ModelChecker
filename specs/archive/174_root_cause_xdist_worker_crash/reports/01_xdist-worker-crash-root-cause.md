# Research Report: Root Cause of Recurring xdist Worker Crash (`[gwN] node down`)

## Scope and Method

This report investigates CI-budget item D — the recurring `[gwN] node down: Not properly
terminated` xdist worker crash — building on the telemetry collected by the worker-count task
and the incident record carried in the task description. Method: (1) re-read the full prior
telemetry report and the two related tasks' plans that touched the same file scope while this
task was open, (2) inspect `worker_rss_sample.py`, `test_frame_class_mapping.py`, and the
bimodal test fixtures directly, (3) inspect the installed `pytest-xdist==3.8.0` source
(`xdist/remote.py`, `xdist/scheduler/load.py`, `xdist/plugin.py`) to replace assumptions about
its scheduling algorithm with verified behavior, (4) reproduce local `--collect-only` orderings
to check structural claims about lead (b). No CI run was triggered by this research task; all
findings are either drawn from existing artifacts or verified locally against the source tree
and the installed xdist package.

## Finding 0 (governs everything else): the crash's confirmed trigger site is currently
unreachable in gating CI — for reasons unrelated to this investigation

This is the single most important fact this report adds to the record, and it must be read
before any hypothesis discussion below.

Both confirmed `node down` incidents, and a third (confounded) occurrence surfaced independently
by task 173's own verification run, all landed inside
`code/src/model_checker/theory_lib/bimodal/tests/`. Since commit `74e6eb08` ("task 153 phase 8:
apply development marker to the bimodal test tree", 2026-08-31), that entire tree — 313 items,
including every test in `test_frame_class_mapping.py` — carries a blanket `development` marker
applied by `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`'s
`pytest_collection_modifyitems` hook. Both of `.github/workflows/tests.yml`'s gating pytest
invocations (`-n 4` parallel pass and the `xdist_serial` serial pass) already carry
`and not development` (added by task 173 phase 2, `a0556fb4`). Verified locally:

```
$ PYTHONPATH=src pytest tests/ src/model_checker \
    -m "not packaging and not performance and not unstable and not xdist_serial and not development" \
    --collect-only -q
2133/2580 tests collected (447 deselected)   # zero bimodal/tests items among them
$ PYTHONPATH=src pytest tests/ src/model_checker \
    -m "xdist_serial and not packaging and not unstable and not development" \
    --collect-only -q
9/2580 tests collected (2571 deselected)     # zero bimodal/tests items among them
```

This is corroborated by a follow-on task's own record: task 179
(`ci_pipeline_exclude_bimodal_until_finished`, `status: completed`,
`specs/179_ci_pipeline_exclude_bimodal_until_finished/`) confirms the same containment is now a
deliberate, documented policy — bimodal is to stay excluded from every gating `-m` expression
"until it is finished" (7 gating invocations total, enforced by
`code/tests/ci/test_unstable_deselection_wiring.py`) — and additionally mirrors the same
`development` blanket into `oracle/conftest.py` (595/644 oracle items), independently confirming
the pattern is not this task's own artifact.

**What this means for item D's exit condition**: `test_frame_class_mapping.py` cannot currently
crash a gating CI run, because it does not run in gating CI at all. This is a real, verifiable
containment — but it is *incidental*, not a fix for this task's crash:

- It was motivated entirely by "bimodal is unfinished," not by the xdist crash. Task 173's own
  plan says so explicitly: "the delegation's explicit instruction [was] not to investigate that
  crash [t]here."
- It is temporary by design. Task 179's description states the intent is to re-admit bimodal to
  gating once it is finished, at which point the exact conditions that produced two confirmed
  crashes return unless this task's investigation has closed the gap by then.
- Per this task's own "innocent bystander" framing, the true cause may not be bimodal-specific.
  If so, containment of bimodal buys time but does not reduce the crash rate on whatever the real
  trigger is — it only removes two (of an unknown total) trigger sites.

**Evidence that the containment is not merely coincidental with a real reduction in crash
frequency**: task 173's own Phase 6 record (`specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`)
captured a *fourth* worker-crash data point, before the quarantine landed:

```
................................F..................................[gw0] node down: Not properly terminated
F
replacing crashed worker gw0
..FF
```

captured from the exact gating `-n 4` command, on a working tree shared with task 153's
then-in-flight, uncommitted changes to `bimodal/semantic/core.py` and
`test_frame_constraints.py`. This occurrence names **`gw0`**, not `gw2` — already a data point
against a "gw2 specifically" reading (see Finding 2 below) — and is explicitly flagged by that
task as confounded (concurrent uncommitted edits in the same files, one test observed blocked in
a 400s+ Z3 solve when killed). After task 153 landed and the tree was clean, the identical
command was re-run and completed **`2132 passed, 1 skipped, 2 warnings in 82.21s`, with no
timeout, no `F`, no worker crash** — a single clean run, which per this task's own "green on one
run is weak evidence" standard is suggestive but not proof that removing bimodal removes the
crash. Taken together, this is now **4 worker-crash observations, 3 of the 4 inside
`theory_lib/bimodal`, 0 of 4 confirmed to occur in a run with bimodal genuinely absent** (the one
clean bimodal-absent run is one data point in a shifting, non-hermetic environment).

## Finding 1: `PYTEST_XDIST_WORKER` gives a concrete, verified mechanism for lead (a)'s
PID-to-worker correlation

Lead (a) asks for "the obvious next instrumentation step": mapping `worker_rss_sample.py`'s
per-PID peaks to xdist worker IDs (`gwN`) and test groups. Reading the installed
`pytest-xdist==3.8.0` source (`xdist/remote.py:416-418`) confirms the mechanism:

```python
os.environ["PYTEST_XDIST_TESTRUNUID"] = workerinput["testrunuid"]
os.environ["PYTEST_XDIST_WORKER"] = workerinput["workerid"]        # e.g. "gw2"
os.environ["PYTEST_XDIST_WORKER_COUNT"] = str(workerinput["workercount"])
```

This is set *inside* each worker subprocess's own environment before it begins executing tests.
Because `worker_rss_sample.py` already discovers worker PIDs as descendants of the pytest
controller PID via `/proc/<pid>/status`'s `PPid:` chain (`discover_descendant_pids`), the exact
same `/proc`-only technique extends cleanly: read `/proc/<pid>/environ` (NUL-separated) for each
discovered descendant and extract the `PYTEST_XDIST_WORKER=gwN` entry. This requires no new
dependency and mirrors the sampler's existing `_parse_ppid`/`read_vm_rss_kb` pattern exactly. It
directly answers "wiring that correlation is the obvious next instrumentation step" — the
mechanism exists and is verified; it is simply not yet implemented in
`.github/scripts/worker_rss_sample.py`, which today records `per_pid_peak_kb` with no `gwN` tag
at all.

Mapping a worker to the *test group* it executed (not just its id) is a harder, separate problem
— xdist does not expose this via environment variable. The closest low-cost mechanism is a
worker-side pytest hook (e.g. `pytest_runtest_logstart`/`pytest_runtest_logreport`) that appends
`(timestamp, nodeid)` to a per-worker log file tagged by `PYTEST_XDIST_WORKER`; cross-referencing
that log's timestamps against the RSS sampler's periodic snapshots would reconstruct which test
was running (and, by comparing successive per-PID RSS readings, how much each test's execution
window contributed) without needing xdist's internal scheduler state at all. This is a plan-phase
implementation item, not something this research task should build.

## Finding 2: the same-worker, same-module pattern (lead b) is real but its mechanism is
different from a naive "hash the module to a fixed worker" story

Investigating lead (b) required understanding pytest-xdist's actual default scheduling
algorithm, `xdist.scheduler.load.LoadScheduling` (the algorithm actually used here:
`xdist/plugin.py` sets `config.option.dist = "load"` automatically whenever `-n`/`--numprocesses`
is passed, and `tests.yml` never overrides `--dist`, so `-n 4`/`-n 6` both run under `"load"`).

Two structural facts, read from `xdist/scheduler/load.py`, replace assumption with verified
behavior:

1. **The initial per-worker batch is not one or two tests — it is a large, module-sized,
   consecutive slice.** `schedule()` computes `node_chunksize = min(items_per_node // 4,
   maxschedchunk)` (with `maxschedchunk` defaulting to `len(collection)`, i.e. unbounded) and
   sends that many *consecutive* collection-order items to each node in round-robin order. For a
   ~2,445-item collection at `-n 4`, that is `~152` consecutive tests per worker's first batch;
   at `-n 6`, `~101`. A single test file's items are always contiguous in collection order (pytest
   collects file-by-file), so a file with fewer tests than the chunk size lands entirely inside
   one worker's batch far more often than a naive "distribute test-by-test" model would predict.
2. **Continuation batches after the initial one are also consecutive, but the worker that
   receives the *next* chunk is determined by which worker asks first** (`check_schedule`, driven
   by `WorkerController.check_schedule`'s duration heuristic) — i.e., by real-time solve-duration
   variance across workers, not by a fixed formula. This part of the process genuinely is
   non-deterministic run-to-run.

Locally reproducing the (pre-quarantine-equivalent) collection order —
`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial"`
(no `and not development`, matching what ran before task 153 phase 8) — places
`test_frame_class_mapping.py`'s first test at 0-indexed collection position **1459** of **2445**
selected items. Computing the deterministic initial-batch windows for that item count:
`-n 4`: `node_chunksize = min(611//4, …) = 152`, so gw0=[0,152), gw1=[152,304), gw2=[304,456),
gw3=[456,608) — position 1459 falls well outside every worker's *deterministic* initial window
for either `-n` value tried. This means the file's assignment to `gw2` in both confirmed
incidents was **not** produced by the algorithm's one deterministic step; it came from the
timing-driven continuation phase, which is a real race and not a fixed congruence.

**Reconciling this with the "two-for-two" observation**: a fixed-assignment story ("`gw2` always
gets this module") is not structurally guaranteed by the algorithm and this task's own framing
("two incidents is a thin base — do not over-fit") should be taken at face value; a coincidence
rate of roughly 1-in-N (N = worker count) per incident is not remarkable evidence on its own.
What the chunk-contiguity property *does* establish, and what is new here, is a mechanistically
different and more useful reading: **whichever worker becomes the "fast finisher" during a run
tends to accumulate multiple large, consecutive chunks over the run's lifetime** (because
`check_schedule` keeps re-filling whichever node goes idle from the front of the same shared
queue), and `theory_lib/bimodal`'s files sit consecutively in collection order next to other
Z3-heavy `theory_lib` suites. A worker that happens to pull one bimodal-adjacent chunk is
structurally likely to keep pulling further bimodal-and-neighbor chunks for the same reason (it
is still the fastest asker), producing a real, non-leak explanation for sustained
per-worker heavy-Z3-test concentration — not proof, but a concrete, testable mechanism (see
Recommendations).

## Finding 3: the RSS asymmetry is equally consistent with "one worker did a disproportionate
share of genuinely heavy work," not only with "spike the 2s sampler missed"

The prior report's own framing (2s sampling cannot see a transient spike) remains valid and is
not contradicted here. But Finding 2's chunk-contiguity mechanism supplies an alternative,
non-exotic explanation for the same observed asymmetry (one worker at 3.59 GiB, siblings at
226–380 MB, peaks *not* simultaneous) that does not require either a memory leak or an ABI fault:
if one worker's dynamic chunk-stream happened to concentrate a disproportionate share of the
suite's Z3-heaviest tests (bimodal's frame-constraint and iteration tests are documented
elsewhere in this repo as taking up to ~82s per node under contention), its cumulative native
allocation — much of it plausibly retained by Z3's own allocator/arena behavior across many
back-to-back solver instantiations within one long-lived process rather than returned to the OS
between tests — would organically dwarf a worker that instead received a mixed bag of cheap
tests. This is a *reasoned hypothesis*, not a confirmed mechanism; it is offered because it
better explains two things the leading hypotheses individually do not: (a) why the two named
"culprit" tests differ (any test executing at the moment a worker's accumulated native footprint
crosses whatever destabilizes it gets blamed — consistent with the "innocent bystander" reading
already on record) and (b) why the asymmetry is 1-worker-heavy rather than uniformly elevated
(the chunk-stream concentration effect is inherently unevenly distributed, unlike a fixed
per-test allocation that would show up more evenly).

`test_frame_class_mapping.py` itself, inspected directly, is not a heavy contributor by its own
settings: its `semantics`/`solved_model` fixtures use `N=2, M=2` (tiny state space), function
scope (fresh per test), and one `solver.check()` call per test — this is consistent with the
"innocent bystander" reading and with the crash log evidence already on record (the replacement
worker re-ran the named test in 0.23s). The heavier candidate work is elsewhere in the same
theory tree (e.g. `bimodal/tests/integration/test_iterate.py`, whose
`TestBimodalIteratorReal::test_iterate_two_produces_distinct_models` is independently documented
at 82.34s under `-n 6` contention) and, per Finding 2, is highly likely to be dispatched to the
*same* worker in the same run given collection-order adjacency (`integration/` sorts before
`unit/` inside `bimodal/tests/`, so `test_iterate.py` is collected immediately ahead of
`test_frame_class_mapping.py`).

## Updated Hypothesis Status

| # | Hypothesis | Status after this research | Basis |
|---|------------|------------------------------|-------|
| 1 | Memory exhaustion (naive: aggregate RSS approaches the 16 GB ceiling) | **Still weakened**, unchanged from the prior report — 4.14 GiB aggregate is ~26% of 16 GB. Not eliminated: 2s sampling cannot see a spike. | Prior telemetry, re-confirmed, not re-measured here. |
| 1b | *(new, narrower)* Concentrated native-memory buildup within one worker from chunk-contiguous heavy-test stacking | **Open, newly articulated, mechanistically plausible, not yet tested.** | Findings 2+3 (xdist source + collection-order adjacency), reasoned not measured. |
| 2 | Python-3.12-specific Z3/z3-solver ABI fault | **Further weakened.** The 4th data point (task 173's confounded `gw0` crash) occurred on whatever Python version that dispatch ran locally (not confirmed 3.12-specific in that record) — adds no support to a 3.12-only story, and the existing 3.11 incident already substantially weakened it. | This report + prior addendum. |
| 3 | xdist/execnet worker-communication fault under load | **Unchanged: gains weight by elimination, nothing confirms it directly.** | No new evidence found either way. |
| — | Same-worker (`gw2`), same-module (`test_frame_class_mapping.py`) binding is a fixed/deterministic scheduling property | **Weakened by mechanism, not by data.** The verified xdist algorithm does not deterministically bind a module to a fixed worker index at the collection positions measured locally; the 4th incident also named a *different* worker (`gw0`). Treat the `gw2` recurrence as likely coincidence riding on a real but non-worker-specific mechanism (Finding 2/3), not as evidence of something special about worker index 2 or about `test_frame_class_mapping.py`'s fixtures specifically. | Finding 2 (verified xdist source + local collection reproduction), Finding 0 (4th incident on `gw0`). |

## Root Cause: NOT identified. Honest record per this task's exit condition

No hypothesis reached confirmation. What changed:

- **Eliminated (to the extent stated)**: a fixed worker-index binding, and a 3.12-only ABI
  explanation.
- **Weakened, not eliminated**: aggregate memory exhaustion as a simple ceiling story.
- **Newly articulated, untested**: a chunk-contiguity-driven concentration mechanism (1b above)
  that would produce exactly the asymmetric, non-simultaneous RSS pattern already measured,
  without requiring a leak or an ABI bug — testable with the instrumentation in
  Recommendations 1–2 below, on whichever future run (bimodal-gated or not) next reproduces a
  `node down` event.
- **Newly established as containment, not fix**: bimodal's already-landed, unrelated
  `development`-marker quarantine (Finding 0) currently removes both confirmed trigger sites from
  every gating invocation. This is real and verifiable today, but is explicitly temporary and
  motivated by a different concern, so it must not be reported or relied on as a resolution of
  item D.

## Recommendations for the next phase (plan/implement)

1. **Extend `worker_rss_sample.py` to tag each PID with its `PYTEST_XDIST_WORKER` value**, read
   from `/proc/<pid>/environ` using the same discovery pass that already reads `/proc/<pid>/status`
   (Finding 1). Low cost, no new dependency, closes lead (a) precisely as specified. Add
   corresponding unit tests in `code/tests/ci/test_worker_rss_sampler.py` (a synthetic
   `/proc/<pid>/environ` fixture, mirroring the existing synthetic `/status` fixtures).
2. **Add a lightweight worker-side per-test log** (a `conftest.py` hook keyed off
   `PYTEST_XDIST_WORKER`, appending `(timestamp, nodeid)` on `pytest_runtest_logstart`) so that a
   future crash's telemetry can be cross-referenced against exactly which tests each worker ran
   and when, testing the Finding 3 "concentrated chunk" hypothesis directly instead of by
   inference. This is the most direct path to confirming or refuting 1b.
3. **Tighten the sampling interval** (lead c) from 2s toward ~0.25s, as already recommended and
   still cheap and unactioned; combine with items 1–2 so a future incident's telemetry is both
   fine-grained and worker-attributed.
4. **Do not attempt the file-level `xdist_serial` experiment (lead d) as originally scoped.**
   It is moot: the entire theory, not just this one file, is already out of both gating passes
   (Finding 0). Recording this explicitly satisfies the task's "record the result either way"
   instruction for lead (d) — the broader version of the experiment already ran, via task 173's
   before/after comparison, with a negative (no-recurrence) result on the one clean data point
   available, which is weak evidence and should be reported as such, not as resolution.
5. **Record the containment's expiry condition** wherever item D's status lives going forward:
   when bimodal is re-admitted to gating (task 179's stated eventual intent), items 1–3 above
   should already be in place so the next `node down` occurrence — inside or outside bimodal —
   is diagnosable on the first observation rather than requiring a fourth or fifth blind
   incident.
6. **Do not close item D.** Per this task's own standard, a single clean run and an incidental,
   temporary containment are not proof of a fix. Carry the updated hypothesis table and the
   containment's fragility forward as this task's honest record, per the exit condition's second
   branch.

## Files Referenced

- `.github/workflows/tests.yml` — both gating pytest invocations, `-n 4`, `and not development`
- `.github/scripts/worker_rss_sample.py` — sampler; extension point identified (Finding 1)
- `code/tests/ci/test_worker_rss_sampler.py` — existing 20-test hermetic suite; extension point
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` — confirmed
  innocent-bystander test file, inspected directly (Finding 3)
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` — the `development`-marker
  blanket hook (Finding 0)
- `code/pyproject.toml` — marker registration, `testpaths`/collection order inputs
- `specs/171_verify_xdist_worker_count_on_real_ci/reports/01_verify-xdist-worker-count-ci.md` —
  prior telemetry (RSS numbers, both confirmed incidents, addendum)
- `specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md` —
  4th (confounded) incident, before/after clean-run comparison (Finding 0)
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/` (state.json entry) — confirms the
  containment is deliberate, documented, and intended to be temporary
- `xdist/remote.py`, `xdist/scheduler/load.py`, `xdist/plugin.py` (installed `pytest-xdist==3.8.0`)
  — verified scheduling algorithm and `PYTEST_XDIST_WORKER` mechanism (Findings 1–2)
