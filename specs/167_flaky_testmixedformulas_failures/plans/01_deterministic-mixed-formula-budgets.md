# Implementation Plan: Task #167

- **Task**: 167 - Fix flaky TestMixedFormulas failures (`test_mixed_or_diamond_prev`, `test_mixed_and_all_future_neg`)
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours (route-exclusive; see "Route exclusivity" below — realistic single-route total is ~4.25h)
- **Dependencies**: None
- **Research Inputs**: `specs/167_flaky_testmixedformulas_failures/reports/01_flaky-testmixedformulas-root-cause.md`
- **Artifacts**: plans/01_deterministic-mixed-formula-budgets.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, code/docs/core/TESTING_GUIDE.md (sections 8.6, 8.9)
- **Type**: python
- **Lean Intent**: false

## Overview

Both target tests convert a wall-clock budget overrun into a hard failure: `find_countermodel()`
maps `timeout_ms` directly to Z3's `max_time`, and neither test catches `OracleTimeoutError`, so
the sole variable governing pass/fail is real wall-clock solve time against a fixed budget. Three
prior investigations already responded with `xdist_serial` markers and budget widenings; a fourth
reactive widening is explicitly forbidden by `test_mixed_and_all_future_neg`'s own docstring.

This plan does not widen a wall-clock budget first. It first **measures whether the quantity of
Z3 work is run-to-run deterministic** — using Z3's resource-unit counter (`rlimit`) rather than
wall clock — and, if it is, replaces the load-dependent pass/fail boundary with a load-independent
one by plumbing the already-existing, already-plumbed-to-the-solver `max_rlimit` setting through
the oracle provider. `max_rlimit` is the deterministic complement to `max_time` that
`code/docs/core/TESTING_GUIDE.md` section 8.6 already documents and blesses for exactly this case
("Prefer `max_rlimit` alongside `max_time` … for a test whose flakiness is specifically load-driven
rather than a genuine near-budget solve"), and it is wired end-to-end in
`ExampleSettings` -> `ModelDefaults.solve()`/`re_solve()` -> `Z3SolverAdapter.set_rlimit()` — but
`Z3OracleProvider.find_countermodel()` builds its own settings dict and never sets it.

**Definition of done**: the two tests' pass/fail outcome no longer depends on host load, and the
basis for that claim is a recorded measurement — or, if measurement shows the work quantity is
itself nondeterministic, the honest fallback (`unstable` marking on the existing machinery) is
taken with that measurement recorded as the reason.

### Research Integration

Taken as established and not re-litigated:

- Root cause is genuine Z3 solve-time variance sitting close to the `timeout_ms` budgets.
- Test ordering / state leakage is **ruled out** (`isolated_z3_context()` per solve, fresh
  `Z3OracleProvider` per test via `setup_method`, no `pytest-randomly`, no default `-n`,
  order-independent measured timings at 114.86s source-order vs. 110.20s reversed).
- A semantics defect is **ruled out** (every probe across four investigations finds the *same*
  countermodel; a timeout is an inconclusive result, never a wrong verdict).
- A fourth unmeasured budget bump repeats what has been tried three times and is prohibited.

The research's own measurement supplies the key structural clue this plan builds on: two
non-adjacent isolated runs of `test_mixed_and_all_future_neg` produced an **identical** 31.70s wall
time, while the spread across all four draws (27.47s / 31.70s / 31.70s / 52.86s = 1.92x) tracks the
host's load average of 6-10 on 24 cores. That is the signature of a *fixed* amount of Z3 work being
scheduled against a *varying* amount of CPU — i.e. the pass/fail boundary is measured in the wrong
unit, not set at the wrong number.

One correction this plan draws from the report, which changes the recommended sizing: the
already-recorded 80.6s and 107.4s heavy draws were measured on **pinned, non-default
`sat.random_seed`/`smt.random_seed` values**. Nothing in the oracle path
(`provider.py`, `BimodalSemantics`, `ModelConstraints`, `isolated_z3_context()`) sets a seed, so
production always executes the *default-seed* draw. Those cross-seed tail figures therefore
characterize a distribution the test never samples from. Phase 2 measures the quantity that
actually governs these tests: the default-seed work quantity, and whether it is stable.

### Prior Plan Reference

No prior plan. This is the first plan for task 167.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md was loaded. No roadmap
phases are included.

## Route exclusivity

Phase 3 is a decision gate. Exactly one of two downstream routes executes:

- **Route A** (Phases 4-5) — taken when Phase 2 shows the default-seed rlimit is stable across
  repeated draws. Preferred; satisfies "make the outcomes deterministic" literally.
- **Route B** (Phase 6) — taken when Phase 2 shows the rlimit itself varies materially. The
  documented `unstable` fallback, reusing the existing machinery.

The route **not** taken closes as `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions`
record naming the Phase 3 measurement that excluded it. It is never marked `[COMPLETED]` and never
silently skipped.

## Process constraints (binding on every phase)

These are contract terms for the implementer, not advice. They exist because the immediately
preceding task lost three separate implementation dispatches to exactly the failure mode in the
first bullet.

1. **Never background a slow command and then end the turn waiting on it.** Every `pytest`, every
   probe invocation, every `gh` call runs in the **foreground** with an explicit
   `timeout <seconds>` prefix. `run_in_background` is prohibited for any command in this plan.
   There is no "kick it off and check later" step anywhere in this plan.
2. **Every long command carries an explicit `timeout`.** A command with no `timeout` prefix is a
   defect in the invocation, not a slow run to be waited out.
3. **A probe that hits its `timeout` is a recorded data point, not a blocker.** Record it as
   "undecided at ceiling Ns" in the measurement log and move to the next draw. Do not retry it,
   do not widen the ceiling mid-campaign, do not treat it as a phase failure.
4. **Phase 2 has a hard total wall-clock ceiling of 45 minutes.** When the ceiling is reached,
   Phase 2 ends with whatever draws completed. A partial campaign that reaches Phase 3 with an
   honest record beats a complete campaign that never reports.
5. **Do not undo recently-landed work.** `TestGatingConclusiveScan`'s `unstable` marking, the
   extraction of `.github/scripts/unstable_watch_classify.py` from workflow YAML, and the
   `not unstable` deselection on **both** passes of `oracle/run-oracle-suite.sh` all stay exactly
   as they are. Route B extends that machinery; it never forks or replaces it.

## Goals & Non-Goals

**Goals**:

- Make `test_mixed_or_diamond_prev` and `test_mixed_and_all_future_neg` produce the same outcome
  regardless of host CPU load, with a recorded measurement as the basis.
- Establish, by measurement, whether the default-seed Z3 work quantity for these two formulas is
  run-to-run deterministic — the one open question from the research that changes the answer.
- Leave a reusable probe harness in the tree, so the next "recalibrate from a fresh uncensored
  probe" instruction (which `TESTING_GUIDE.md` issues repeatedly) does not require another ad hoc
  scratch script.
- If determinism cannot be established, route to the `unstable` fallback **with the measurement
  recorded**, and make that fallback actually work end-to-end (see the classifier defect below).

**Non-Goals**:

- Changing the bimodal semantics, the quantifier encoding, or `find_countermodel()`'s
  timeout-vs-UNSAT contract. The countermodel is genuinely found; this is a budget-unit problem.
- Removing `@pytest.mark.xdist_serial` from either test. Both markers stay: they address a
  different, real mechanism (`-n 6` contention) and are load-bearing for
  `oracle/run-oracle-suite.sh`'s two-pass split.
- A fourth unmeasured `timeout_ms` bump. Any budget change in this plan carries measured numbers
  and is recorded in the test docstring alongside them.
- Reproducing the originally reported failure by sampling until it happens (see "Explicit
  disposition of the research's open items").
- Introducing a pinned `sat.random_seed`/`smt.random_seed` into the *production* solve path.
  Seed pinning stays a probe-only tool; pinning it in production would freeze one arbitrary draw
  and hide genuine cost regressions.

## Explicit disposition of the research's open items

The research listed four things it could not determine. Each is decided here, with the reason.

| Open item | Decision | Why |
|---|---|---|
| **1. No direct repro of the reported failure** | Do **not** plan a sampling campaign. Do plan a cheap *forced* repro (Phase 2, step 5). | Sampling until a low-probability wall-clock tail event fires costs hours and violates the 45-minute ceiling. It is also unnecessary under Route A: determinism is established *positively* (identical rlimit across draws), not by observing a failure. The one thing the failure mode is genuinely needed for is authoring the Route B classifier signature — and that is obtained in seconds by deliberately under-budgeting a probe, which times out fast by construction. |
| **2. Z3-internal search variance not separated from host scheduling variance** | **Plan work — this is the load-bearing measurement.** Phase 2 separates them at zero incremental cost. | This is the item that changes the whole approach. rlimit counts Z3's internal resource units and is load-independent; wall clock is not. Reading both from the same draws separates the two mechanisms directly, and the answer selects Route A vs. Route B. |
| **3. Behavior under actual `-n` contention untested** | Do **not** plan work. | Both tests carry `xdist_serial`, and `oracle/run-oracle-suite.sh` routes them to pass 2 (`-m "xdist_serial and not slow and not unstable"`, no `-n`). Measuring under `-n 6` would characterize an invocation path the gating suite never takes, at the cost of a full parallel suite run. The structural guarantee is already in place and is re-verified in Phase 7 by confirming both markers survive. Note as a free side effect: Route A's widened `max_time` also increases headroom for an ad hoc developer `-n auto` run, without that being a goal. |
| **4. CI flake-rate history not mined** | Plan a **bounded, non-blocking, single-query** attempt (Phase 2, step 6, `timeout 60`); unavailability is recorded and the phase proceeds. | `gh` access to Actions history is not guaranteed in this environment, and a base rate is not needed for Route A's positive determinism proof. But it is cheap and has one high-value trigger: `test_mixed_and_all_future_neg`'s docstring states that a **serial** failure is the specific event that invalidates its 60000ms basis. One `gh run list` query can confirm or fail to confirm that, so it is worth 60 seconds. It must never block the phase. |

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Measured rlimit is *not* stable across repeated default-seed draws, invalidating Route A | H | M | This is precisely what Phase 3's gate tests for. Route B exists as the planned, honest fallback and is fully specified — a nondeterministic result is an outcome, not a plan failure. |
| Python hash randomization (`PYTHONHASHSEED`) perturbs constraint-construction order and thus Z3's search | M | M | Phase 2 records `PYTHONHASHSEED` per draw. If rlimit varies while all else is fixed, re-run 2 draws with `PYTHONHASHSEED=0` before concluding — this converts an apparent Z3 nondeterminism into a diagnosed, fixable one. Budget for this is inside the 45-minute ceiling. |
| rlimit consumption is Z3-version-dependent, so a Z3 upgrade silently invalidates a calibrated `max_rlimit` | M | M | Record the exact Z3 version in the test docstring next to the measured rlimit, and state the recalibration trigger explicitly, matching the existing docstrings' convention of recording the basis alongside the number. Set `max_rlimit` at generous headroom (>=3x measured), not at measured-plus-margin. |
| Route B's `unstable` marking silently fails to classify: `classify()`'s `MAX_TIME_BY_NODEID_FRAGMENT` path requires `FAILURE_SIGNATURE = "Test failed for example:"`, which an `OracleTimeoutError` failure text does **not** contain | H | H (near-certain if done naively) | Called out as a first-class Phase 6 task. Route B adds a **dedicated `classify()` branch** following the `GATING_FLOOR_NODEID_FRAGMENT` pattern the module's own comment prescribes for non-`max_time`-dict signatures — not a `MAX_TIME_BY_NODEID_FRAGMENT` entry. Pinned by new tests in `code/tests/ci/test_unstable_watch_classifier.py`. |
| Probe campaign overruns the wall-clock ceiling | M | M | Hard 45-minute ceiling, explicit per-draw `timeout`, bounded repetition count (3 draws/test), timeout-as-data-point rule. Phase 2 may end partial and still feed Phase 3. |
| `OracleTimeoutError`'s message becomes dishonest under Route A (it asserts "within {timeout_ms} ms" even when the rlimit budget is what fired) | M | H under Route A | Phase 4 makes the message name both budgets when `max_rlimit` is set. Pinned by a test. The two existing construction sites in `test_cross_oracle_differential.py` keep working because the new parameter is optional. |
| Route B raises `unstable-watch.yml`'s oracle-step runtime by ~4 minutes (two heavy solves added to `-m unstable`) | L | H under Route B | Non-gating workflow, nightly cadence. Note it in the Route B record rather than treating it as a blocker. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 6 | 3 |
| 5 | 5 | 4 |
| 6 | 7 | 5, 6 |

Phases within the same wave can execute in parallel. **Wave 4 is the route-exclusive wave**:
Phase 4 (Route A) and Phase 6 (Route B) are mutually exclusive by Phase 3's decision, not
genuinely parallel — exactly one runs, the other closes `[COMPLETED WITH EXCLUSIONS]`.

---

### Phase 1: Reusable solve-cost probe harness [COMPLETED]

**Goal**: A standalone, foreground CLI that solves one oracle formula through the exact
`find_countermodel()` pipeline and reports wall time, decided/undecided, and the Z3 rlimit
consumed — so every later measurement in this plan, and every future "recalibrate from a fresh
uncensored probe" instruction in `TESTING_GUIDE.md`, uses one tested tool instead of a scratch
script.

**Tasks** (TDD — tests first, per `code/docs/core/TESTING_GUIDE.md`):

- [x] Write `oracle/bimodal_logic/tests/test_probe_solve_cost.py` (RED) covering: the CLI reports
      a decided result with a positive rlimit for a cheap **atemporal** formula (sub-second, so
      the test itself is fast and unmarked); it reports `undecided` rather than raising when given
      a deliberately tiny `--timeout-ms`; it emits one machine-readable JSON record per draw; it
      accepts and applies `--seed` (pinning `sat.random_seed` and `smt.random_seed`) and
      `--repeat N`.
- [x] Implement `oracle/probe_solve_cost.py` (GREEN), sited alongside the existing standalone
      `oracle/scan_runner.py` CLI. It must replicate `find_countermodel()`'s settings dict
      verbatim (`N=2`, `M=max(depth+2,3)`, `temporal_depth`, `contingent=False`,
      `disjoint=False`, `max_time`, `expectation=True`, `solver='z3'`) inside
      `isolated_z3_context()`, so a probed number is a number about the real path.
- [x] Read the consumed rlimit from the solver's Z3 statistics. `ModelDefaults.solve()` keeps
      `self.stored_solver` alongside `self.solver`, and `Z3SolverAdapter.raw_solver()` exposes the
      underlying `z3.Solver`, so `structure.stored_solver.raw_solver().statistics()` is the
      intended access path. **Confirm this survives `_cleanup_solver_resources()`** — see Scope
      Hypothesis. If it does not, capture the statistic inside a probe-local replication of the
      solve call rather than reaching into the structure after the fact.
- [x] Record `PYTHONHASHSEED`, the resolved `z3.get_version_string()`, and the seed (or `default`)
      in every emitted JSON record.
- [x] Verify: `timeout 300 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_probe_solve_cost.py -v`

**Timing**: 1.0 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts that the consumed rlimit is reachable via
`structure.stored_solver.raw_solver().statistics()` after `solve()` returns. Confirm at
implementation time by asserting a positive rlimit in the RED test *before* writing the
production path; if the statistic is unreachable post-cleanup, fall back to capturing it inside a
probe-local solve replication and record the deviation in the phase handoff.

**Files to modify**:

- `oracle/probe_solve_cost.py` - new standalone probe CLI
- `oracle/bimodal_logic/tests/test_probe_solve_cost.py` - new unit tests (atemporal formulas only,
  so this file adds no slow tests to the gating suite)

**Verification**:

- The new test file passes in under 60 seconds total.
- A manual single invocation against an atemporal formula prints a JSON record containing
  non-null `wall_s`, `rlimit`, `decided`, `z3_version`, `pythonhashseed`.
- The new test file introduces no `slow`, `xdist_serial`, or `unstable` marker (it is fast by
  construction), and `timeout 300 env PYTHONPATH=code/src pytest code/tests/ci/ -q` still passes.

---

### Phase 2: Bounded measurement campaign [COMPLETED]

**Goal**: Determine, within a hard 45-minute wall-clock ceiling, whether the **default-seed** Z3
work quantity for each of the two formulas is stable across repeated draws — and capture the
default-seed rlimit and wall-time range needed to size budgets under Route A.

**Why 3 draws per test and not 20**: repeated draws of the *same* configuration measure host
scheduling variance, not Z3 variance. The Z3 question ("is the work quantity fixed?") is answered
by whether the rlimit values agree, which 3 draws answer as well as 20 — and disagreement, if it
appears, appears immediately. The cross-seed sweep the research proposed characterizes a
distribution the test never samples (production has no pinned seed), so it is deliberately not
run here. Cost at measured rates: `all_future_neg` ~30-55s x3 ~= 2.5 min; `or_diamond_prev`
~85s x3 ~= 4.5 min; ~7 min expected, ~30 min at the per-draw ceilings, comfortably inside 45.

**Tasks**:

- [x] Create the measurement log
      `specs/167_flaky_testmixedformulas_failures/measurements/01_default-seed-probe.md` and
      append to it after **every** draw, before starting the next one. A campaign that is
      interrupted must leave behind everything it already learned.
- [x] Record ambient conditions before the first draw and after the last:
      `timeout 10 uptime` (load average), `nproc`, `z3.get_version_string()`, `PYTHONHASHSEED`.
- [x] **Draws 1-3**: `and(neg(A), next(B))` (`test_mixed_and_all_future_neg`'s formula), default
      seed, probe `--timeout-ms 180000`, each invocation prefixed
      `timeout 240` — foreground, one at a time. Record wall time, decided/undecided, rlimit.
- [x] **Draws 4-6**: `or(diamond(A), prev(B))` (`test_mixed_or_diamond_prev`'s formula), default
      seed, probe `--timeout-ms 240000`, each invocation prefixed `timeout 300` — foreground,
      one at a time. Record the same fields.
- [x] **Step 5 — forced repro (cheap, ~seconds)**: one probe invocation per formula at a
      deliberately tiny `--timeout-ms` (e.g. 2000), prefixed `timeout 60`, to capture the exact
      failure text a real budget overrun produces. Then one `pytest` invocation of a scratch copy
      of one target test with its `timeout_ms` temporarily lowered, prefixed `timeout 120`, to
      capture the **pytest-level** failure text (the string a JUnit `<failure>` element would
      carry). Paste both verbatim into the log. This is the string Route B's classifier branch
      must match; it must be copied, never retyped from memory. Revert the scratch edit
      immediately and confirm with `git diff --stat`.
- [x] **Step 6 — bounded, non-blocking CI history query**: one
      `timeout 60 gh run list --workflow=... --limit 50` style query looking for prior **serial**
      failures of either test. If `gh` is unavailable, unauthenticated, or the query exceeds 60s,
      record "CI history unavailable — not obtained" in the log and proceed. **This must not
      block the phase under any circumstance.**
- [x] **Conditional (only if rlimit disagrees across draws of the same formula)**: SKIPPED --
      rlimit agreed exactly (0% spread) across all 3 draws for both formulas, so the trigger
      condition never fired. 2 additional
      draws of the disagreeing formula with `PYTHONHASHSEED=0` fixed, same per-draw `timeout`, to
      test whether construction-order randomization rather than Z3 explains the spread. Skip
      entirely if rlimit agrees.
- [x] Enforce the ceiling: if 45 minutes of wall clock elapse, stop, write a "CEILING REACHED —
      campaign partial" line naming which draws completed, and proceed to Phase 3 with what
      exists.

**Timing**: 0.75 hours (hard ceiling 45 minutes of campaign wall clock plus logging)

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: `per-substep` — commit the measurement log after each draw group, so an
interrupted campaign is not lost.

**Scope Hypothesis**: This phase asserts 3 draws per formula suffice to answer the determinism
question, and that expected campaign cost is ~7 minutes against a 45-minute ceiling, based on the
research's measured 27-53s (`all_future_neg`) and 84-87s (`or_diamond_prev`) ranges. Confirm at
implementation time from draws 1-2: if either formula's first two draws exceed 150s wall each, the
cost model is wrong — record that, and reduce `or_diamond_prev` to 2 draws to stay inside the
ceiling rather than dropping the determinism check for `all_future_neg`.

**Files to modify**:

- `specs/167_flaky_testmixedformulas_failures/measurements/01_default-seed-probe.md` - new
  measurement log (the phase's only durable output)

**Verification**:

- The log contains, for each formula, either 3 completed draws or an explicit ceiling/timeout
  record for each missing one.
- Every draw record carries wall time, decided/undecided, rlimit, and `PYTHONHASHSEED`.
- Both verbatim failure texts from step 5 are present.
- `git diff --stat` shows no residual scratch edit to
  `oracle/bimodal_logic/tests/test_oracle_interface.py`.

---

### Phase 3: Route decision gate [COMPLETED]

**Goal**: Read Phase 2's log and commit, in writing, to Route A or Route B — with the numbers that
decided it.

**Tasks**:

- [x] Compute per-formula rlimit spread across the completed default-seed draws.
- [x] Apply the decision rule and record it explicitly in the measurement log:
  - **Route A** if, for **both** formulas, the rlimit values across draws agree within **5%** of
    their minimum. Rationale: identical work quantity under varying wall clock is the direct
    demonstration that the pass/fail boundary is measured in the wrong unit, and that an
    rlimit-denominated bound is deterministic.
  - **Route B** if either formula's rlimit spread exceeds 5% *after* the `PYTHONHASHSEED=0`
    control (where that control was run). The work quantity is then genuinely nondeterministic,
    no budget in either unit makes the outcome deterministic, and the honest answer is the
    documented `unstable` fallback.
  - **Route B** also if Phase 2 hit its ceiling with fewer than 2 completed draws for either
    formula — an undersampled campaign cannot support a determinism claim, and asserting one
    anyway would be exactly the unmeasured move this task forbids.
- [x] Write the decision, the deciding numbers, and the excluded route into the log under a
      "ROUTE DECISION" heading.
- [x] Update this plan file: mark the not-taken route's phase(s) `[COMPLETED WITH EXCLUSIONS]` and
      add a `#### Reasoned Exclusions` subsection under each, naming the Phase 3 measurement.

**Timing**: 0.25 hours

**Depends on**: 2

**Verification Tier**: prose

**Verification**:

- The measurement log has a "ROUTE DECISION" section naming exactly one route, the rule applied,
  and the numeric basis.
- The not-taken route's phase heading carries `[COMPLETED WITH EXCLUSIONS]` with a populated
  `#### Reasoned Exclusions` record — never `[COMPLETED]`, never `[DESCOPED]`.

---

### Phase 4: Route A — Plumb `max_rlimit` through the oracle provider [IN PROGRESS]

**Goal**: `Z3OracleProvider.find_countermodel()` accepts an optional, deterministic
resource-unit budget and reports honestly when it fires — closing the one gap between
`ExampleSettings`' already-plumbed `max_rlimit` and the oracle path that never sets it.

**Tasks** (TDD — tests first):

- [ ] Write RED tests in `oracle/bimodal_logic/tests/test_oracle_interface.py` (or a focused
      sibling module, using **atemporal** formulas only so the new tests are fast and unmarked):
  - `find_countermodel(..., max_rlimit=None)` (the default) produces a settings dict with **no**
    `max_rlimit` key — behavior is byte-for-byte unchanged for every existing caller.
  - `find_countermodel(..., max_rlimit=<tiny>)` raises `OracleTimeoutError` on a formula that
    otherwise decides — confirming the budget actually reaches `Z3SolverAdapter.set_rlimit()`.
  - The raised error's `context` dict carries `max_rlimit`, and its message names **both**
    budgets rather than asserting the wall-clock one fired.
- [ ] Add an optional `max_rlimit: int | None = None` parameter to `find_countermodel()` and
      insert `'max_rlimit': max_rlimit` into the settings dict **only when truthy**, mirroring
      `ModelDefaults.solve()`'s own default-off `if max_rlimit:` guard.
- [ ] Add an optional `max_rlimit: int | None = None` parameter to `OracleTimeoutError.__init__`.
      When present: include it in `self.context`, and phrase the message as budget exhaustion
      naming both budgets (an rlimit-exhausted UNKNOWN is classified `is_timeout=True` identically
      to a wall-clock timeout by `ModelDefaults.solve()`, so the code genuinely cannot tell which
      fired — the message must not pretend it can). When absent, the existing message is
      unchanged.
- [ ] Confirm the two existing construction sites in
      `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` still work unchanged (the new
      parameter is optional and keyword-only in effect).
- [ ] Update `find_countermodel()`'s docstring: document `max_rlimit` as the load-independent
      complement to `timeout_ms`, and cross-reference `TESTING_GUIDE.md` section 8.6.
- [ ] Verify: `timeout 600 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m "not slow and not unstable and not xdist_serial" -q`

**Timing**: 1.0 hour

**Depends on**: 3

**Verification Tier**: interface — this changes two public signatures
(`find_countermodel`, `OracleTimeoutError.__init__`) with call sites spanning
`oracle/bimodal_logic/provider.py` and `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.

**Scope Hypothesis**: This phase asserts the change is confined to the three files listed below
plus one test module, and that `OracleTimeoutError` has exactly two construction sites outside
`provider.py`. Confirm at implementation time with
`grep -rn "OracleTimeoutError(" --include=*.py oracle code` before editing; if the grep finds
additional sites, enumerate them in the phase handoff and widen the phase's file set rather than
proceeding on the plan's count.

**Files to modify**:

- `oracle/bimodal_logic/provider.py` - optional `max_rlimit` parameter, conditional settings key,
  pass-through to the raise site, docstring
- `oracle/bimodal_logic/errors.py` - optional `max_rlimit` parameter, `context` entry, honest
  dual-budget message
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - new fast, atemporal RED->GREEN tests

**Verification**:

- New tests pass; the whole non-slow, non-serial oracle test selection still passes.
- `git diff` on `errors.py` shows the no-`max_rlimit` message text is byte-identical to before.
- No existing caller of `find_countermodel()` was edited to pass the new parameter in this phase.

---

### Phase 5: Route A — Apply calibrated budgets and record the fourth investigation [NOT STARTED]

**Goal**: Both target tests bound their solve by a **deterministic** rlimit ceiling with generous
headroom, backed by a wall-clock budget wide enough that it is not the operative bound — and their
docstrings record this investigation the way the three prior ones were recorded.

**Tasks**:

- [ ] Set each test's `max_rlimit` to **>= 3x** its Phase 2 measured default-seed rlimit. Not
      measured-plus-margin: `TESTING_GUIDE.md` section 8.6's standing instruction is "Set budgets
      generously, not tightly", and the sibling recalibrations in this tree used ~2.07x-2.3x of a
      *wall-clock* worst; an rlimit bound is deterministic, so its headroom exists to absorb
      future genuine cost growth, not run-to-run noise.
- [ ] Widen each test's `timeout_ms` so wall clock is no longer the operative bound. Prefer the
      file's own existing house constant `TEMPORAL_SOLVE_TIMEOUT_MS = 180000` (both formulas have
      `temporal_depth > 0`, which is exactly what that constant exists for, and it is already
      more generous than both tests' current 150000/60000) over a fresh bespoke number. Where a
      Phase 2 draw makes 180000 insufficient headroom, state the measured basis for the larger
      figure inline.
- [ ] Rewrite both docstrings to record: the fourth investigation and its date; the default-seed
      rlimit measured and the draw count; the wall-clock range observed; the Z3 version the rlimit
      figure is valid for and the explicit statement that a Z3 upgrade requires recalibration; and
      why the pass/fail boundary moved from a wall-clock unit to a resource unit. **Preserve the
      existing docstring history** — `TESTING_GUIDE.md` section 8.9 is explicit that "the history
      of what was tried and what finally worked is worth more than a clean diff". Append; do not
      replace.
- [ ] Explicitly resolve `test_mixed_and_all_future_neg`'s standing watch item ("If this test ever
      fails SERIALLY, treat that as new measurement contradicting the 60000ms figure and
      recalibrate from a fresh uncensored probe -- do not tweak the budget reactively") — state in
      the docstring that the recalibration happened, from which probe, and that the 60000ms figure
      is superseded.
- [ ] Note explicitly that the cross-seed 80.6s/107.4s draws recorded in the prior docstring were
      measured under **pinned non-default seeds** and do not describe the production draw, so the
      new budget is not "ignoring" them.
- [ ] Keep both `@pytest.mark.xdist_serial` markers. Add a one-line docstring note that the marker
      remains for the `-n 6` contention mechanism, which is separate from the budget-unit change.
- [ ] Verify: `timeout 900 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_oracle_interface.py -m xdist_serial -v`

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: local — edits confined to two test functions in one module, with no
externally visible signature change. The behavioral check is the full run in Phase 7.

**Scope Hypothesis**: This phase asserts `TEMPORAL_SOLVE_TIMEOUT_MS = 180000` provides adequate
wall-clock headroom for both formulas. Confirm at implementation time against Phase 2's measured
wall-time range: require >= 2x the slowest completed draw. If 180000 does not clear 2x, record the
measured basis and set a larger explicit value rather than adopting the constant for tidiness.

**Files to modify**:

- `oracle/bimodal_logic/tests/test_oracle_interface.py` - `test_mixed_or_diamond_prev` and
  `test_mixed_and_all_future_neg`: budgets and docstrings

**Verification**:

- Both tests pass in a serial run.
- Both docstrings name a measured rlimit, a draw count, a Z3 version, and a recalibration trigger.
- Prior docstring history is still present (verify by reading the diff, not by re-running).
- Both `xdist_serial` markers are intact.

---

### Phase 6: Route B — `unstable` marking on the existing machinery [COMPLETED WITH EXCLUSIONS]

**Goal**: If Phase 3 selects Route B, both tests become documented, watched, non-gating
instabilities using the machinery that already exists — with the classifier actually able to
recognize their failure signature, which a naive marking would not achieve.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| All of Phase 6 (Route B: `unstable` marking, classifier branch, TESTING_GUIDE.md 8.9 entry) | Phase 3's decision gate selected Route A, not Route B. Route B is defined as executing only "if Phase 3 selects Route B" — it did not. | `specs/167_flaky_testmixedformulas_failures/measurements/01_default-seed-probe.md`'s "ROUTE DECISION" section: both target formulas' rlimit values are bit-identical (0% spread) across 3 default-seed draws each, well under the 5% Route A/B threshold, with no ceiling event and no `<2`-draws shortfall -- neither Route B trigger condition applies. |

This phase's tasks (classifier constants, `classify()` branch, `unstable` markers,
`code/tests/ci/test_unstable_watch_classifier.py` tests, `TESTING_GUIDE.md` 8.9 update) were not
executed. Route A (Phases 4-5) is executed instead. No file listed in this phase's "Files to
modify" was touched.

**Tasks** (TDD — classifier tests first):

- [ ] **The critical correction**: do **not** simply add entries to
      `MAX_TIME_BY_NODEID_FRAGMENT`. That path additionally requires
      `FAILURE_SIGNATURE = "Test failed for example:"` to appear in the failure text; these tests
      fail with an uncaught `OracleTimeoutError`, whose text does not contain that string, so
      such entries would classify every real failure as `NEW` and fail the watch job. The module's
      own comment prescribes the right shape: "A test whose TIMING signature is NOT duration-based
      … gets its own dedicated branch in `classify()` instead of an entry here."
- [ ] Write RED tests in `code/tests/ci/test_unstable_watch_classifier.py`: a failure on either
      target node id carrying the verbatim `OracleTimeoutError` text captured in Phase 2 step 5
      classifies `TIMING`; a failure on the same node id with a *different* message (e.g. an
      assertion that the countermodel was not a dict) classifies `NEW`; the existing `BM_CM_1` and
      gating-floor branches are unaffected.
- [ ] Add `ORACLE_TIMEOUT_NODEID_FRAGMENTS` and `ORACLE_TIMEOUT_SIGNATURE` constants plus a
      dedicated `classify()` branch to `.github/scripts/unstable_watch_classify.py`, following the
      `GATING_FLOOR_NODEID_FRAGMENT`/`GATING_FLOOR_SIGNATURE` pattern verbatim. Include the same
      style of negative laundering guard: a failure on these node ids that is *not* the timeout
      signature must return `NEW`.
- [ ] Extend `currently_unstable` in the promotion-notice computation so a `READY TO PROMOTE`
      notice names the newly marked tests (the module already unions
      `MAX_TIME_BY_NODEID_FRAGMENT.keys()` with `{GATING_FLOOR_NODEID_FRAGMENT}` for exactly this
      reason; add the new fragments to that union).
- [ ] Add `@pytest.mark.unstable` to both tests, **keeping** `@pytest.mark.xdist_serial`, and write
      the mandatory `TESTING_GUIDE.md` section 8.9 entry-criteria comment at the marker site, with
      all four items as separately identifiable records: (1) what fails and why, with Phase 2's
      concrete numbers; (2) demonstrably non-semantic — the same countermodel is found on every
      decided draw across four investigations; (3) genuine fixes attempted and their measured
      failure — the three prior budget/marker rounds, plus this task's rlimit-determinism probe
      and exactly what it showed; (4) a written, concrete exit criterion (the section's default:
      20 consecutive zero-failure `unstable-watch` runs, or a demonstrated encoding fix across
      >= 20 seeds).
- [ ] Update `TESTING_GUIDE.md` section 8.9's "Currently marked" list with both tests and a
      pointer to their entry-criteria comment.
- [ ] **Verify, do not modify**, that `oracle/run-oracle-suite.sh` already carries
      `and not unstable` on **both** passes. It does. Do not touch that file. Do not touch
      `.github/workflows/unstable-watch.yml` — the classifier lives in the extracted module by
      design.
- [ ] Note in the entry-criteria comment that `unstable-watch.yml`'s oracle step gains ~4 minutes
      of runtime from these two solves (non-gating, nightly).
- [ ] Verify: `timeout 300 env PYTHONPATH=code/src pytest code/tests/ci/ -v`

**Timing**: 1.25 hours

**Depends on**: 3

**Verification Tier**: interface — adds module-level constants and a `classify()` branch
consumed across `.github/scripts/unstable_watch_classify.py` and
`code/tests/ci/test_unstable_watch_classifier.py`.

**Scope Hypothesis**: This phase asserts the change set is the four files listed below and that
`oracle/run-oracle-suite.sh` needs no edit. Confirm at implementation time with
`grep -n "not unstable" oracle/run-oracle-suite.sh` (expect both pass 1 and pass 2 to match) and by
running `code/tests/ci/test_unstable_deselection_wiring.py`; if either shows a gap, record it and
widen the file set rather than assuming.

**Files to modify**:

- `.github/scripts/unstable_watch_classify.py` - new node-id/signature constants, dedicated
  `classify()` branch, `currently_unstable` union extension
- `code/tests/ci/test_unstable_watch_classifier.py` - new RED->GREEN classifier tests
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - `unstable` markers plus the four-item
  entry-criteria comment
- `code/docs/core/TESTING_GUIDE.md` - section 8.9 "Currently marked" list

**Verification**:

- `code/tests/ci/` passes in full, including the pre-existing deselection-wiring and classifier
  tests.
- A simulated JUnit failure carrying the Phase 2 verbatim timeout text classifies `TIMING`; a
  different failure on the same node id classifies `NEW`.
- `git diff --stat` shows **no** change to `oracle/run-oracle-suite.sh` or
  `.github/workflows/unstable-watch.yml`.

---

### Phase 7: Final verification and handoff [NOT STARTED]

**Goal**: The full gate set passes, the recently-landed `unstable` machinery is provably intact,
and the outcome — including an honest Route B outcome — is recorded.

**Tasks**:

- [ ] `timeout 900 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_oracle_interface.py -m "xdist_serial and not unstable" -v`
      (Route A: both target tests run and pass. Route B: they are deselected — confirm that is
      what happened and that the remaining serial tests still pass.)
- [ ] Route B only: `timeout 900 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable -v`
      — confirm the watch selection picks up both tests.
- [ ] `timeout 600 env PYTHONPATH=code/src pytest code/tests/ci/ -v` — the CI-contract guards
      (`test_unstable_deselection_wiring.py`, `test_unstable_watch_classifier.py`,
      `test_timing_marker_coverage.py`, `test_example_budget_floor.py`, `test_workflow_parity.py`)
      all pass.
- [ ] `timeout 900 env PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m "not slow and not xdist_serial and not unstable" -q`
      — the parallel-pass selection is unregressed.
- [ ] Confirm no regression to protected recent work: `git diff --stat` against the task's base
      shows no change to `oracle/run-oracle-suite.sh`, and
      `grep -c "not unstable" oracle/run-oracle-suite.sh` still finds the filter on both passes.
- [ ] Write the implementation summary at
      `specs/167_flaky_testmixedformulas_failures/summaries/01_deterministic-mixed-formula-budgets-summary.md`,
      stating the route taken, the deciding measurement, and — under Route B — an explicit
      statement that full determinism was **not** achieved, why the measurement ruled it out, and
      what the exit criterion is.

**Timing**: 0.5 hours

**Depends on**: 5, 6

**Verification Tier**: full

**Files to modify**:

- `specs/167_flaky_testmixedformulas_failures/summaries/01_deterministic-mixed-formula-budgets-summary.md` - new summary

**Verification**:

- All four pytest invocations above exit 0 (or, for the Route B watch selection, collect and pass
  the expected two tests).
- `oracle/run-oracle-suite.sh` is unmodified.
- The summary names the route, the numbers, and — under Route B — the honest non-determinism
  admission.

---

## Testing & Validation

- [ ] TDD order observed in every code-touching phase: RED test written and seen to fail before
      the implementation that makes it pass (Phases 1, 4, 6).
- [ ] New probe-harness tests use atemporal formulas only, so they add no slow tests to the gating
      suite and carry no `slow`/`xdist_serial`/`unstable` marker.
- [ ] `oracle/bimodal_logic/tests/test_oracle_interface.py` passes in its serial selection.
- [ ] `code/tests/ci/` passes in full — in particular the deselection-wiring and classifier guards.
- [ ] The oracle parallel-pass selection is unregressed.
- [ ] Under Route A, `find_countermodel()` behavior is byte-for-byte unchanged for callers that do
      not pass `max_rlimit` (pinned by a dedicated test).
- [ ] Under Route B, a simulated `OracleTimeoutError`-shaped JUnit failure classifies `TIMING` and
      a differently-shaped failure on the same node id classifies `NEW`.

## Artifacts & Outputs

- `specs/167_flaky_testmixedformulas_failures/measurements/01_default-seed-probe.md` — the
  measurement log and the recorded ROUTE DECISION
- `oracle/probe_solve_cost.py` — reusable foreground probe CLI
- `oracle/bimodal_logic/tests/test_probe_solve_cost.py` — probe harness unit tests
- Route A: modified `oracle/bimodal_logic/provider.py`, `oracle/bimodal_logic/errors.py`, and the
  two recalibrated tests with recorded docstrings
- Route B: modified `.github/scripts/unstable_watch_classify.py`,
  `code/tests/ci/test_unstable_watch_classifier.py`, the two marked tests with entry-criteria
  comments, and `code/docs/core/TESTING_GUIDE.md` section 8.9
- `specs/167_flaky_testmixedformulas_failures/summaries/01_deterministic-mixed-formula-budgets-summary.md`

## Rollback/Contingency

Every phase commits separately, so rollback is per-phase `git revert`. Specific contingencies:

- **Phase 1 probe cannot read rlimit at all** (statistics unreachable through every access path):
  Phase 2's determinism question becomes unanswerable, Phase 3's third clause fires, and the plan
  routes to Route B with "rlimit unobservable" as the recorded reason. This is a legitimate
  outcome, not a plan failure.
- **Phase 2 exceeds its ceiling with <2 draws per formula**: Phase 3's third clause fires; Route B.
- **Phase 4 breaks an existing `OracleTimeoutError` caller**: revert Phase 4, keep the new
  parameter optional-only with no message change, and re-attempt with a narrower edit; the
  behavior-unchanged-by-default test is the tripwire for this.
- **Phase 5's recalibrated budget still fails in Phase 7's serial run**: do **not** widen it
  reactively — that is the prohibited move. Revert Phase 5 and route to Route B, recording the
  Phase 7 failure as the measurement that closed Route A.
- **Anything appears to require editing `oracle/run-oracle-suite.sh` or
  `.github/workflows/unstable-watch.yml`**: stop and re-read Process Constraint 5. Both are
  recently-landed protected work; the classifier module is the sanctioned extension point.
