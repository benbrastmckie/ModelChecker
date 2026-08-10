# Implementation Plan: Oracle Full-Scan Self-Consistency

- **Task**: 133 - fix_oracle_self_consistency_disagreements
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours attended (plus up to ~3.5 hours unattended background wall clock)
- **Dependencies**: None
- **Research Inputs**: `specs/133_fix_oracle_self_consistency_disagreements/reports/01_oracle-self-consistency.md`
- **Artifacts**: plans/01_oracle-self-consistency.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/plan-format-enforcement.md`
  - `.claude/rules/state-management.md`
- **Type**: python

## Overview

`test_complexity_5_scan_self_consistent` (`oracle/bimodal_logic/tests/test_cross_oracle_differential.py:1365`)
is not failing because the Z3 oracle disagrees with itself. It fails because the oracle's default
5000 ms solve budget sits *inside* the solve-time band of at least one formula in the 274-formula
complexity<=5 enumeration, and a blown budget is reported as "no countermodel" rather than as an
error — so a boundary-straddling formula silently inverts its verdict instead of failing loudly.
This plan widens that one test's solve budget to a generous, principled value; records the
structural correction of a stale "Category C contention flake" label attached to this test; and
verifies the result with a full two-pass oracle-suite run so a downstream regression-baseline task
can proceed. Definition of done: the widened test passes in isolation, the full two-pass suite
returns exit 0 on both passes, and the corrective note is in place.

### Research Integration

The research report is authoritative and its conclusions are not re-derived here. Load-bearing
findings carried into this plan:

- **Mechanism is settled by direct observation.** An instrumented read-only re-run of the full
  scan produced one disagreement on `untl(bot, box(p))`, and that disagreement had a recorded
  timeout on exactly one side: solve A returned a model at `z3_model_runtime` 4.7796s
  (`structure.timeout=false`), solve B hit the budget at 5.0003s (`structure.timeout=true`) and
  its timeout was reported as `UNSAT`. Same formula, same settings (`N=2`, `M=3`,
  `temporal_depth=1`), same 5.0s `max_time`.
- **Root cause of the conflation** is `Z3OracleProvider.find_countermodel()` at
  `oracle/bimodal_logic/provider.py:255`, which returns `None` for both `structure.timeout` and a
  genuine UNSAT. Both consumers in the test — the local `ref_fn` and
  `_run_differential_comparison` — read only that ambiguous `None`/non-`None` signal.
- **The test solves every formula twice** (`ref_fn` at line 1370, then an independent
  `find_countermodel` call inside `_run_differential_comparison` at line 363), so a budget-boundary
  formula can land on opposite sides of the cliff within a single test run. Any budget change must
  apply to *both* solves or it reintroduces the asymmetry it is meant to remove.

### Prior Plan Reference

No prior plan for this task. `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`
is referenced only as an *edit target* in Phase 1 (it carries the stale misclassification), not as
a template or a source of approach.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no ROADMAP.md was consulted.

### Sample-count honesty (carry this through the whole plan)

The instrumented run behind this diagnosis is **one sample**. It produced 1 disagreement, which
happens to match the pre-refactor baseline's reported count rather than HEAD's previously reported
count of 3. The *mechanism* is settled by that run's own recorded timeout. The *count distribution*
is not settled and this plan does not claim otherwise. Both the 1-count and 3-count observations
are consistent with the same mechanism: how many of 274 formulas land near the budget cliff on a
given run is a function of machine load, not of the code under test. No phase in this plan asserts
count stability, and no phase's success criterion is "the count is reliably N".

## Goals & Non-Goals

**Goals**:

- Give `test_complexity_5_scan_self_consistent` a solve budget with headroom far beyond the
  observed 4.78-5.00s boundary, applied identically to both of its per-formula solves.
- Leave every other call site of the two shared differential helpers behaviourally unchanged, so
  this change cannot perturb the currently-green remainder of the suite.
- Structurally retract the "Category C contention flake" label wrongly attached to this test in a
  prior plan document, so that document stops being a source of the stale claim.
- Produce a clean, verdict-bearing full two-pass oracle-suite result that a downstream
  regression-baseline task can act on.

**Non-Goals**:

- **Hardening `find_countermodel`'s return contract.** Making SAT/UNSAT/TIMEOUT explicit at the
  oracle's public API boundary is the real fix for the defect *class*, and the research recommends
  it — as its own task. It touches `ref_fn`, `_run_differential_comparison`, the
  `_KNOWN_INVALID_JSON` xfail block (`test_cross_oracle_differential.py:770-781`), and
  `validate_self()` (`provider.py:277-295`), which has the identical `None`-collapsing pattern.
  Doing it here would convert a ~1-hour edit into a cross-cutting API change with an unbounded
  blast radius across `oracle/bimodal_logic/tests/`. See "Handoff to the contract-hardening
  follow-up" below.
- **Repeat sampling to establish count stability.** 3-5 repeats of the instrumented scan would
  cost roughly **1.5-2.5 hours of unattended wall clock** and would only sharpen confidence about
  the count *distribution* — it would not change the diagnosis. This plan deliberately does not
  include it. If a downstream consumer wants a stability estimate, that is a separate, explicitly
  budgeted piece of work.
- Fixing, re-marking, or suppressing any other test in the oracle suite.
- Touching `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`. Another
  session holds a stale-heartbeat lock on it with uncommitted changes. Out of scope entirely.
- Any `git checkout`/`git restore`/`git stash`/`git reset` operation on the working tree, which
  already carries unrelated pre-existing modifications.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Widening the budget inflates the test's ~31 min runtime, because an unknown number of solves currently hit the 5s ceiling silently and would now run to the new ceiling. A formula that times out on *both* solves reports UNSAT twice, counts as an agreement, and is therefore invisible in the current disagreement count. | H | M | Phase 2 runs the widened test alone in the background and records wall clock as a first-class output. A hard abort rule is stated (Phase 2, step 5): if the run exceeds 2h30m, kill it, record the partial evidence, and reduce the budget rather than waiting it out. |
| The chosen budget is still too tight and the test fails again. | M | L | Phase 3 states the escalation ladder explicitly and forbids blind re-widening: the documented next levers are `@pytest.mark.xdist_serial` on `TestFullScanReport`, then the contract-hardening follow-up. |
| Threading a `timeout_ms` parameter through the shared helpers perturbs the eight other call sites. | H | L | The new parameter defaults to `None`, and `None` means "call `find_countermodel` exactly as before, with no `timeout_ms` keyword". Only the self-consistency test opts in. Phase 1's smoke check covers the other consumers of both helpers. |
| Only one of the two per-formula solves gets the widened budget, recreating the asymmetry. | H | L | Phase 1 changes `ref_fn` *and* passes `timeout_ms` into `_generate_differential_report`; Phase 1's verification step greps for both. |
| The full-suite run in Phase 3 fails on some *other* test due to machine load. | M | M | Phase 3's success criterion is verdict-based and scoped: a non-`test_complexity_5_scan_self_consistent` failure is reported, not fixed, and is called out as out of scope for this task. |
| A long-running command is cut off by the 10-minute foreground Bash ceiling and is misread as a failure. | M | H if ignored | Every phase that runs pytest against this test or the full suite MUST use `run_in_background: true`. A cut-off foreground command is a harness limit, not a test failure. |

## Environment contract (applies to every command in every phase)

These are verified constraints, not suggestions:

- **Every python/pytest invocation MUST be wrapped in `nix develop --command ...`.**
  `pytest-xdist` is absent from the bare interactive python but present and already realized in the
  devShell (no rebuild needed). The devShell supplies pytest 9.0.3 and z3.
- **`PYTHONPATH=code/src` is required.**
- **`run_in_background: true` is mandatory** for Phase 2 and Phase 3 commands. The self-consistency
  test alone runs ~31 minutes at the current budget; the full two-pass suite runs ~52 minutes. Both
  exceed the 10-minute foreground Bash ceiling.
- The two-pass runner is `oracle/run-oracle-suite.sh`: pass 1 is `pytest oracle -n 6 -m "not
  xdist_serial"`, pass 2 is `pytest oracle -m "xdist_serial"`. It assumes it is already inside the
  devShell and does not invoke `nix develop` itself.
- Before launching a long timing-sensitive run, check for competing pytest processes
  (`ps aux | grep pytest`) per `code/docs/core/TESTING_GUIDE.md` section 8.6 — concurrent sessions
  measurably contend and a long suite can be killed outright by resource pressure.

## Budget decision: named constant at 60000 ms

This is the recommendation, not a menu.

**Use a named module-level constant, not a bare number.** The sibling pattern is already
established in this tree: `oracle/bimodal_logic/tests/test_oracle_interface.py:115-116` defines
`TEMPORAL_SOLVE_TIMEOUT_MS = 180000` and `ATEMPORAL_SOLVE_TIMEOUT_MS = 10000`, each carrying a
comment that records the measured solve band and cites
`code/docs/core/TESTING_GUIDE.md` section 8.6 as the reason for sizing generously. Follow it.

**The 5.0s budget is inherited, not local.** `test_cross_oracle_differential.py` never passes
`timeout_ms` anywhere — `grep -n "timeout_ms" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
returns nothing. Every solve in that file silently inherits `find_countermodel`'s
`timeout_ms: int = 5000` default (`provider.py:173`). So the widening cannot be a one-line edit at
the test: the value has to be threaded through `_generate_differential_report` and
`_run_differential_comparison`, which is why Phase 1 touches three functions rather than one.

**Value: 60000 ms (60s), a 12x margin over the 5.0s cliff.** Justification against
`code/docs/core/TESTING_GUIDE.md` section 8.6:

- Section 8.6 records a ~20x spread (0.69s, 1.37s, 1.85s, 1.98s, 15.08s) for a single *unchanged*
  formula, attributed to machine load rather than test order.
- Section 8.6 also records a concrete failed margin: "An observed ~1.7s solve was given a 10s
  budget — an ~6x margin — and still failed at 10.11s call time inside a full-suite run." A 6x
  margin is documented as insufficient. 30s here would be exactly 6x and would be repeating that
  mistake.
- The observed solve band for the offending formula is 4.78-5.00s, and 5.00s is a *censored*
  observation — we know the solve exceeded the budget, not how long it actually needed. Sizing at
  "measured plus a little" is precisely the error section 8.6 warns against, and precisely the
  error that produced this failure.
- 12x sits above the documented-insufficient 6x and near the documented ~20x spread, while keeping
  the worst-case runtime blow-up bounded (see the Phase 2 abort rule). Going to 100s+ would track
  the 20x spread more literally but multiplies the unbounded-runtime risk on a test that already
  takes ~31 minutes.

**Do not also add `@pytest.mark.xdist_serial` in this task.** Note that `TestFullScanReport` is
marked `@pytest.mark.slow` but *not* `xdist_serial`, so it currently runs inside pass 1 under
six-way parallelism. That looks like an omission, but the marker's own registered criterion
(`oracle/conftest.py`, `pytest_configure`) is "tests whose Z3 solve budget has under ~2x
headroom". At 5000 ms this test had ~4% headroom and qualified; at 60000 ms it has 12x headroom and
does not. Widening the budget removes it from the marker's stated scope. Adding the marker anyway
would move ~31 minutes of work from the parallel pass into the serial pass for no gain by the
runner's own criterion. Keep it as an escalation lever (Phase 3), not a default.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential.

---

### Phase 1: Widen the scan's solve budget and retract the stale classification [COMPLETED]

**Goal**: The self-consistency scan solves every formula twice under a 60000 ms budget instead of
the inherited 5000 ms default, with no behavioural change at any other call site; and the prior
plan document that carries the false "Category C contention flake" label for this test is
corrected in place.

**Tasks**:

- [x] Add a module-level constant to `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`,
      placed near the top of the file alongside the other module-level definitions:
      `SELF_SCAN_SOLVE_TIMEOUT_MS = 60000`. Give it a comment in the style of
      `test_oracle_interface.py:111-116` that records the measured band (one solve returned a model
      at 4.7796s while an independent solve of the same formula hit the budget at 5.0003s), states
      that a blown budget is reported as "no countermodel" rather than as an error, and cites
      `code/docs/core/TESTING_GUIDE.md` section 8.6 for the sizing rule.
      **This file lives outside `specs/`: cite the guide section as the durable anchor and do not
      reference any task number in the comment.**
- [x] Add an optional keyword parameter `timeout_ms: int | None = None` to
      `_run_differential_comparison` (`test_cross_oracle_differential.py:363`). Inside its existing
      `try` block, call `oracle.find_countermodel(formula_json)` unchanged when `timeout_ms is
      None`, and `oracle.find_countermodel(formula_json, timeout_ms=timeout_ms)` otherwise. Update
      the docstring's `Args:` section.
- [x] Add the same optional `timeout_ms: int | None = None` parameter to
      `_generate_differential_report` (`test_cross_oracle_differential.py:1176`) and pass it through
      to `_run_differential_comparison` at line 1209. Update its docstring's `Args:` section.
- [x] In `test_complexity_5_scan_self_consistent` (`test_cross_oracle_differential.py:1365`), change
      `ref_fn` to call `self.oracle.find_countermodel(f, timeout_ms=SELF_SCAN_SOLVE_TIMEOUT_MS)`
      **and** pass `timeout_ms=SELF_SCAN_SOLVE_TIMEOUT_MS` to the `_generate_differential_report`
      call. Both solves must carry the same budget; changing only one reintroduces the asymmetry
      this phase exists to remove.
- [x] Leave the eight other `_run_differential_comparison` call sites (lines 823, 838, 846, 855,
      861, 867, 874, 875) and the other `_generate_differential_report` call sites (1262, 1349,
      1393, 1501, 1517) untouched. The `None` default is what keeps them behaviourally identical.
- [x] Add a corrective note to
      `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`.
      Insert a clearly-marked block (e.g. a `> **Correction (2026-07-25)**:` blockquote)
      immediately after the bullet at lines 40-43, and a one-line pointer at the Non-Goals bullet
      at line 78. Do not delete the original text — retract it in place. The note must state: the
      source disposition document
      (`specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/oracle-suite-disposition.md`)
      lists 7 named tests under Category C and `test_complexity_5_scan_self_consistent` is not
      among them; the label was introduced by conflation with `test_all_sat_task_relation_ternary`,
      which genuinely is a Category C entry; and the actual diagnosis is in
      `specs/133_fix_oracle_self_consistency_disagreements/reports/01_oracle-self-consistency.md`.
      (This file is under `specs/**`, so task-number references are permitted here.)

**Timing**: 45 minutes.

**Depends on**: none

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — new `SELF_SCAN_SOLVE_TIMEOUT_MS`
  constant; optional `timeout_ms` parameter on two helpers; both solves in the self-consistency test
  opt in.
- `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md` —
  in-place corrective note at lines 40-43 and line 78.

**Verification**:

- Both solve paths carry the budget — this must return exactly three matches (the constant
  definition, the `ref_fn` call, the report call):
  ```bash
  grep -n "SELF_SCAN_SOLVE_TIMEOUT_MS" oracle/bimodal_logic/tests/test_cross_oracle_differential.py
  ```
- The fast consumers of both modified helpers still pass (foreground-safe; these classes are not
  marked `slow`):
  ```bash
  nix develop --command bash -c 'PYTHONPATH=code/src pytest \
    oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
    oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
    oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate -q'
  ```
  Success criterion: exit 0, zero failures. If this exceeds the 10-minute foreground ceiling,
  re-run it with `run_in_background: true` — a cut-off command is not a failure.
- The corrective note is present and points at the new report:
  ```bash
  grep -n "Correction" specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md
  ```

---

### Phase 2: Verify the widened test in isolation and record its wall clock [IN PROGRESS]

**Goal**: Establish that `test_complexity_5_scan_self_consistent` passes at the widened budget, and
capture how long it now takes — the runtime number is a first-class output of this phase, not a
side note, because it is the only evidence available about how many solves were previously hitting
the ceiling silently.

**Tasks**:

- [ ] Check for competing pytest processes before launching (`ps aux | grep pytest`), per
      `code/docs/core/TESTING_GUIDE.md` section 8.6.
- [ ] Launch the target test alone, **with `run_in_background: true`** — this is mandatory, the run
      is expected to exceed 30 minutes:
      ```bash
      nix develop --command bash -c 'PYTHONPATH=code/src pytest \
        "oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent" \
        -q --durations=0'
      ```
- [ ] Record the exit status, the reported test duration from `--durations=0`, and — on failure —
      the exact disagreement count from the assertion message.
- [ ] Compare the recorded duration against the ~31 minute baseline at the 5000 ms budget and note
      the delta. A materially larger number is the signal that many solves were previously being
      cut off at 5s and silently counted as agreements.
- [ ] **Abort rule**: if the background run exceeds **2 hours 30 minutes** of wall clock, stop it,
      record the partial evidence, and reduce `SELF_SCAN_SOLVE_TIMEOUT_MS` (30000 ms is the next
      step down) rather than waiting it out. Note in the summary that the reduction was forced by
      runtime, and that a reduced margin re-exposes the test to the same boundary mechanism.

**Timing**: 30 minutes attended; up to 2h30m unattended background wall clock.

**Depends on**: 1

**Files to modify**: none (verification only).

**Verification**:

- Success criterion: the command above exits 0 with `1 passed`.
- On failure at 60000 ms, do **not** re-widen blindly. Record the disagreement count and the
  durations, and carry the escalation ladder in Phase 3 forward.
- Explicit honesty requirement for the summary: a single green run demonstrates that the test
  passed once, under that run's machine load. It does not establish that the disagreement count is
  stably zero. State it that way.

---

### Phase 3: Full two-pass suite run and downstream exit verdict [NOT STARTED]

**Goal**: Produce the verdict a downstream regression-baseline task needs — a full two-pass oracle
suite result with this test included — and state precisely what that verdict does and does not
prove.

**Tasks**:

- [ ] Check for competing pytest processes (`ps aux | grep pytest`) before launching.
- [ ] Run the full two-pass suite, **with `run_in_background: true`** (expected ~52 minutes at the
      old budget, longer at the new one):
      ```bash
      nix develop --command bash oracle/run-oracle-suite.sh
      ```
- [ ] Record, from the script's own `== oracle suite summary ==` block: pass 1 status, pass 2
      status, and the overall exit code. Record total wall clock.
- [ ] Write the downstream verdict (see "Exit criteria" below) into the implementation summary,
      including the budget value that the green result rests on.
- [ ] If `test_complexity_5_scan_self_consistent` fails again at 60000 ms, apply the escalation
      ladder in order and do not skip steps: (1) add `@pytest.mark.xdist_serial` to
      `TestFullScanReport` so it runs in pass 2 with zero sibling workers — accepting that this
      moves ~31+ minutes from the parallel pass to the serial pass; (2) if it still fails serially,
      stop and hand off to the contract-hardening follow-up. Blind re-widening beyond 60000 ms is
      not on the ladder.
- [ ] If any test *other* than `test_complexity_5_scan_self_consistent` fails, report it with its
      node id and output and stop. Fixing it is out of scope for this task.

**Timing**: 30 minutes attended; ~1-1.5 hours unattended background wall clock.

**Depends on**: 2

**Files to modify**: none (verification only), unless the escalation ladder's step (1) is reached,
in which case `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` gains one marker.

**Verification**:

- Success criterion: `oracle/run-oracle-suite.sh` exits 0, and its summary block reports
  `pass 1 (parallel, -n 6, not xdist_serial): PASSED` and
  `pass 2 (serial, xdist_serial):             PASSED`.

## Exit criteria for the downstream regression-baseline task

State these verbatim in the implementation summary. A verdict beats an unconditional
zero-failure assertion, because the underlying variance makes an unconditional assertion
unsupportable from any number of runs this task can afford.

**Necessary and sufficient to unblock**: one complete `oracle/run-oracle-suite.sh` invocation in
which both passes report PASSED and the script exits 0, with the widened budget in place.

**What that green run proves**: at that moment, under that machine's load, the full oracle suite
had zero failures — including the test that was previously the suite's only failure.

**What it does not prove**: that the self-consistency scan's disagreement count is stably zero.
The count is load-dependent, this task takes one sample of it, and establishing a distribution
would cost 1.5-2.5 hours of additional unattended wall clock (see Non-Goals). The green result
rests on a 12x solve-budget margin, not on the elimination of the underlying mechanism — which is
`find_countermodel`'s `None` conflating timeout with UNSAT, still present at `provider.py:255`.

**Annotation the promoted baseline must carry**: record the budget value
(`SELF_SCAN_SOLVE_TIMEOUT_MS = 60000`) alongside the result, and record that a future failure of
`test_complexity_5_scan_self_consistent` specifically must be triaged as a budget-boundary event
first (`code/docs/core/TESTING_GUIDE.md` section 8.6), not as a semantic regression. Four
consecutive triage efforts in this line of work have each spent significant time re-discovering
that a timeout was being read as a semantic verdict.

## Handoff to the contract-hardening follow-up

Not implemented here. Recorded so the follow-up task does not restart from zero:

- **The change**: make `Z3OracleProvider.find_countermodel()` return three-valued information
  (SAT / UNSAT / TIMEOUT) instead of collapsing UNSAT and TIMEOUT to the same `None` at
  `oracle/bimodal_logic/provider.py:255`. `structure.timeout` is already `True` for any Z3
  `unknown` result (`code/src/model_checker/models/structure.py:210-260`), so the information
  exists at the point of collapse — it is discarded, not missing.
- **Known call sites that must change with it**: `ref_fn` and `_run_differential_comparison` in
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`; the `_KNOWN_INVALID_JSON` xfail
  block at `test_cross_oracle_differential.py:770-781`, which already names `provider.py:255`
  explicitly; and `validate_self()` at `provider.py:277-295`, which repeats the identical
  `None`-collapsing pattern.
- **Why it is a separate task**: it is an API-shape change to the oracle's public boundary that
  ripples across `oracle/bimodal_logic/tests/`, and it deserves its own scoped plan rather than
  arriving as a side effect of one test's budget fix.
- **Why it is worth doing**: it retires the recurring root cause rather than moving the wall-clock
  cliff to a new value. Widening a budget is a symptom patch; every formula whose true solve time
  sits near whatever budget is chosen remains exposed to the same silent verdict inversion.

## Testing & Validation

- [ ] `grep -n "SELF_SCAN_SOLVE_TIMEOUT_MS" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
      returns three matches (definition, `ref_fn` call, report call).
- [ ] Fast helper consumers pass:
      `nix develop --command bash -c 'PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate -q'`
      exits 0.
- [ ] The target test passes in isolation (background):
      `nix develop --command bash -c 'PYTHONPATH=code/src pytest "oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent" -q --durations=0'`
      exits 0 with `1 passed`.
- [ ] Full two-pass suite (background): `nix develop --command bash oracle/run-oracle-suite.sh`
      exits 0 with both passes PASSED.
- [ ] Wall-clock duration of the isolated run is recorded and compared against the ~31 minute
      baseline.
- [ ] The corrective note exists in
      `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`
      and cites `specs/133_fix_oracle_self_consistency_disagreements/reports/01_oracle-self-consistency.md`.

## Artifacts & Outputs

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — widened solve budget for the
  self-consistency scan via a named constant, threaded through both helpers.
- `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md` —
  in-place corrective note retracting the "Category C contention flake" label for this test.
- `specs/133_fix_oracle_self_consistency_disagreements/summaries/01_oracle-self-consistency-summary.md` —
  implementation summary carrying the recorded wall clock, the two-pass suite verdict, the exit
  criteria text above, and the contract-hardening handoff.

## Rollback/Contingency

- The code change is confined to one test file and is additive: an optional parameter defaulting to
  `None` plus one new constant. Reverting means removing the constant, removing the parameter from
  the two helper signatures and their pass-through, and dropping the two `timeout_ms=` arguments in
  `test_complexity_5_scan_self_consistent`. No other call site changes.
- If the runtime abort rule in Phase 2 fires, the fallback is a smaller budget (30000 ms), not a
  revert — reverting restores the known-failing 5000 ms state.
- The corrective note in the prior plan document is an insertion that preserves the original text;
  rolling it back means deleting the inserted block.
- **No destructive git operations.** The working tree carries unrelated pre-existing modifications
  and another session holds a lock on
  `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`. Do not run
  `git checkout`, `git restore`, `git stash`, or `git reset` to undo anything in this task; revert
  by editing the files listed above.
