# Execution Summary: Close the oracle gating conclusive-population diagnosis

- **Task**: 180 - Diagnose oracle conclusive-population shortfall (`unstable-watch`, 2026-08-27 -> 2026-09-01)
- **Plan**: `specs/180_diagnose_oracle_conclusive_population_shortfall/plans/01_close-diagnosis-record-gaps.md`
- **Status**: All 5 phases COMPLETED

## What this task did

The diagnosis itself was already complete and recorded in
`reports/01_gating-conclusive-shortfall-diagnosis.md` before this plan began. This plan closed the
task by (1) correcting a materially false claim and two recording gaps at the `unstable` marker's
own source-site entry-criteria block, (2) adding one pointer-shaped annotation to
TESTING_GUIDE.md 8.9 without rewriting its documented signature, (3) wiring one piece of opt-in
observability the diagnosis itself was blocked by, and (4) allocating the discriminating follow-up
as a real, specified task. No budget constant, no floor, no assertion, no marker, and no semantics
change was made anywhere in this plan.

## Phase-by-phase

**Phase 1** — Corrected criterion (3b)'s false "identical 96/103 conclusive, 7-timeout" claim with
the real six-run spread (96-98/103 conclusive, 5-7 timeouts, table with all six run IDs/dates/
durations); added the sixth run (33494135668, 2026-09-01); recorded why the per-node-id promotion
streak reset every night (all six runs classified `NEW`, not `TIMING`, by a bare-substring
classifier bug fixed in `cfb9cb4a`, which postdates the frozen `98d3ad8d` checkout and has never
executed in CI); added the axiom-bearing local data point (`HEAD=9ce3b4ad`, 93/103 conclusive, 10
timeouts, 951.21s) with its non-idle-host caveat kept in the same sentence, not a footnote; added
the AXIOM AVENUE CLOSED paragraph to criterion (3), scoped strictly to the six runs at `98d3ad8d`
(never a claim about HEAD, per C7); corrected criterion (4)'s stale function reference from
`compute_promotion_streak` to `compute_per_test_promotion_streak` after confirming both functions
exist and TESTING_GUIDE.md 8.9 describes the latter as driving promotion. Comment-only diff,
zero executable-statement changes.

**Phase 2** — Added one pointer-shaped sentence to TESTING_GUIDE.md 8.9's "Currently marked" bullet
for the gating test, noting the recorded signature was last confirmed against pre-axiom code. The
four entry criteria, the exit-criteria paragraph, the 20-run default, and the standing-rule
paragraph are all byte-identical (confirmed by diff). The standing-rule justification for keeping
the quarantine (marking ~1 week old, well inside the two-review-cycle window; active repair work
in progress) and the confirmation that `cfb9cb4a`'s classifier lesson needs no new guide text (8.9
already documents it) are recorded in this summary and the Phase 2 handoff, per the plan's
pointer-not-restatement instruction — neither was added to the guide itself.

**Phase 3** — Added `_resolve_scan_instrumentation(env_var_name)`, a module-level helper mirroring
Decision D2's inline resolution verbatim in behaviour; wired it into
`test_known_conclusive_population_self_consistent` via the new, distinct
`ORACLE_GATING_SCAN_OUT_DIR` environment variable (never `ORACLE_SCAN_OUT_DIR`, so the two
instrumented tests can never clobber one another's `report.json`/`SCAN_COMPLETE`); left
`test_complexity_5_scan_self_consistent`'s existing D2 block completely untouched (confirmed
byte-identical to HEAD); added a docstring paragraph explaining the env var; amended criterion
(3)'s closing sentence to record the instrumentation is now wired and how to use it; added 5 new
Z3-free tests (`TestResolveScanInstrumentation`) covering unset/empty-defaults, set-value
resolution, cross-variable independence, and the no-files-written-when-unset technique. The
`_assert_scan_report(...)` call and `_assert_scan_report` itself are unmodified.

**Phase 4** — Allocated task 183
("discriminate_gating_shortfall_axiom_vs_contention", `not_started`, `python`,
topic `test-reliability`) consolidating report items 0a, 1, and 2, under the `specs/.scope-lock`
mutex. Its description is self-contained: the six run IDs/counts, the stale-checkout and
classifier-bug explanation, the local `HEAD=9ce3b4ad` data point with its non-idle-host caveat,
the two undiscriminated explanations, the two discriminating observations, the hard constraints
verbatim, and a note that `ORACLE_GATING_SCAN_OUT_DIR` now exists. No shortfall-remediation task
was created — TESTING_GUIDE.md 8.9's escalation trigger has not fired (marking ~1 week old,
active repair work in progress). Cross-referenced task 183 back into the diagnosis report's "What
remains open" section.

**Phase 5** — Closure gate. See "Verification" below for the full C1-C7 record.

## Scope judgment on the instrumentation gap (Phase 3)

Reaffirmed at closure: wiring `ORACLE_GATING_SCAN_OUT_DIR` was in scope because it is opt-in,
off-by-default observability (moves nothing toward green — the same formulas time out, the same
floor fails, the same assertion fires with the same message), it directly answers a gap this same
diagnosis could not close on its own, it follows an existing precedented pattern (Decision D2) in
the same file, and it was verified here without running the long gating scan (against the Z3-free
`_StubOracle` in the fast gating pass). The long gating scan itself was never run in this
dispatch, at any phase, on this or the prior contended host — timing evidence collection is
explicitly deferred to task 183.

## Deviation note: Phase 5's fast-gate command corrected mid-phase

The plan's literal Phase 5 verification command,
`pytest oracle/bimodal_logic/tests/ -m "not slow and not unstable" -q`, does not mirror what real
CI actually runs. `oracle/conftest.py`'s `pytest_collection_modifyitems` applies a `development`
marker as a tree-level blanket to every oracle test EXCEPT the six differential/soundness-core
classes (pre-existing infrastructure, unrelated to this task or to tasks 181/182's concurrent
work) — tests belonging to bimodal, which is under active construction, and whose current failure
is expected and tracked, not a regression. `oracle/run-oracle-suite.sh` (the actual CI entry
point) always includes `and not development` in both its passes. Running the plan's literal
command surfaced 18 failures, none in any file this task touched (`test_boundary_regression.py`,
`test_oracle_interface.py`, `test_oracle_provider.py`, `test_soundness_regression.py`) and all
covered by the `development` blanket. Re-running with the CI-accurate filter,
`-m "not slow and not unstable and not development"`, produced 49 passed, 600 deselected, zero
failures, 220.69s. This is recorded as a corrected verification command, not a plan deviation in
substance — no code, assertion, or constant this task owns was touched by this correction.

## Verification (Phase 5 constraint gate, C1-C7)

All checks scoped to this task's own four phase commits
(`d95be050`, `0fd874cc`, `6a4b1af9`, `ab83ed68`), not the shared working tree — tasks 181 and 182
committed concurrently into the same branch during this dispatch.

| Check | Result |
|---|---|
| C1: `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` unchanged | PASS (grep-confirmed at HEAD) |
| C2: `MIN_CONCLUSIVE_GATING_FORMULAS = 100` unchanged | PASS (grep-confirmed at HEAD) |
| C3: no line inside `_assert_scan_report` changed; no `assert` removed/negated/skipped in `oracle/` | PASS (`_assert_scan_report` byte-identical to pre-task baseline via range diff; the one `-`-line grep hit is a comment mentioning "assert" in prose, not a code statement) |
| C4: `@pytest.mark.unstable` / `@pytest.mark.xdist_serial` counts and attachment points unchanged | PASS (2 / 3, identical to baseline; still attached to the same method/class) |
| C5: no file under `oracle/bimodal_logic/` other than `tests/test_cross_oracle_differential.py`; nothing under `code/src/model_checker/theory_lib/bimodal/` | PASS (confirmed against the union of all four phase commits' changed-file lists) |
| C6: no task-number reference introduced outside `specs/**` | PASS (`check-task-references.sh`: 109 pre-existing occurrences, all under `.opencode/**`, none in any file this task touched, unchanged before/after this task's commits) |
| C7: no claim that the axioms are excluded at HEAD | PASS (both mentions in the source-site block explicitly say "NOT a claim that the axioms are excluded at HEAD"; zero occurrences of any exclusion-at-HEAD claim in either edited file) |

Test gates:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow and not unstable"`: 74 passed, 3 deselected (includes the 5 new instrumentation tests).
- `oracle/bimodal_logic/tests/ -m "not slow and not unstable and not development"` (CI-accurate): 49 passed, 600 deselected, 0 failed, 220.69s.
- `code/tests/ci/ -q`: 167 passed (includes task 181's new `test_gating_selection_bimodal_decoupling.py`).
- The `unstable`-marked gating scan itself was never run in this dispatch, at any phase.

## Plan Deviations

- Phase 5's verification command was corrected from the plan's literal
  `-m "not slow and not unstable"` to the CI-accurate `-m "not slow and not unstable and not
  development"`, for the reason recorded above. No other deviations. All five phases' task
  checklists were executed as specified with no skipped or altered items.

## Follow-on task

Task 183 ("discriminate_gating_shortfall_axiom_vs_contention") carries forward report items 0a,
1, and 2, and the hard constraints, verbatim.
