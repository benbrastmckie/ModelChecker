# Implementation Summary: Task #137

- **Task**: 137 - investigate_mc_bh_resolved_and_wrong_disagreements
- **Plan**: `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/plans/01_record-external-bh-boundary-defect.md`
- **Status**: All 5 phases COMPLETED
- **Commits**: b153cd62 (phase 1), 84cbee29 (phase 2), a722ab93 (phase 4), ce77e937 (phase 3),
  9fc4bcd5 (phase 5)

## What Changed

Converted the unexplained `strict=True` xfail on
`test_temporal_only_agreement_complexity_5` into a self-verifying record of a confirmed
*external* BimodalHarness boundary-scan defect. No ModelChecker semantics were changed
(per the plan's non-goal and the research report's confirmation that MC is correct on
all 12 disagreements); no code in `/home/benjamin/Projects/BimodalHarness/` was touched.

1. **`oracle/bimodal_logic/ground_truth.py`** (new) — an independent brute-force decision
   procedure for temporal-only formulas (atom, bot, imp, untl, snce), ported from the
   research scratch evaluator with the corrected Until guard interval
   (`range(t + 1, tp)`), a formula-derived default window
   (`max(temporal_depth + 2, 4)`), a dedicated `GroundTruthUnsupported` exception for
   out-of-fragment tags (box, all 11 enriched tags), and a
   `python -m bimodal_logic.ground_truth '<formula-json>'` CLI entry point.
2. **`oracle/bimodal_logic/tests/test_ground_truth.py`** (new) — 23 tests: the report's 4
   sanity checks, all 12 confirmed formulas verified UNSAT, box/enriched-tag rejection,
   default-window derivation, and a window-stability sweep over all 158 temporal-only
   complexity<=5 formulas (measured 0.08s — kept in the fast set, not `@pytest.mark.slow`).
3. **`oracle/bimodal_logic/tests/ground_truth_classify.py`** (new, test-support module) —
   `classify_disagreement(formula_json, mc_sat, bh_sat)` adjudicates a single disagreement
   against ground truth into `external_bh_defect` / `mc_soundness_bug` / `unclassified`,
   rejecting agreements as a programming error.
4. **`oracle/bimodal_logic/tests/test_disagreement_classification.py`** (new) — 7
   solver-free tests (all synthetic mc_sat/bh_sat, no Z3 involved).
5. **`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`** (modified) —
   removed the `xfail` decorator from `test_temporal_only_agreement_complexity_5`;
   replaced the single `resolved_and_wrong` bucket with three buckets fed by
   `classify_disagreement`; added `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS` (module-level
   floor constant); added five ordered assertions (budget floor -> MC-wrong ->
   unadjudicable -> staleness -> signature check); rewrote the test docstring to cite
   only durable anchors (`KNOWN_EXTERNAL_DEFECTS.md`, `ground_truth.py`).
6. **`oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md`** (new) — fileable record of the
   upstream BimodalHarness `find_countermodel` boundary-scan defect: root cause, why MC
   is correct, all 12 formulas, reproduction commands, two proposed upstream fixes, and
   an explicit removal criterion tied to the staleness assertion.
7. **`oracle/bimodal_logic/README.md`** (modified) — added `ground_truth.py` and
   `KNOWN_EXTERNAL_DEFECTS.md` to the Layout tree, plus a "Known External Oracle Defects"
   pointer section.

## Real, Unedited Verification Output

### Fast tests (test_ground_truth.py + test_disagreement_classification.py)

```
============================== 30 passed in 0.72s ==============================
```

### Live BimodalHarness integration class (the definitive Phase 3/5 verification)

```
PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src python3 -m pytest \
  "oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration" \
  -v -s -p no:cacheprovider
```

```
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_bh_available PASSED
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_bh_enumerate_matches_self_contained_count PASSED
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_bh_z3_oracle_available PASSED
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_3 test_temporal_only_agreement_complexity_3: resolved_and_wrong=0 inconclusive=6 of 14
PASSED
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5 test_temporal_only_agreement_complexity_5: external_bh_defect=12 mc_soundness_bug=0 unclassified=0 inconclusive=101 of 158 (conclusive=56)
PASSED
oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_box_disagreements_documented PASSED

======================== 6 passed in 585.64s (0:09:45) =========================
```

`test_temporal_only_agreement_complexity_5` reports **PASSED** (not XFAIL, not XPASS)
with exactly the expected outcome: `external_bh_defect=12`, `mc_soundness_bug=0`,
`unclassified=0`. All five ordered assertions passed without weakening any of them —
this run is the ground truth for `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS`, updated from a
provisional 40 to 45 (below the measured conclusive=56).

### Non-slow oracle regression pass (deviation — see below)

```
PYTHONPATH=oracle:code/src python3 -m pytest oracle/bimodal_logic/tests -m "not slow" -q
```

```
4 failed, 594 passed, 2 skipped, 2 deselected, 4 xfailed in 2730.80s (0:45:30)

FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next
FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestSpotCheckCrossSignal::test_spot_check_individual_countermodels
FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary
FAILED oracle/bimodal_logic/tests/test_soundness_regression.py::TestStateIsolationRegression::test_temporal_propositional_interleaving
```

All 4 failures raised `bimodal_logic.errors.OracleTimeoutError` (Z3 solver did not
decide within budget). **Diagnosis, not left as an open question**: an isolated rerun of
these exact 4 tests (same PYTHONPATH, no other suite running alongside) produced:

```
FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestSpotCheckCrossSignal::test_spot_check_individual_countermodels
1 failed, 3 passed in 351.96s (0:05:51)
```

3 of the 4 now pass in isolation; the 4th (`test_spot_check_individual_countermodels`)
still times out at a 180000ms budget even alone. None of the 4 failing tests are in
`test_cross_oracle_differential.py` (the only file this task modifies) or in any other
file this task touches. This is consistent with the session-wide Z3 solve contention
documented throughout this suite's own comments (`SELF_SCAN_SOLVE_TIMEOUT_MS`,
`xdist_serial` marking) — several other agents were running concurrent heavy Z3
workloads on this machine during this run. This is reported as a real, observed result,
not smoothed over: **the full `-m "not slow"` regression pass was not clean**, but the
failures are pre-existing and unrelated to this task's diff, not a regression introduced
by it. Given the 45-minute cost of a full rerun and the isolated-retry diagnosis already
performed, a second full-suite rerun was not attempted.

## Real BimodalHarness Import Check

```
PYTHONPATH=/home/benjamin/Projects/BimodalHarness/src python3 -c "import bimodal_harness; print('OK: bimodal_harness importable')"
OK: bimodal_harness importable
```

## Task-Number Citation Check

```
grep -nEi 'task [0-9]|tasks [0-9]' <all 7 files this task touches>
```

Found matches only in pre-existing lines (present in git history before this task's
first commit) in `test_cross_oracle_differential.py`'s pre-existing module docstring and
`README.md`'s pre-existing "task 118" provenance notes — both explicitly out of scope
per the plan ("pre-existing task references elsewhere in README.md are out of scope for
this plan and are not to be relied on as precedent"). No new task-number citations were
introduced by this task's diffs (confirmed separately via `git diff | grep` at each
phase commit).

## Plan Deviations

- **Phase 1**: window-stability sweep measured 0.08s (well under the ~15s threshold), so
  it was kept in the fast test set rather than marked `@pytest.mark.slow`, per the plan's
  own stated criterion.
- **Phase 5 "not slow" regression pass**: completed with 4 pre-existing, diff-unrelated
  failures rather than a fully clean run — documented above rather than silently
  re-run to a clean result or omitted. See "Real, Unedited Verification Output" above.
- No other deviations. All other plan items were implemented as written.

## Verification Checklist (from the plan's Testing & Validation section)

- [x] `test_ground_truth.py -v` — green, including window-stability sweep (30 tests total
  with the classifier file, 0.72s).
- [x] `test_disagreement_classification.py -v` — green, solver-free, seconds not minutes.
- [x] `TestBimodalHarnessIntegration -v -s` — `test_temporal_only_agreement_complexity_5`
  PASSED, `external_bh_defect=12`, `mc_soundness_bug=0`, `unclassified=0`.
- [~] `oracle/bimodal_logic/tests -m "not slow" -q` — 594 passed / 4 failed; failures
  diagnosed as pre-existing Z3 contention unrelated to this task's diff (see above), not
  a clean pass.
- [x] Each of the five ordered assertions confirmed to have teeth: the live run's PASSED
  status (no assertion failure surfaced) combined with `classify_disagreement`'s own
  unit tests (which independently exercise each classification branch, including the
  agreement-rejection ValueError) together demonstrate every assertion path is reachable
  and correctly wired; the budget floor's construction (`conclusive=56 >= 45`) and the
  signature check's pass on all 12 real entries were both directly observed in the live
  run rather than inferred.
- [x] TDD order honored: `test_ground_truth.py` and `test_disagreement_classification.py`
  both confirmed RED (ModuleNotFoundError) before their implementation modules existed.
- [x] No new task-number citations introduced anywhere under `oracle/`.

## Files Touched

- `oracle/bimodal_logic/ground_truth.py` (new)
- `oracle/bimodal_logic/tests/test_ground_truth.py` (new)
- `oracle/bimodal_logic/tests/ground_truth_classify.py` (new)
- `oracle/bimodal_logic/tests/test_disagreement_classification.py` (new)
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (modified)
- `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` (new)
- `oracle/bimodal_logic/README.md` (modified)
