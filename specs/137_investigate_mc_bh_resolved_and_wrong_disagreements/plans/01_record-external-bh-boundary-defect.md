# Implementation Plan: Task #137

- **Task**: 137 - investigate_mc_bh_resolved_and_wrong_disagreements
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: 133, 139
- **Research Inputs**: `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/reports/01_mc-bh-soundness-disagreements.md`
- **Artifacts**: plans/01_record-external-bh-boundary-defect.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The research report closes the semantic question: all 12 resolved-and-wrong MC/BimodalHarness
disagreements share one root cause, ModelChecker is correct on every one, and the defective side
is BimodalHarness — an external, separately-maintained project outside this repository. No
ModelChecker semantics change is warranted. What remains in scope here is turning an open,
unexplained `strict=True` xfail into an accurate, self-verifying record of a known *external*
defect: promote the report's brute-force ground-truth evaluator into a durable in-repo asset,
use it to classify every MC/BH disagreement at solve time, remove the xfail, and add loud-failure
guards so the accommodation cannot silently absorb a new disagreement, an MC-side regression, a
starved solve budget, or a fixed BimodalHarness. Definition of done:
`test_temporal_only_agreement_complexity_5` passes (not xfails) with the 12 disagreements
attributed to the external defect by ground truth, and any deviation from that exact situation
fails the test with a message naming the deviation.

### Research Integration

Findings carried directly into this plan:

- **F4 (confirmed)**: all 12 disagreements are `(TAUTOLOGY \Until/\Since Y)`-shaped, verdict
  signature `MC_sat=False, BH_sat=True`, ground truth UNSAT. MC correct, BH wrong, on all 12.
- **Recommended Fix Path item 3**: no code change inside `oracle/bimodal_logic/` addresses the
  root cause; the xfail must not be silently removed nor reinterpreted as an MC bug.
- **Recommended Fix Path item 4**: prefer a general adjudication over hard-coding the 12
  formulas, since the same defect recurs at higher complexity. This plan goes one step further
  than the report's suggested syntactic predicate: instead of a "tautology-event" shape test, it
  adjudicates each disagreement against the ground-truth evaluator itself. That is strictly more
  general (it covers any future disagreement of any shape), and it makes the claim "MC is correct
  here" a checked assertion rather than a comment.
- **Executive-summary disclosure**: the evaluator's first version had an off-by-one in the Until
  guard interval that produced a false agreement with BH. The promoted module therefore ships
  with its own test suite, including the report's four sanity checks and a window-stability
  sweep, before anything depends on its verdicts.
- **Count reconciliation (12 vs 13)** and **Open Question 1**: the guards are written so a 13th,
  differently-shaped disagreement fails loudly rather than being absorbed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as `roadmap_path` in the delegation context and
`roadmap_flag` was not set, so no roadmap review/update phases are included and no roadmap items
are claimed. ROADMAP.md is not modified by this plan.

## Goals & Non-Goals

**Goals**:
- Promote the brute-force ground-truth evaluator into `oracle/bimodal_logic/` as a tested,
  runnable, durable asset with a documented correctness contract.
- Replace the `strict=True` xfail on `test_temporal_only_agreement_complexity_5` with an accurate
  representation: disagreements are adjudicated by ground truth and bucketed as external-BH
  defect, MC soundness bug, or unclassified.
- Guarantee loud failure on: an MC-wrong disagreement, an unadjudicable disagreement, a starved
  solve budget, and a BimodalHarness that no longer exhibits the defect.
- Record the upstream BimodalHarness defect in a form that can be filed against that project:
  root cause, code site, the 12 formulas, reproduction, and two concrete fix options.

**Non-Goals**:
- Changing ModelChecker's bimodal semantics, `is_valid_time`, `main_time`, or `M = max(depth+2, 3)`.
  The research confirms MC is correct on all 12; there is nothing to fix on the MC side.
- Editing anything under `/home/benjamin/Projects/BimodalHarness/`. That repository is out of
  scope; this plan produces the defect record, not the fix.
- Touching the existing `_KNOWN_MC_EDGE_CASES` carve-out for `untl(bot, bot)`. The report
  classifies that as a separate, pre-existing mechanism with its own standing attribution.
- Extending the investigation to complexity 6+ formulas (report Open Question 2).
- Chasing the "13th" formula. The guards make a genuine 13th disagreement fail loudly if it
  reappears; that is the correct handling for an unconfirmed, jitter-consistent count.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The ground-truth evaluator is itself wrong (it already had one such bug) | H | M | Phase 1 is test-first and includes the report's four independently-sourced sanity checks plus a window-stability sweep proving verdicts do not change as the brute-force window widens. Nothing depends on its verdicts until those pass. |
| Window truncation makes a formula look falsifiable at the evaluator's own edge — the exact class of bug being diagnosed in BH | H | M | The window-stability test is the direct guard: identical verdicts at window `d+2`, `d+3`, `d+4` for every temporal-only formula at complexity<=5. A verdict that moves with the window is a hard failure, not a tolerance. |
| Brute-force cost explodes (valuation count is `2^(2W+1)` per atom) | M | M | Default window derives from `temporal_depth` (`max(depth+2, 4)`), giving W=4 and 512 valuations for complexity<=5. The wide-window sweep is confined to a `slow`-marked test. Phase 1 records measured wall clock. |
| Staleness guard (`external_bh_defect` non-empty) misfires when all 12 happen to time out, given the documented session-order sensitivity near the 5000 ms budget | M | L | The conclusive-count floor is asserted *first*, so a starved run is diagnosed as a budget regression before the staleness guard is reached; the staleness message explicitly names both readings. Both observed runs resolved all 12. |
| Removing the xfail leaves the test failing for an unforeseen reason | H | L | Phase 5 runs the real test to completion before the task is called done; Rollback restores the xfail with the corrected reason text rather than leaving a red suite. |
| BimodalHarness unavailable, making the whole verification vacuous (`setup_method` skips) | H | L | Phase 5 asserts BH importability as an explicit precondition and treats a skip as a blocker, not a pass. |
| New task-number references leak into `oracle/**` deliverables | L | M | Every phase writing outside `specs/**` states the durable-anchor requirement; Phase 5 greps the touched files for task-number citation patterns. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. Phases 2 and 4 touch disjoint files
(Phase 2: `tests/test_disagreement_classification.py`, `tests/ground_truth_classify.py`;
Phase 4: `KNOWN_EXTERNAL_DEFECTS.md`, `README.md`) and may run concurrently.

---

### Phase 1: Promote the ground-truth evaluator into the repository [COMPLETED]

**Goal**: `oracle/bimodal_logic/ground_truth.py` exists as a tested, runnable, independently
trustworthy decision procedure for temporal-only formulas, with its correctness contract stated
and checked.

**Tasks**:
- [x] Write `oracle/bimodal_logic/tests/test_ground_truth.py` FIRST (RED). Required cases:
  - The four sanity checks from the research report's validation table:
    `(p Until q) -> (q Until p)` = SAT; `bot Until bot` = SAT; `p -> p` = UNSAT; `p` = SAT.
  - All 12 confirmed formulas (the `(TAUTOLOGY \Until/\Since Y)` list in the report's findings
    table, in their JSON form) evaluate to UNSAT.
  - **Window stability**: for every temporal-only formula at complexity<=5, the verdict is
    identical at windows `d+2`, `d+3`, and `d+4` (where `d` is the formula's temporal depth).
    Mark this test `@pytest.mark.slow` if measured runtime exceeds ~15s; otherwise leave it in
    the fast set. *(Measured 0.08s -- left in the fast set, not marked slow.)*
  - A formula containing a `box` node raises the module's dedicated unsupported-formula
    exception (not a bare `ValueError`, not a silent wrong answer).
  - The default window is derived from the formula, not hard-coded, and is at least `depth+2`.
- [x] Confirm the tests fail against the absent module (RED).
- [x] Create `oracle/bimodal_logic/ground_truth.py`, ported from
  `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/run/ground_truth.py`, with these
  changes: reuse `bimodal_logic.translation.temporal_depth` rather than reimplementing depth;
  default `window = max(temporal_depth(formula) + 2, 4)`; raise a module-defined
  `GroundTruthUnsupported(ValueError)` for any tag outside `{atom, bot, imp, untl, snce}`;
  keep the corrected Until guard interval `range(t + 1, tp)` together with the source comment
  explaining why the closed-at-`t` version was wrong.
- [x] Add a `python -m bimodal_logic.ground_truth '<formula-json>'` entry point so the asset is
  runnable, mirroring `bimodal_logic.cli`'s shape.
- [x] Write the module docstring to state the correctness contract explicitly: this is a decision
  procedure for the *unbounded*-time semantics only insofar as widening the window does not move
  the verdict, and that property is enforced by the window-stability test rather than assumed.
- [x] Record measured wall clock for the new tests in the module or test docstring.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `oracle/bimodal_logic/ground_truth.py` - new module (port + hardening + CLI entry point)
- `oracle/bimodal_logic/tests/test_ground_truth.py` - new test module

**Verification**:
- `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_ground_truth.py -v` passes.
- The window-stability case is present and green; a deliberate temporary narrowing of the default
  window is confirmed to make it fail (proves the guard has teeth), then reverted.
- No task-number references in either new file.

---

### Phase 2: Disagreement classifier with unit tests [COMPLETED]

**Goal**: A pure, Z3-free function that adjudicates a single MC/BH disagreement against ground
truth and returns exactly one of three outcomes, with the "cannot adjudicate" case explicit
rather than swallowed.

**Tasks**:
- [x] Write `oracle/bimodal_logic/tests/test_disagreement_classification.py` FIRST (RED),
  driving the classifier with synthetic `mc_sat`/`bh_sat` values so no solver is invoked:
  - Ground truth UNSAT, `mc_sat=False`, `bh_sat=True` -> `external_bh_defect` (use one of the 12).
  - Ground truth UNSAT, `mc_sat=True`, `bh_sat=False` -> `mc_soundness_bug` (same formula,
    verdicts swapped — proves the classifier is not keying on the formula shape).
  - Ground truth SAT, `mc_sat=False`, `bh_sat=True` -> `mc_soundness_bug`.
  - A `box`-containing formula -> `unclassified` (exception mapped, not propagated).
  - Agreement (`mc_sat == bh_sat`) is rejected as a programming error rather than silently
    classified.
- [x] Confirm RED, then implement `classify_disagreement(formula_json, mc_sat, bh_sat) -> str` in
  a new `oracle/bimodal_logic/tests/ground_truth_classify.py` (test-support module; `pytest`'s
  `python_files = "test_*.py"` means it is not collected as a test).
- [x] Keep the three outcome strings as module-level named constants so the differential test and
  the defect record refer to the same tokens.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `oracle/bimodal_logic/tests/ground_truth_classify.py` - new classifier module
- `oracle/bimodal_logic/tests/test_disagreement_classification.py` - new test module

**Verification**:
- `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_disagreement_classification.py -v`
  passes in under ~5 seconds (no solver involvement).
- Collection succeeds both from the repository root and with `oracle/` as the invocation root
  (this tree has no reachable pytest ini file — see `oracle/conftest.py`'s module docstring).

---

### Phase 3: Replace the xfail with adjudicated bucketing and loud-failure guards [NOT STARTED]

**Goal**: `test_temporal_only_agreement_complexity_5` records the real state of the world: it
passes, attributes the 12 disagreements to the external BimodalHarness defect via ground truth,
and fails loudly on any deviation.

**Tasks**:
- [ ] Delete the `@pytest.mark.xfail(strict=True, reason=...)` decorator from
  `test_temporal_only_agreement_complexity_5`. Keep `@pytest.mark.slow` and the class-level
  `@pytest.mark.differential`.
- [ ] Leave `_KNOWN_MC_EDGE_CASES` and its `untl(bot, bot)` entry exactly as they are — a
  separate, pre-existing mechanism with its own attribution.
- [ ] Replace the single `resolved_and_wrong` bucket with three buckets fed by
  `classify_disagreement`: `external_bh_defect`, `mc_soundness_bug`, `unclassified`. Keep
  `inconclusive` unchanged.
- [ ] Print all four counts unconditionally, in the style of `_assert_scan_report`, so a green run
  is still informative.
- [ ] Assert, in this order (the order matters — it makes each failure self-diagnosing):
  1. `conclusive >= MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS` — a new module-level constant, a
     *budget/performance* floor, with a comment recording its measured basis and the existing
     "never widen this to paper over a contended run" convention already used by the sibling
     floors in this tree.
  2. `not mc_soundness_bug` — ground truth sides with BimodalHarness against ModelChecker: a real
     in-repo soundness defect. Message must say so plainly and list the formulas.
  3. `not unclassified` — a disagreement ground truth cannot adjudicate (e.g. a new shape outside
     the evaluator's supported fragment). Message must direct the reader to extend the evaluator
     rather than widen the accommodation.
  4. `external_bh_defect` is non-empty — the staleness guard. Message must distinguish the two
     readings: (a) the external defect has been fixed upstream, so this accommodation is now dead
     code and must be deleted along with the classifier call; (b) a starved budget, which
     assertion 1 already rules out by construction.
  5. Every `external_bh_defect` entry has `mc_sat is False and bh_sat is True` — the documented
     signature. A member with any other signature fails, so a *different* external defect cannot
     hide inside this bucket.
- [ ] Rewrite the test docstring to describe the external defect accurately, citing durable
  anchors only: `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` for the root cause and
  `oracle/bimodal_logic/ground_truth.py` for the adjudication basis. No task numbers, no "13
  formulas" claim, no implication that this is an MC bug.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - remove xfail, add three-bucket
  classification, five ordered assertions, new floor constant, rewritten docstring

**Verification**:
- `PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5 -v -s -p no:cacheprovider`
  reports PASSED (not XFAIL, not XPASS) with `external_bh_defect=12`, `mc_soundness_bug=0`,
  `unclassified=0`. Expected wall clock ~9-10 minutes based on the report's measured 546.74s.
- Each of the five assertions is confirmed to have teeth by temporarily inverting its input and
  observing the intended failure message, then reverting.

---

### Phase 4: Record the upstream BimodalHarness defect [COMPLETED]

**Goal**: A standalone, fileable defect record for the external project, plus repository
navigation pointing at it.

**Tasks**:
- [x] Create `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` covering:
  - Scope statement: defects in *external* reference oracles that this repository's differential
    suite accommodates, and the standing rule that an accommodation is deleted once upstream
    fixes the defect.
  - The defect: BimodalHarness's `find_countermodel`
    (`/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/z3_provider.py`, the
    `encoded_cells` loop asserting `Or(Not(cell) ...)` across every `(w, t)` cell) treats its own
    frame's edge cells (`t = m_time` for Until, `t = 0` for Since) as genuine falsifying points.
  - Why ModelChecker is correct: `main_time` fixed at 0 with the valid-time interval `(-M, M)`
    and `M = max(depth+2, 3)`, the deliberate boundary-safety invariant already tracked by
    `TestBoundaryVacuity` in `oracle/bimodal_logic/tests/test_soundness_regression.py`; and the
    canonical semantics typing time as a `LinearOrderedAddCommGroup`, which has no maximal or
    minimal element.
  - The 12 affected formulas in both readable and JSON form, with the shared signature
    `MC=UNSAT, BH=SAT, ground truth=UNSAT`.
  - Reproduction: the exact pytest invocation from the Phase 3 verification, plus the
    `python -m bimodal_logic.ground_truth '<json>'` one-liner for adjudicating a single formula.
  - Two proposed upstream fixes, as stated in the research: (a) exclude the literal edge cells
    from the falsifying-point search; (b) pad `m_time` against the formula's own temporal depth
    before scanning.
  - Removal criterion: when upstream fixes this, the differential test's staleness assertion
    fires; the correct response is to delete the accommodation, not to relax the assertion.
- [x] Add a short "Known External Oracle Defects" section to `oracle/bimodal_logic/README.md`
  pointing at the new file, and add `ground_truth.py` to the README's Layout tree.
- [x] Use durable anchors only — file paths, symbol names, section headings. No task numbers
  anywhere in either file (pre-existing task references elsewhere in README.md are out of scope
  for this plan and are not to be relied on as precedent).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` - new defect record
- `oracle/bimodal_logic/README.md` - new pointer section, Layout tree entry

**Verification**:
- Every file path, symbol name, and line-anchored claim in the new document is confirmed against
  the actual files before the phase is called done.
- `grep -nEi 'task [0-9]|tasks [0-9]' oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` returns
  nothing, and the README diff introduces no new task-number citation.

---

### Phase 5: End-to-end verification and evidence capture [NOT STARTED]

**Goal**: The whole change is proven green against the real BimodalHarness, with real output
captured, and the floor constant's measured basis recorded rather than guessed.

**Tasks**:
- [ ] Confirm BimodalHarness is importable
  (`PYTHONPATH=/home/benjamin/Projects/BimodalHarness/src python -c 'import bimodal_harness'`).
  If it is not, stop and report a blocker — a skipped `TestBimodalHarnessIntegration` makes this
  verification vacuous and must never be reported as a pass.
- [ ] Run the fast new tests:
  `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_ground_truth.py oracle/bimodal_logic/tests/test_disagreement_classification.py -v`.
- [ ] Run the full BH integration class to completion with real output captured:
  `PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration -v -s -p no:cacheprovider`.
- [ ] Update `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS` to a value derived from the measured conclusive
  count in that run (conservatively below it, not equal to it), and record the measured number and
  date-free provenance in the adjacent comment.
- [ ] Run the non-slow oracle suite for regressions:
  `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests -m "not slow" -q`.
- [ ] Grep all files touched by this task outside `specs/**` for task-number citation patterns.
- [ ] Paste the real, unedited pytest output (not paraphrased) into the implementation summary,
  including the printed four-bucket counts.

**Timing**: 1 hour (mostly wall-clock waiting on the ~10-minute slow test)

**Depends on**: 3, 4

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - floor constant value and its
  measured-basis comment

**Verification**:
- `test_temporal_only_agreement_complexity_5` reports PASSED with `external_bh_defect=12`,
  `mc_soundness_bug=0`, `unclassified=0`.
- No other test in `TestBimodalHarnessIntegration` regressed.
- The `-m "not slow"` oracle run is green.

---

## Testing & Validation

- [ ] `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_ground_truth.py -v` — green,
  including the window-stability sweep.
- [ ] `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests/test_disagreement_classification.py -v`
  — green, solver-free, seconds not minutes.
- [ ] `PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration -v -s`
  — `test_temporal_only_agreement_complexity_5` PASSED, `external_bh_defect=12`,
  `mc_soundness_bug=0`, `unclassified=0`.
- [ ] `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests -m "not slow" -q` — no regressions.
- [ ] Each of the five ordered assertions in the rewired test demonstrated to fail with its
  intended message when its input is temporarily inverted.
- [ ] TDD order honored: every code module in Phases 1-2 has a failing test before implementation.
- [ ] No task-number citations introduced anywhere under `oracle/`.

## Artifacts & Outputs

- `oracle/bimodal_logic/ground_truth.py` — durable, runnable brute-force ground-truth evaluator
- `oracle/bimodal_logic/tests/test_ground_truth.py` — its test suite, including window stability
- `oracle/bimodal_logic/tests/ground_truth_classify.py` — three-way disagreement classifier
- `oracle/bimodal_logic/tests/test_disagreement_classification.py` — classifier tests
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — xfail removed, adjudicated
  bucketing and five ordered guards added
- `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` — fileable upstream defect record
- `oracle/bimodal_logic/README.md` — pointer section and Layout tree entry
- `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/summaries/01_record-external-bh-boundary-defect-summary.md`
  — implementation summary with real pytest output

## Rollback/Contingency

- Phases 1, 2, and 4 are purely additive (new modules, new document, two additive README edits);
  reverting means deleting the new files and reverting the README hunk.
- Phase 3 is the only edit to an existing test. If the rewired test does not pass in Phase 5 for a
  reason this plan did not anticipate, do **not** leave the suite red and do **not** weaken a
  guard to force green. Restore the `xfail` on `test_temporal_only_agreement_complexity_5` with a
  corrected `reason` string — stating that the divergence is a confirmed *external*
  BimodalHarness boundary-scan defect, that ModelChecker's verdict is correct, and pointing at
  `KNOWN_EXTERNAL_DEFECTS.md` — and report what blocked full removal. That fallback still
  discharges the core requirement (the suite stops recording an unexplained divergence) even if
  the stronger self-verifying form cannot land.
- If the ground-truth evaluator fails its own window-stability test in Phase 1, stop: nothing
  downstream may depend on its verdicts. Report it as a blocker, since it would call the research
  report's central conclusion into question and warrants re-research rather than a workaround.
