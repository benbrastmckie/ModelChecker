# Implementation Summary: Divisor-Period Search Coverage

- **Task**: 203 - Research and recommend whether the bimodal search should cover all
  divisor-periods up to each bound, and at what cost
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T00:00:00Z
- **Effort**: ~4.75 hours (matches plan estimate)
- **Dependencies**: 195 (in flight this same cycle; owned `docs/ADEQUACY.md` and three other
  files this plan read but never wrote)
- **Artifacts**: plans/01_divisor-period-search-coverage.md,
  reports/01_divisor-period-search-coverage.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This task's own deliverable — a report comparing three routes to fixing the divisor-period
non-monotonicity in the bimodal certificate search's `back`/`fwd` coverage, with a recommendation
and a staged path, explicitly *not* an implementation — was already complete going into this
round. This plan landed the report's durable conclusions where a future reader and a future
refactorer will find them: a two-level machine-checked regression pin of the non-monotonicity
fact (previously recorded only in prose), a new theory doc recording the decision, and a
territory-gated pointer from `docs/ADEQUACY.md` section 7.1's condition (iii) to that doc. It
deliberately did not build the recommended sweep driver — that is staged as follow-on work.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`: new
  `TestWrapFoldsByExactPeriod` class (6 tests) pinning `WitnessRegistry.wrap()`'s exact-period
  folding arithmetic directly — a back-period-3 family shares a slot at `back=3` but not at
  `back=4`, mirrored for `fwd`, plus an assertion that `bit()` returns the identical Z3 Boolean
  for two positions sharing a slot and a distinct one otherwise.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`
  (new file): pins the end-to-end consequence with two `\prev`-chain premise families run
  through the real `Syntax -> ModelConstraints -> BimodalStructure` pipeline across the grid
  `(2,1,2) (3,1,3) (4,1,4) (5,1,5) (6,1,6)`, asserting `z3_model_status` and `timeout is False`
  at every point.
- `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md` (new file): the fact, two
  corrections to how the gap is often posed, the three routes compared with cost/benefit for
  each, the decision (route (b), the bounded sweep) and its proportionality argument, the
  asymmetric theorem-side cost that gates any default-behavior change, and the staged path.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md`: two additive entries (Quick
  Navigation bullet, `### SEARCH_COVERAGE.md` overview subsection).
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`: one additive sentence under
  section 7.1's (iii-a) sub-bullet, pointing at `docs/SEARCH_COVERAGE.md` by name.

## Decisions

- Confirmed by direct measurement (not merely carried over from the report) that the period-3
  chain is SAT at `(3,1,3)`/`(6,1,6)` and genuinely UNSAT at `(2,1,2)`/`(4,1,4)`/`(5,1,5)`, and
  that a period-2 chain gives the counterpart direction (SAT at `(2,1,2)`, UNSAT at `(3,1,3)`).
  Both reproduced the plan's Scope Hypothesis exactly, with no divergence to record.
- Followed the plan's own correction of the task description's premise: "union over the divisors
  of a bound" is already today's behavior at a single bound (every `p` dividing `n` is already
  representable at `back=n`); the change that matters is the **bounded sweep** over
  `back' in [1, back]`, which is what `docs/SEARCH_COVERAGE.md` recommends and stages.
- Confirmed, against the live source (`LabelledLasso.nb`/`nm`/`nf` are `len(...)` properties on
  the exported label arrays, and `recheck`'s windows read those same properties), that neither
  candidate route touches the certificate wire format or the Lean-side re-checker — closing a
  cost line the task description's original framing raised for both routes (b) and (c).
- Phase 4 (the `ADEQUACY.md` pointer) took the edit branch: the file was clean (no foreign
  uncommitted modification) when checked. The pointer was placed at (iii-a) — a sub-bullet the
  concurrent sibling task (195) had already carved out of the flat condition (iii) — rather than
  at condition (iii) as a whole, following the plan's own fallback instruction for a moved anchor.

## Plan Deviations

- None (implementation followed plan).

## Impacts

- No production code changed. Every edit is additive: two new test modules/classes and a new
  doc, plus one sentence in an existing doc and two additive entries in the docs hub. No existing
  test assertion, class, or production function was altered.
- `ADEQUACY.md` section 7.1 condition (iii) is now discoverable from `docs/SEARCH_COVERAGE.md`'s
  fuller route comparison, without any of that section's existing wording changing.
- The non-monotonicity fact this task pins is now a regression: a future refactor of
  `WitnessRegistry.wrap()` that silently widens or narrows the represented period space will
  break a named test at both the unit and integration level, rather than only violating prose.

## Verification

- Phase 1: `test_witness_registry.py` — 53 passed (6 new). Confirmed the pin bites: a scratch
  `% self.nb -> % (self.nb + 1)` edit to `wrap()` failed 2 of the 6 new assertions; the edit was
  discarded, never committed.
- Phase 2: `test_search_period_coverage.py` — 10 passed in 1.28s. Both premise chains, run once
  before any assertion was written, reproduced the Scope Hypothesis's verdicts exactly (total
  wall clock for all 10 `_build` calls: ~0.92s, well under the ~2s per-point budget).
- Phase 3: every symbol (`wrap`, `slots_per_lasso`, `sel`, `LabelledLasso`, `recheck`,
  `WitnessConstraintGenerator`, `finalize_certificate`, `target_constraints`,
  `mem_all_iff_window`, `coherent_iff_window`, `fulfil_iff_window`) and both test-module paths
  the new doc cites resolve by grep. A manual grep for task-number/`specs/` patterns across both
  new/edited files found none (the repo's `check-task-references.sh` scans only
  `agent-system/extensions`/`.opencode`/`lua`/`.memory`, not `code/`, so it cannot certify this
  directly).
- Phase 4: `git diff` for `ADEQUACY.md` shows exactly one added sentence, nothing else changed.
- Phase 5 (final gate):
  - Full bimodal suite: **591 passed, 4 failed** in 67.24s. All 4 failures are in
    `test_certificate_a2_triangle.py::TestExhaustiveTriangleBoxFree`/`TestExhaustiveTriangleWithBox`
    — a file outside this task's declared scope, confirmed via `git status --short`/`git diff
    --stat` to carry a 79-insertion/20-deletion **foreign uncommitted modification** from the
    concurrent sibling task (195), whose declared `file_scope` names this exact path this cycle.
    Not a regression from this task's work (this task's only source-adjacent change is a new
    test class with no production-code edit, plus one independent new integration module —
    neither touches this file or anything it imports). Left untouched and reported here per the
    concurrency protocol.
  - `code/tests/ -q` (repo-wide, outside the theory): **645 passed, 5 skipped**, 0 failed, in
    47.07s — confirms the 4 failures above are confined to the one foreign in-flight file and
    nothing else regressed repo-wide.
  - `git status --short` after Phase 4's commit shows only foreign, untouched changes (task 195's
    in-flight `test_certificate_a2_triangle.py`; task 204's in-flight plan; shared
    `specs/TODO.md`/`events.jsonl`/`state.json` churned by concurrent sibling activity). Nothing
    from this task's own declared file set was left uncommitted.

## Follow-ups

- The sweep driver, its opt-in setting, and its benchmark against the 53-example suite (with
  particular attention to the theorem-side multiplicative cost) are staged in
  `docs/SEARCH_COVERAGE.md`'s "Open obligations" list, not built by this task.
- `ADEQUACY.md` section 7.1 condition (iii) remains open pending A1 (compression) and (iii-a)
  through (iii-e); this task's pointer makes the route comparison discoverable from there, it
  does not discharge the condition.
- The `test_certificate_a2_triangle.py` failures observed during Phase 5 belong to the concurrent
  sibling task's own in-flight work and are its responsibility to resolve, not a follow-up for
  this task.

## References

- `specs/203_research_divisor_period_search_coverage/plans/01_divisor-period-search-coverage.md`
- `specs/203_research_divisor_period_search_coverage/reports/01_divisor-period-search-coverage.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`
- `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/README.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
