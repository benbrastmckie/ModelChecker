# Implementation Summary: A2-triangle encoding completeness test

- **Task**: 191 - A2 triangle encoding completeness test
- **Status**: [COMPLETED]
- **Started**: 2026-09-25T21:00:00Z
- **Completed**: 2026-09-26T00:18:46Z
- **Effort**: ~4.5 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_a2-triangle-encoding-completeness.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Built the A2-triangle encoding-completeness test named in `bimodal/docs/ADEQUACY.md` section 7.3:
an exhaustive candidate enumeration over subsets of the closure at `back = mid = fwd = 1`,
comparing the pure-Python re-checker's aggregate verdict against the real Z3/`BimodalStructure`
search's SAT/UNSAT verdict (leg iii, the direction no prior test exercised), plus a bounded
sample cross-checked against `lake exe check_certificate` (leg ii). All five plan phases are
complete; the two-tier module is green, and so is the full bimodal suite and the repo-wide test
gate, modulo one unrelated, pre-existing failure attributable to a concurrently-dispatched
sibling task (see Impacts).

## What Changed

- Added `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`: extracted the
  `lake exe check_certificate` invocation, checkout/`lake` resolution, and skip-reason
  computation out of `test_certificate_lean_agreement.py` into a shared, publicly-named helper.
- Added `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`:
  - `_candidates`, a deterministic exhaustive generator over `(bx, lassos, target_time)`
    candidates, reading the candidate space's shape (closure, active lassos, box children,
    target window) from the live search object rather than re-deriving it.
  - Tier 1 (`TestExhaustiveTriangleBoxFree`, `TestExhaustiveTriangleWithBox`): exhaustive
    comparison of legs (i)/(iii) over three closures -- two box-free (one SAT, one UNSAT) and
    one with a `Box` (SAT, exercising the witness-lasso and `bx` dimensions), the last marked
    `slow`.
  - Tier 2 (`TestBoundedLeanCrossCheck`): a deterministic, fixed-stride sample of 5 accepted and
    5 rejected candidates per closure, plus each SAT closure's live extracted certificate, all
    cross-checked against leg (ii); skips cleanly via the shared helper without a BimodalLogic
    checkout.
- Re-pointed `test_certificate_lean_agreement.py` (and, once discovered, `test_semantics_core.py`)
  at the new shared helper; corrected the former's docstring to state it covers legs (i)/(ii) on
  the fixture corpus only, not the full triangle.
- Updated `bimodal/docs/ADEQUACY.md` section 7.3 and `bimodal/tests/README.md` to record the new
  module as the standing A2 deciding test.

## Decisions

- Followed the plan's already-resolved runtime decision: the literal subsets-of-`C` enumeration
  is affordable unconditionally (no atoms-only fallback generator needed).
- Applied the Lean skip (`SKIP_REASON`) as a `@pytest.mark.skipif` **on `TestBoundedLeanCrossCheck`
  only**, not as a module-level `pytestmark` as the plan's Phase 4 task list literally said --
  a module-level skip would also skip Tier 1, contradicting the plan's own Testing & Validation
  requirement that Tier 1 keep running and passing under `BIMODAL_LOGIC_PATH=/nonexistent`.
- Kept `LEAN_SAMPLE_PER_CLASS = 5` rather than lowering it: the measured Tier 2 total (~58s
  across three cases) sits within the plan's own ~50-60s estimate, even though most of the
  single-box case's cost is two Python-side enumeration passes over its 1,572,864 candidates
  (needed to fix a deterministic stride), not the ~11 Lean subprocess calls themselves. Added an
  early-exit once both sample quotas are filled, with modest effect.

## Plan Deviations

- **Phase 1**: discovered a second, plan-unanticipated importer of the moved Lean-check names
  (`tests/unit/test_semantics_core.py`'s `TestExportedCertificateAgreesWithLeanBinary`), contradicting
  the plan's verification-step assumption that no other importer existed. Re-pointed it at the
  shared helper (`_lean_check.py`) directly, with a small local timeout constant replacing the
  borrowed fixture-specific one. Recorded inline in the plan.
- **Phase 4**: applied the Lean skip at class level, not module level (see Decisions above) --
  a deliberate divergence from the literal task-list wording, required to satisfy the plan's own
  stated verification criterion. Recorded inline in the plan.
- No other deviations; all other tasks in all five phases were followed as specified, and every
  measured count (candidate totals, accepted counts, closure sizes, SAT/UNSAT verdicts, timings)
  matched the plan's own pre-computed expectations exactly.

## Impacts

- **Observed A2-triangle verdicts** (the deliverable this task exists to produce): all three
  closures agree across all three legs.
  - `[] / ["(q \Until p)"]`: `|C|=3`, 1,536 candidates, 52 accepted, Z3 SAT.
  - `["A"] / ["A"]`: `|C|=1`, 24 candidates, 0 accepted, Z3 UNSAT.
  - `["\Box A"] / ["B"]`: `|C|=3` (one `Box`, two lassos), 1,572,864 candidates, 96 accepted, Z3
    SAT.
  No encoding incompleteness or unsoundness found in any of the three closures.
- **Foreign finding, not caused by this task**: the full bimodal suite run during Phase 5
  surfaced one failing test outside this task's scope --
  `bimodal/tests/integration/test_iterate.py::TestLiveIteration::
  test_iterate_three_yields_three_pairwise_distinct_certificates` (`assert 0 == 2`). Confirmed
  via `git log` that this is task 189's own deliberately-red reproduction test
  (`task 189 phase 1: baseline, reproduction, and failing live test`), committed to the shared
  working tree mid-way through this task's own phases (task 189 was dispatched concurrently on
  the same tree this cycle, per the dispatch's Territory note), for an unrelated iterator defect
  that task's own plan is still fixing. With that one test deselected, the full bimodal suite
  (374 tests) and the full `code/tests/` repo gate (645 passed, 5 skipped) are both green.
- The Lean-dependent tests in the new module (and the pre-existing ones) add real subprocess
  time when a BimodalLogic checkout is present (~58s for Tier 2 alone, ~72s for the whole new
  module including the `slow`-marked Tier 1 box case) but skip cleanly and near-instantly
  without one.

## Follow-ups

- None owned by this task. Task 189's iterator fix is tracked under its own task/plan and is
  unaffected by this task's changes.

## References

- `specs/191_a2_triangle_encoding_completeness_test/plans/01_a2-triangle-encoding-completeness.md`
- `specs/191_a2_triangle_encoding_completeness_test/reports/01_a2-triangle-encoding-completeness.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (section 7.3)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`
