# F5 session-order sensitivity: scope determination

**Question**: is `test_spot_check_individual_countermodels`'s (F5's) session-order sensitivity
scoped to its own class (`TestSpotCheckCrossSignal`), or process-wide (any preceding Z3 work)?
This determines whether adding `@pytest.mark.xdist_serial` to `test_mixed_and_box_next` — which
would move it into F5's serial pass — is safe.

**Answer**: **process-wide**, and the proposed marker is **unsafe**.

## Structural evidence (no run required)

`oracle/run-oracle-suite.sh` pass 2 selects `-m "xdist_serial and not slow"`. Collected order:

1. `test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_1-example_case7]`
2. `test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` (~190 s of Z3 over 103 formulas)
3. `test_oracle_interface.py::TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement[some_past]`
4. `test_oracle_interface.py::TestMixedFormulas::test_mixed_or_diamond_prev` (~73 s of Z3)
5. `test_oracle_interface.py::TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` ← F5
6-10. `test_soundness_regression.py` tests

F5's own class siblings (`test_validate_self_temporal_only`, `test_validate_self_all_formulas`)
are **not** `xdist_serial`-marked, so pass 2 deselects them entirely — yet F5 still fails there.
Class siblings are therefore not necessary for the failure.

## Experimental evidence

All runs serial (`-p no:xdist`), each in its own pytest process, on a machine with no competing
pytest. F5's budget is `TEMPORAL_SOLVE_TIMEOUT_MS = 180000`.

| # | Preceding in-process Z3 work | External load | F5 wall time | Result |
|---|---|---|---|---|
| 1 | none (F5 alone) | competing `pytest` at ~90% CPU | 131.42 s | **PASS** |
| 2 | none (F5 alone) | none (load 1.11) | 135.35 s | **PASS** |
| 3 | `test_mixed_and_box_next` (47.53 s), a **different class** | self only | 180.53 s | **FAIL** |
| 4 | `test_validate_self_temporal_only` (186.68 s) + `test_validate_self_all_formulas` (0.47 s), **same class** | self only | 180.42 s | **FAIL** |
| 5 | gating pass 2: `TestGatingConclusiveScan` + `test_mixed_or_diamond_prev`, **different files** | sibling pytest | >180 s | **FAIL** |

Rows 3 and 4 both fail. Preceding Z3 work triggers the failure whether it comes from inside the
class (row 4) or outside it (rows 3, 5). **The sensitivity is process-wide, not class-scoped.**

### The load confound is ruled out

Loads were higher in rows 3-4 (3.39, 2.50) than in row 2 (1.11), so "it was just CPU load" needs
answering. It does not survive row 1: F5 alone ran **131.42 s and passed while a competing pytest
consumed ~90% of a core**, i.e. under genuine external contention. Meanwhile rows 3-4 blow the
same 180 s budget on a machine whose only load is F5's own back-to-back predecessor.

External CPU contention does **not** push F5 over; preceding in-process Z3 work does. The elevated
load readings in rows 3-4 are the decaying one-minute average of the immediately preceding
sub-run's own single-core Z3 work on a 24-core box — an artifact of running back-to-back, not
starvation. This is the same-process Z3-state effect F5's own docstring already describes, and it
is orthogonal to the cross-worker CPU contention `xdist_serial` exists to eliminate.

## Consequences

**Do not add `@pytest.mark.xdist_serial` to `test_mixed_and_box_next`.** Row 3 *is* that
configuration: `test_mixed_and_box_next` (line 870) sorts before F5 (line 1044) in the same file,
so marking it would place its ~47 s of Z3 work immediately before F5 in the serial pass — the
exact ordering measured to flip F5 from a 135 s pass to a 180 s+ failure. There is also nothing to
fix: `test_mixed_and_box_next` **passed** in the gating run at HEAD (it is in pass 1, which had a
single unrelated failure).

**`xdist_serial` is the wrong mechanism for F5 and currently makes it worse.** The marker routes a
test around *cross-worker* contention, but F5's problem is *in-process* state accumulation. Marking
F5 `xdist_serial` moved it into a pass where roughly 260 s of heavy Z3 (`TestGatingConclusiveScan`
plus `test_mixed_or_diamond_prev`) runs ahead of it in the same process — so the marker placed F5
in a worse position than the parallel pass did, which is consistent with F5 failing in pass 2 while
passing alone every time it is measured.

**What would actually work** (any one of):
- Give F5 process isolation — its own pytest invocation, or `pytest-forked`/a dedicated worker — so
  no prior Z3 work shares its process.
- Order it first within its pass, if a mechanism exists to guarantee that.
- Widen its budget to cover the post-accumulation cost (it needs materially more than 180 s once
  preceded by other Z3 work) — least attractive, since it hides the growth rather than bounding it.
- Reduce what the test solves, so its margin is not set by the slowest formula in the set.

Note that a widened budget alone is a weak fix: the effect scales with how much Z3 work precedes
it, which is a property of the pass composition rather than of the test.
