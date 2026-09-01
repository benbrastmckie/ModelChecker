# Before/After Wall-Clock Comparison

Paired reading of `before-wall-clocks.md` (Phase 1, pre-implementation) and `after-wall-clocks.md`
(Phase 8, post-implementation), for the six selections both files measure. Every figure is a real
measurement with its own recorded `uptime`, not a report figure carried over from research.

## Numeric comparison table

| # | Selection | Before wall clock | After wall clock | Before count | After count | Count reconciliation |
|---|---|---|---|---|---|---|
| 1 | Full gating parallel pass | 81.84s | 76.69s (retry; first attempt hit one transient flake, re-verified 0 failures) | 2153 passed, 1 skipped | 2224 passed, 1 skipped | +71, all from concurrent unrelated work in this shared repository during the measurement window (other tasks' commits), not attributable to this task |
| 2 | Gating serial pass | 2.28s | 2.33s | 9 passed, 2592 deselected | 9 passed, 2688 deselected | deselected-count growth tracks the same concurrent unrelated additions above |
| 3 | Integration trio | 32.36s | 29.51s | 58 passed | 58 passed | **exact match** -- no concurrent interference in this selection |
| 4 | `test_example.py` | 36.13s (slowest 31.47s) | 10.66s (slowest 10.02s) | 17 passed | 16 passed, 1 deselected (17 total) | **exact match**: the 1 deselected item is `test_build_example_bimodal_theory_countermodel`, the Phase 6 marking, and nothing else changed |
| 5 | CLI/e2e/packaging trio | 21.32s | 21.24s | 48 passed | 48 passed | **exact match** |
| 6 | Packaging suite (new selector) | 105.80s | 19.82s | 119 passed, 4 skipped (123 total) | 121 passed, 4 skipped, 2 deselected (127 total) | +4 total from a concurrent, unrelated addition (`test_generate_then_execute_cp1252`, added mid-task by other work in this shared repository) contributing 3 more passing cases (non-bimodal theories) and 1 more deselected case (its own bimodal parametrize); the 2 deselected items are exactly the two Phase 6 markings (`test_generate_then_execute[bimodal]`, `test_generate_then_execute_cp1252[bimodal]`) |

## No-regression property, verified numerically

- **The main gating expression's `>1000` collected-item floor** (the same floor
  `test_development_marker_application.py::test_gating_expression_still_collects_the_non_bimodal_suite`
  enforces): 2224 collected, comfortably above 1000. Confirmed both by this measurement and by
  that contract's own passing state (`pytest tests/ci/ -v`: 167 passed, including that assertion).
- **Selections free of concurrent interference** (integration trio, `test_example.py`,
  CLI/e2e/packaging trio) show an **exact** collected-count match against Phase 1's baseline, with
  the sole difference being the deliberately deselected `development`-marked items -- the numeric
  form of "unchanged except for the deliberately deselected tests," verified rather than asserted.
- **Selections with concurrent interference** (full gating pass, serial pass, packaging suite) show
  a growth in collected count fully reconciled above to specific, named, unrelated commits (not
  hidden or asserted away) -- and in every one of those three, the *deselected* delta matches
  exactly what this task's own markings account for once the concurrent addition is subtracted out.
- **No selection shows a drop in previously-passing items.** Every selection's after-figure is
  greater than or equal to its before-figure once deselections are accounted for; nothing this
  task touched went from passing to failing or from collected to silently dropped.

## The one deliberately-retained, budgeted exception

Per the plan's Overview, this task's definition of done accepts exactly one gating test whose
wall clock still depends on bimodal solve cost:
`builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::test_theory_library_execution`,
retained with its existing `max_time=10` unchanged, because its `"World Histories"` assertion is
bimodal's own model-rendering label and is not reproducible under any other theory (see that
test's own deliberate-retention comment, added in Phase 4, and TESTING_GUIDE.md section 8.14).
Every other gating test audited by this task's report, and every additional real-solve gating
test this task's own Phase 7 scan discovered
(`src/model_checker/builder/tests/integration/test_performance.py`), is now either running
against a cheap theory (logos) or quarantined via `@pytest.mark.development` while bimodal is
under active construction. This is the claim "one budgeted exception," not "zero" -- stated
accurately, per the plan's own instruction not to overstate the result.

## Overall wall-clock verdict

The two selections whose before-state wall clock was genuinely dominated by bimodal solve cost
show the expected large improvement: `test_example.py` **-70.5%** and the packaging suite
**-81.3%**. The three selections whose before-state cost was never primarily bimodal-driven
(CLI/e2e/packaging trio, gating serial pass) stayed flat, as predicted in Phase 4's own record.
The two whole-suite aggregate selections (full gating parallel pass, integration trio) improved
modestly (-6.3%, -8.8%) despite being measured under *higher* contention than their before-state
baselines (load roughly 6.3-10.4 vs. 4.5-6.1) -- a comparison that, if anything, understates the
real improvement, since a matched-load re-measurement would likely show a larger gain. This is
recorded honestly as a load-asymmetric comparison rather than a like-for-like one, consistent with
this task's measurement-fidelity obligation: the direction and rough magnitude of the improvement
is defensible, even though the two figures were not captured under identical load.

## Full gating suite: final green confirmation

- `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" -n 4 -q --timeout=300 --timeout-method=thread`: **2224 passed, 1 skipped, 2 warnings** (retry run; 0 failures).
- `pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable and not development" -q --timeout=300 --timeout-method=thread`: **9 passed, 2688 deselected**.
- `pytest tests/packaging/ -v -m "packaging and not unstable and not development"`: **121 passed, 4 skipped, 2 deselected**; `test_generate_then_execute[bimodal]` and `test_generate_then_execute_cp1252[bimodal]` confirmed not collected.
- `pytest tests/ci/ -v`: **167 passed** (the full CI-wiring contract suite, including the extended `test_unstable_deselection_wiring.py`, the widened `test_development_marker_application.py`, and the new `test_gating_selection_bimodal_decoupling.py`).
