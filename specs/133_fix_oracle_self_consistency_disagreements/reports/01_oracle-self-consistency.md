# Research Report: Oracle Full-Scan Self-Consistency Disagreements

## Summary

`test_complexity_5_scan_self_consistent` does not demonstrate a correctness defect in the Z3
oracle. It fails because `Z3OracleProvider.find_countermodel()` reports a blown solver budget
identically to a genuine "no countermodel" (UNSAT) result — the same timeout/UNSAT conflation
already root-caused in three prior tasks of this effort. Direct instrumentation of the
complexity<=5 self-comparison scan (274 formulas, each solved twice) reproduced exactly one
disagreement, and that disagreement's own solve-time data settles the question outright: one of
the two independent solves for the same formula completed at 4.7796s (under the 5.0s budget,
returned a model), the other hit the budget at 5.0003s (timed out, and the timeout was reported
as UNSAT). The oracle agreed with itself on the actual Z3 outcome; only the budget-vs-timeout
boundary differed between the two calls. Recommended fix: make timeout status explicit at
`find_countermodel`'s return value (never silently equal to a semantic UNSAT), and treat that as
its own follow-up task rather than doing it inside this one, given the compounding evidence below
that this single conflation point has now cost four separate triage efforts.

## 1. What the self-comparison compares, and where

- **Test**: `oracle/bimodal_logic/tests/test_cross_oracle_differential.py:1365`
  (`TestFullScanReport.test_complexity_5_scan_self_consistent`).
- **Formula set**: `_enumerate_primitive_formulas(5, ["p"])`
  (`test_cross_oracle_differential.py:146`) — all primitive-tag formulas at structural
  complexity <=5 over a single atom `p`. This resolves to **274 formulas**.
- **The comparison harness**: `_generate_differential_report()`
  (`test_cross_oracle_differential.py:1176-1228`). For each formula it:
  1. Calls `ref_fn(f)` (`test_cross_oracle_differential.py:1370-1372`), which itself calls
     `self.oracle.find_countermodel(f)` and maps `None -> "UNSAT"`, non-`None -> "SAT"`.
  2. Calls `_run_differential_comparison(oracle, f, ref_result)`
     (`test_cross_oracle_differential.py:363-412`), which calls
     `oracle.find_countermodel(f)` **again**, independently, and compares its result to
     `ref_result`.
  3. Increments `disagreements` when the two do not match
     (`test_cross_oracle_differential.py:1214-1217`).
- **Net effect**: every formula in the scan is solved by Z3 **twice**, via two separate calls to
  the same `find_countermodel()` method on the same `Z3OracleProvider` instance — not once
  and compared to a precomputed reference. "Self-comparison" means literally "the same solver
  invoked twice on the same input," not "compared to a cached/fixed expected value."
- **The disagreement-recording code**: `_generate_differential_report`
  (`test_cross_oracle_differential.py:1207-1217`); the final assertion is at
  `test_cross_oracle_differential.py:1381-1383`.
- **The conflation root cause**: `Z3OracleProvider.find_countermodel()`
  (`oracle/bimodal_logic/provider.py:169-275`), specifically
  `oracle/bimodal_logic/provider.py:255`:
  ```python
  if structure.timeout or not structure.z3_model_status:
      self._semantics = None
      return None
  ```
  `structure.timeout` is `True` whenever the underlying Z3 `solver.check()` call returns
  `unknown` (see `code/src/model_checker/models/structure.py:210-260`, which treats *any*
  `UNKNOWN` result — timeout or otherwise inconclusive — as `timeout=True`, deliberately not
  trusting `reason_unknown()`'s literal text). `find_countermodel()` returns `None` for both this
  case and a genuine Z3-proved UNSAT. The oracle's public API therefore has no way to distinguish
  "this formula is valid" from "the solver ran out of time." Both `ref_fn` and
  `_run_differential_comparison` in the test file consume exactly this ambiguous `None`/non-`None`
  signal, so a timeout on either of the two calls is indistinguishable, at the assertion site,
  from a semantic verdict.
- The default budget is tight relative to this ambiguity: `find_countermodel(..., timeout_ms:
  int = 5000)` (`provider.py:173`), i.e. a 5.0s `max_time` passed through to
  `BimodalStructure`'s solver.

## 2. Direct measurement: do disagreements correlate with near-budget/timeout solves?

This is answered by direct observation, not correlation over many events, because there was
exactly one disagreement.

**Method**: a read-only instrumentation script (not a modification to any file under `oracle/`
or `code/`) re-implements `find_countermodel()`'s pipeline line-for-line but additionally
surfaces `structure.timeout`, `structure.z3_model_status`, `structure.z3_model_runtime`, and
wall-clock time for each solve, rather than collapsing both timeout and UNSAT to `None`. It ran
the full 274-formula complexity<=5 enumeration, solving each formula independently twice
(mirroring the test's own `ref_fn` + comparison-call structure), and recorded every case where
the two solves disagreed.

**Result**: 1 disagreement out of 274 formulas. The formula is `untl(bot, box(p))` (index 41 in
enumeration order):

| solve | result | `structure.timeout` | `z3_model_runtime` | wall-clock | `max_time` |
|---|---|---|---|---|---|
| A | SAT | `false` | 4.7796s | 4.8856s | 5.0s |
| B | UNSAT | **`true`** | 5.0003s | 5.1225s | 5.0s |

Solve A finished 0.2204s (about 4.4%) under budget and returned a genuine model. Solve B, on the
identical formula with identical settings (`N=2`, `M=3`, `temporal_depth=1`), ran 0.2003s longer
before Z3 gave up, tripped `structure.timeout=True`, and that timeout was reported as `UNSAT` by
`find_countermodel()`'s line 255 conflation. **1 of 1 disagreements had a timeout on exactly one
side.** The oracle's underlying Z3 solve did not produce contradictory semantic answers; one call
landed on either side of a 5-second wall-clock cliff for a formula whose true solve time sits
close to that boundary, and the API surfaced the two outcomes ("found a model" vs. "budget
exceeded") as if they were both semantic verdicts ("SAT" vs. "UNSAT").

This is the same mechanism documented for the `_KNOWN_INVALID_JSON` xfail block earlier in the
same test file (`test_cross_oracle_differential.py:770-781`, citing `provider.py:255` by name)
and the same mechanism behind the timing-variance guidance already recorded in
`code/docs/core/TESTING_GUIDE.md` section 8.6 (a single unchanged formula's measured solve time
spanning 0.69s-15.08s across repeated invocations on this machine, "roughly a 20x spread with no
change to the code under test").

## 3. Sample-count honesty: is the 1-vs-3 difference resolved?

**No, and this report does not claim otherwise.** This was one sampling run. It reproduced
exactly **1** disagreement, which happens to match the pre-refactor baseline's reported count
(1, at commit `6cfb7f48`, per `specs/127_close_oracle_suite_regression_baseline/summaries/
01_close-oracle-regression-baseline-summary.md:40-41`) rather than HEAD's previously reported
count of 3 (same summary, line 33). That match is suggestive but is **one data point**, not proof
that the count is now stable at 1, has decreased, or was never really 3. Both the 1-count and the
3-count runs are consistent with the settled mechanism above (each disagreement is a
budget-boundary event; how many formulas in a 274-formula scan land near that boundary on a given
run is a function of machine load at solve time, not of the code under test).

**What would resolve stability**: 3-5 repeated samples of this same instrumented scan, ideally
alternating with unrelated CPU load to vary contention, comparing not just the disagreement count
but which formula indices disagree each time. That was judged out of scope for this research pass
given the ~28-30 minute cost per repetition (this single run took approximately that long,
consistent with the previously measured ~31:31 serial runtime for the same scan via the ordinary,
uninstrumented test) — the mechanism itself is already settled by this one run's own timing data,
and further sampling would only add confidence about *count distribution*, not change the
diagnosis. If a downstream task wants a stability estimate, budget roughly 1.5-2.5 hours of
unattended wall-clock for 3-5 repeats.

## 4. Correcting the "Category C contention flake" misclassification

The task description asked for this to be corrected wherever recorded. Tracing it down:

- **The source disposition document does not classify this test at all.**
  `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/
  oracle-suite-disposition.md`, "Category C (resolved as contention flakes...): 7 tests"
  (lines 57-87), lists exactly 7 named tests — `TestEnrichedRoundTrip::
  test_enriched_vs_primitive_sat_agreement[some_past]`, `TestTernarySerializationAll::
  test_all_sat_task_relation_ternary`, three `TestStateIsolationRegression` tests,
  `TestGuardedCompositionality::test_nullity_with_temporal_formula_output`, and
  `TestOracleMFormulaBoundarySafe::test_oracle_m_formula_depth1_boundary_safe`. Searching that
  document for `test_complexity_5_scan_self_consistent` (or `complexity_5`/`complexity<=5`)
  returns no match. This test was never in Category C.
- **The false claim was introduced in task 127's plan.**
  `specs/127_close_oracle_suite_regression_baseline/plans/
  01_close-oracle-regression-baseline.md:40-43` states: "The two `F`s in the existing partial
  baseline decode to `test_complexity_5_scan_self_consistent` and
  `test_all_sat_task_relation_ternary`, both already documented as Category C contention flakes
  (pass in isolation)." This conflates the two: `test_all_sat_task_relation_ternary` genuinely is
  in the disposition document's Category C list; `test_complexity_5_scan_self_consistent` is not
  and never was. The same plan repeats the false premise at line 78 ("Fixing, re-marking, or
  suppressing either known contention flake. If they pass in isolation the precedent holds...").
- **The error was caught but only corrected narratively, not structurally.** Task 127's own
  summary (`specs/127_close_oracle_suite_regression_baseline/summaries/
  01_close-oracle-regression-baseline-summary.md:70-78`) explicitly states: "The plan's research
  had classified `test_complexity_5_scan_self_consistent` and `test_all_sat_task_relation_ternary`
  as 'Category C: contention flakes, pass in isolation' ... A watch list built from a single prior
  observation actively pointed away from the real failures." This is the correct diagnosis, but it
  lives only in prose inside the summary — the plan document itself
  (`01_close-oracle-regression-baseline.md:40-43,78`) was never edited to retract the false
  premise, so a future reader of the plan alone (without also reading the summary) would still
  encounter the incorrect classification as if settled. **Recommendation for whoever picks up the
  implementation task**: add a corrective note to
  `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`
  itself (not just leave the correction in the summary) pointing at this report, so the plan
  document stops being a source of the stale claim.

## 5. Recommended fix

Three options were weighed, per the task's request for a clear recommendation rather than a
survey:

- **(a) Widen this test's budget alone.** Cheapest, but does not fix the underlying API defect —
  any formula whose true solve time sits near whatever budget is chosen remains exposed to the
  same conflation, just at a different wall-clock threshold. This is a symptom patch, not a fix,
  and this exact class of bug has already reappeared four times at different budget values (this
  test's 5s default, the ternary test's earlier timeout work in task 131, the xdist contention
  case in task 132, and the "confirmed slow-solver defect" that was actually a false positive
  under six-way parallelism per the task's own framing). Widening alone would very likely need to
  be repeated again on the next machine-load spike.
- **(b) Make timeout status explicit at the comparison site (and, more fundamentally, at
  `find_countermodel`'s return contract) so a timeout can never masquerade as a semantic
  SAT/UNSAT answer.** This directly closes the defect class: `find_countermodel()` would need to
  return three-valued information (SAT / UNSAT / TIMEOUT) rather than collapsing UNSAT and
  TIMEOUT to the same `None`. Every call site that currently treats `None` as "no countermodel" —
  including this test's `ref_fn` and `_run_differential_comparison`, the `_KNOWN_INVALID_JSON`
  xfail block, and any other oracle consumer — would then be able to (and would be forced to)
  treat a timeout as inconclusive rather than as a semantic verdict.
- **(c) Both.** Widen the budget as an immediate mitigation (reduces the *frequency* of
  budget-boundary events for this specific 274-formula scan) while separately hardening the
  contract (eliminates the entire defect class going forward, independent of any specific
  budget).

**Recommendation: (c), but split across two tasks, not done together in one.** The budget widen
for this specific test is a small, low-risk, immediately actionable change scoped to this task
(e.g., raising `test_complexity_5_scan_self_consistent`'s scan to call `find_countermodel` with a
larger `timeout_ms`, consistent with the 30s convention `code/docs/core/TESTING_GUIDE.md` section
8.6 already recommends for `max_time` generally, rather than the oracle's tight 5s default).
That closes this task's immediate assertion failure. **Hardening `find_countermodel`'s contract
(option b) should be its own follow-up task**, not bundled into this one, for two reasons: (1) it
is an API-shape change to `Z3OracleProvider` that ripples into every consumer across
`oracle/bimodal_logic/tests/` (at minimum `test_cross_oracle_differential.py`'s `ref_fn`,
`_run_differential_comparison`, and the `_KNOWN_INVALID_JSON` xfail annotations, plus
`validate_self()` at `provider.py:277-295`, which has the identical `None`-collapsing pattern),
and reworking all of those call sites belongs to a scoped implementation plan of its own rather
than a side effect of fixing one test's budget; (2) the compounding evidence is now strong enough
to justify a dedicated task: four consecutive triage efforts in this line of work have each spent
significant investigation time re-discovering that a `None`/timeout ambiguity was misread as a
semantic result — a boundary flake misread as a refactor-introduced semantic regression, an xdist
failure misread as broken cross-process state isolation, a marginal test misread as a confirmed
slow-solver defect that then passed under strictly worse (six-way parallel) conditions, and now
this self-consistency test misread as a correctness defect. A dedicated task to make timeout
status explicit at the oracle's public API boundary would retire this entire recurring root cause
rather than requiring it to be re-diagnosed a fifth time.

## 6. What a downstream baseline task should expect

With this understood: the full 550-test oracle suite's only remaining failure (per
`specs/127_close_oracle_suite_regression_baseline/summaries/
01_close-oracle-regression-baseline-summary.md` and the spawn context for this task) is this test,
and it is a budget-boundary artifact of the `find_countermodel`/`structure.timeout` conflation,
not a semantic defect in either oracle. A downstream baseline-closing task can treat this test as
resolved once the budget widen (Section 5, option a) lands — it should not require re-litigating
whether the oracle disagrees with itself, since this report's direct instrumentation already
settles that question with a recorded timeout on one side of the one observed disagreement.

## Constraints observed

- **No files under `oracle/` or `code/` were modified.** All instrumentation ran from a standalone
  scratch script at
  `/tmp/claude-1000/-home-benjamin-Projects-ModelChecker/dc4644bb-00ce-4b18-b70d-06efcda75c22/scratchpad/instrument_self_consistency.py`,
  which only imports from `oracle/bimodal_logic` and `code/src/model_checker` — it does not write
  to either tree. `git status --porcelain -- oracle/ code/` after the run shows only the
  pre-existing, unrelated modifications already present in this working tree at session start
  (`code/src/model_checker/builder/tests/...`, `code/tests/...`, etc.) — none introduced by this
  research.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` (locked by another
  session) was not touched.
- No `git checkout`/`git restore`/`git stash` operations were run.
