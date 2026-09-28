# Iteration-Result Fallout Review (Phase 6)

Representative `iterate: 3` examples re-run via `./dev_cli.py` post-fix, compared against Phase
1's pre-fix captures. Same temp example files, same parameters (logos `[] |- \neg A` N=2;
exclusion `EX_CM_6` N=3 max_time=40; imposition `IM_CM_0` N=4 max_time=40).

## logos

| | Pre-fix | Post-fix |
|---|---|---|
| Models found | 1/3 | 1/3 |
| Elapsed | 0.78s | 0.44s |

**Unchanged.** `diff` between `01_pre-fix-logos-iteration.txt` and
`04_post-fix-logos-iteration.txt` shows only timing-noise and progress-bar "skipped" counter
differences -- the printed model content, the models-found count, and the final "0 isomorphic
models skipped" line are identical. At N=2 (only 2 atomic states), this argument's genuinely
distinct-up-to-isomorphism countermodel space is apparently exhausted at 1 model regardless of
whether the persistent solver is populated -- both runs converge to the same result, just
somewhat faster post-fix (less wasted work re-discovering the same orbit's members). This is the
expected outcome when the "true" answer for this example doesn't change: the fix corrects the
search's *constraint content*, not the underlying semantic fact of how many non-isomorphic
models this specific small example admits.

## exclusion

| | Pre-fix | Post-fix |
|---|---|---|
| Models found | 3/3 | 2/3 (timeout after 40s, 139 candidates checked) |
| Elapsed | ~1.2s (unconstrained, fast) | 40.51s |

**Changed -- explained, not a regression.** Pre-fix, `EX_CM_6`'s search found all 3 requested
models almost instantly because the persistent solver had **zero** real assertions (confirmed by
this task's own regression tests): any Z3-satisfiable bit assignment differing from the previous
one's difference-constraint clause counted as "a new model," regardless of whether it actually
satisfied `frame_constraints`/`model_constraints`/`premise_constraints`/`conclusion_constraints`.
Post-fix, the search must find models that genuinely satisfy those real constraints, which is a
strictly harder search -- it finds 2 within the 40s budget rather than 3. This is exactly the
risk the plan's risk table names explicitly ("A newly-constrained search finds fewer models
within `max_time`, reading as a 'regression'") and its own mitigation directs: "an
under-constrained search finding more models is not a benefit." The pre-fix "3/3" figure was not
evidence of 3 genuine models being found quickly; it was evidence of the search accepting
whatever it could reach in an unconstrained space. Model 1 and Model 2's *content* (the actual
countermodels printed) is unaffected either way, since `build_new_model_structure` independently
re-solves/verifies each candidate against the real semantics regardless of what the persistent
search solver believed.

## imposition

| | Pre-fix | Post-fix |
|---|---|---|
| Models found | 2/3 (timeout after 40s, 44 candidates checked) | 2/3 (timeout after 40s, 42 candidates checked) |

**Unchanged in outcome.** Both pre- and post-fix time out after finding 2/3 models, with a
comparable candidate-check count (44 vs. 42). `IM_CM_0`'s search was apparently already
timeout-bound regardless of persistent-solver population for this example/budget, so this
fix's effect here is negligible within the 40s window used for the baseline capture.

## Task 210's Phase 3 blocker

Per the task description's own stated expectation, with the persistent solver genuinely
populated, task 210's pin-routing fix (pins appended into `model_constraints.frame_constraints`)
is expected to make the pinned candidate satisfiable rather than UNSAT for logos and imposition,
matching exclusion's already-passing behavior. This is corroborated by an observation already
recorded in the Phase 3 handoff: `iterate/tests/integration/test_models.py::
TestGenericPinningReachesRebuiltSolve::test_rebuilt_solve_matches_pinned_values` now passes for
both `logos` and `imposition` (previously failing in the Phase 1 baseline), with no file in that
test's own territory touched by this task. This is recorded here as an expectation for that
other task to verify and act on -- not run, modified, or claimed as this task's own deliverable.

## Out-of-scope boundary check

```
git diff --name-only <base>..HEAD
```
does not list `code/src/model_checker/iterate/models.py`,
`code/src/model_checker/iterate/tests/integration/test_models.py`, or
`code/src/model_checker/theory_lib/bimodal/iterate.py`. Confirmed by direct `git diff --stat`
against each path individually (empty output for all three) at Phase 3, Phase 4, and again here.
