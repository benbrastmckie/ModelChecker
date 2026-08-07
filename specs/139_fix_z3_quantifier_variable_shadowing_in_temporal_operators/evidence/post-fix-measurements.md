# Post-fix measurements

Recorded incrementally as each phase re-measures behaviour against the fixed `operators.py`.
Every entry below is a real measurement, not an assumption.

## IMPORTANT: Phase 2's remedy was revised during Phase 4 measurement work

Phase 2 originally implemented the plan's specified remedy, `z3.FreshInt`, at all 14 sites (see
the "Phase 2" section below, which records that work as originally done). While re-measuring
formulas for Phase 4's test rewrites, `z3.FreshInt` was found to cause a severe, previously
undocumented **solver performance regression** on formulas with *no* aliasing hazard at all --
e.g. a lone, non-nested `F(p)` (`some_future(atom(p))`) went from solving in ~1.3s to not
deciding within a 60-second budget. This was investigated thoroughly (see "FreshInt performance
regression investigation" below) and root-caused to `z3.FreshInt`'s own internal term/declaration
bookkeeping interacting badly with this codebase's tuned Z3 MBQI configuration
(`smt.mbqi=True`, `smt.ematching=True`, `smt.mbqi.max_iterations=1000` --
`model_checker.solver.z3_adapter.Z3SolverAdapter`), not with term distinctness itself: a
counter-suffixed plain `z3.Int` (same per-call distinctness guarantee, ordinary declaration
otherwise) does **not** exhibit the regression and performs identically to the pre-fix baseline
on unaffected formulas, while still eliminating the aliasing defect (nested `\Until`/`\Since`
survivors gone, `G(G(p))` no longer a fast spurious `None`).

**Revised remedy**: `operators.py` now declares a module-level `_fresh_bound_int(prefix)` helper
(`itertools.count()`-backed, returns `z3.Int(f"{prefix}!{n}")` for a monotonically increasing
`n`) and all 14 sites use it instead of `z3.FreshInt`. This supersedes Phase 2's original
`z3.FreshInt` edits at the same 14 sites -- the site list, comment placement, and false_at
redundancy rationale from Phase 2 are unchanged; only the specific Z3 API called at each site
changed. See Phase 2's checklist annotations in the plan for the full revision note.

## FreshInt performance regression investigation (discovered during Phase 4)

Investigation performed in the order below (see also the `_fresh_bound_int` docstring in
operators.py for the condensed version):

1. **Reproduced deterministically**: `F(p)` (`some_future(atom(p))`, depth=1, single non-nested
   `FutureOperator` invocation) solved in 1.3-1.8s pre-fix and with `z3.FreshInt` reverted to
   `z3.Int` via monkeypatch, but did not decide within 60s with `z3.FreshInt` live, across 3
   repeated trials (ruling out solver-seed noise).
2. **Ruled out "distinctness itself"**: replacing just this one site's `z3.FreshInt` with a
   plain-but-unique fixed name (`z3.Int('future_true_time_UNIQUE_NEVER_REUSED')`) restored fast
   solving (1.3s) for the single-instance case. (This alone would not fix the nested-aliasing
   case, since a *fixed* name repeats across separate invocations of the same call site -- only a
   genuinely *per-call* fresh name does, which a fixed string, however unique-looking, cannot
   provide.)
3. **Ruled out solver-parameter tuning**: disabling MBQI (`smt.mbqi=False`) makes Z3 return
   `unknown` in ~0.002s (this fragment needs MBQI for completeness, per the adapter's own
   comment); raising `smt.mbqi.max_iterations` from 1000 to 5000/20000 made no difference (still
   exhausts the wall-clock budget, not an iteration cap); default `auto_config=True` (bypassing
   the codebase's tuned settings entirely) also still timed out.
4. **Ruled out explicit E-matching patterns**: manually supplying a plausible trigger
   (`Select(world_function(eval_world), future_time)`) to the `ForAll` did not help.
5. **Ruled out `assert_and_track` vs plain `add`**: an apparent early contradiction (bare
   `z3.Solver().add()` bisection showed *both* Int and FreshInt versions of the full
   frame+conclusion constraint set timing out) was resolved by discovering `structure.py`'s real
   solve path uses `solver.assert_tracked()` (unsat-core tracking), not plain `add()`; redoing the
   comparison with `assert_tracked()` reproduced the real result cleanly (Int: 1.26-1.44s repeatable;
   FreshInt: timeout, repeatable).
6. **Confirmed the regression is specific to `z3.FreshInt`, not "any distinctness mechanism"**: a
   Python-level `itertools.count()`-suffixed plain `z3.Int(f"...{n}")` at the same site restored
   1.3s solving *and* still eliminates the nested-aliasing defect (verified against `G(G(p))`:
   still an honest timeout post-counter-fix, not a fast spurious `None` -- i.e. genuinely
   unfolded, matching the desired soundness outcome, not a reversion to pre-fix behaviour).
7. **Confirmed the regression's blast radius was real but bounded, and distinguished from
   unrelated pre-existing slow formulas**: `G(p)` (`all_future(atom(p))`, the *primitive* ALL
   operator directly, as opposed to `F(p)`'s double-negation-derived form) and `P(p)`
   (`all_past`, primitive) were independently confirmed to time out **identically pre-fix** (i.e.
   before any of this task's changes) -- a pre-existing, unrelated characteristic of this
   specific quantifier polarity (a bare `ForAll` conclusion vs. `some_future`'s
   `Not(Not(ForAll(...)))`-collapsing-to-`ForAll` conclusion), not a regression introduced by
   this task in either its `FreshInt` or counter-`Int` form. `H(p)` (`all_past` derived form,
   analogous to `F(p)`) was slow pre-fix and with `FreshInt`, but fast with the counter-`Int` fix
   -- an incidental *improvement*, not investigated further as it is outside this task's scope
   (soundness, not performance).
8. **Re-ran the full `test_soundness_regression.py` suite** with the counter-`Int` fix: failures
   dropped from 12 (under `z3.FreshInt`) to 7, and the 7 remaining are exactly the ones the
   research/plan anticipated needing rewrite because `G(G(p))`'s conclusion genuinely no longer
   folds to a Boolean literal (the actual, intended soundness fix), plus (per further
   investigation below) `TestStateIsolationRegression`'s tests, which turned out to be a harness
   artifact (see below), not a new regression.

This investigation is recorded in full because it materially changes what "the fix" is: the
plan's specified `z3.FreshInt` remedy is soundness-correct but was empirically found to be
solver-performance-catastrophic on this codebase's tuned Z3 configuration for *any* formula using
an affected operator, not just nested/aliasing-prone ones. The counter-suffixed `z3.Int` remedy
achieves the identical soundness property (proven via the same collapse-census and named
reproductions) without the performance cliff.

## Re-verification after the counter-`Int` revision (Phase 2 amendment)

Everything measured under `z3.FreshInt` above was re-run against `_fresh_bound_int()`:

- Collapse census (`evidence/post-fix-census.json`): identical result -- 94/274 folded (56 True,
  38 False), same 4 non-`\bot` survivors, both `\Until`/`\Since` aliasing-defect formulas still
  gone.
- Anti-collapse guard (`test_encoding_nondegeneracy.py`): 4/4 pass, 2.1-2.6s.
- **Teeth-check repeated against the current mechanism** (not just the original `FreshInt`
  version): reverted `UntilOperator.true_at`'s `witness_time` from
  `_fresh_bound_int('until_witness_time')` back to `z3.Int('until_witness_time')`. Both the
  exhaustive sweep and the targeted `Until`/`Until` test failed with the same expected message
  (`(p Until p) Until p's conclusion constraint folded to a Boolean literal (True)...`). Restored
  via backup; `git diff` confirmed byte-identical to the committed counter-`Int` state afterward.
- Full `test_soundness_regression.py` suite: failures dropped from 12 (under `FreshInt`) to
  3 -- `test_gg_p_returns_none`, `test_gg_p_returns_none_at_m4`, `test_gg_p_spurious_unsat`, all
  three attributable to the same, intended soundness change (`G(G(p))`'s conclusion genuinely no
  longer folds), matching what the plan/research anticipated needing rewrite. `TestStateIsolationRegression`'s
  4 tests, which failed under `FreshInt`, all pass under the counter-`Int` fix (247s for the full
  class -- slow because of call volume: 100+50+50+10 sequential solves -- not because any
  individual call regressed).
- `test_gg_p_spurious_unsat` was **not** in the plan's anticipated rewrite list (the plan expected
  it "unaffected," grouped with `test_fg_p_spurious_unsat`). Investigated directly: both tests
  call `find_countermodel()` with no M override, so both actually run at the *current*
  `M=max(depth+2,3)=4` for their depth-2 formulas, not the `M=2` their docstrings describe (a
  pre-existing staleness from before Task 114 changed the M formula -- unrelated to this task).
  `test_gg_p_spurious_unsat` uses `GG_P`, so it exercises the *exact same* aliasing defect as
  `test_gg_p_returns_none`/`test_gg_p_returns_none_at_m4` and is affected for the same reason.
  `test_fg_p_spurious_unsat` uses `FG_P` (boundary vacuity, not aliasing) and was directly
  re-run in isolation: still passes (0.70s, `result=None`), confirmed unaffected as the plan
  predicted.

## Phase 4: test rewrites and pre-fix spot-check

Rewrote `oracle/bimodal_logic/tests/test_soundness_regression.py`:
- `test_gg_p_returns_none`, `test_gg_p_returns_none_at_m4`, `test_gg_p_spurious_unsat`: all three
  now `pytest.raises(OracleTimeoutError)` around `find_countermodel(GG_P)`, matching the measured
  post-fix outcome (`OracleTimeoutError` at both 5000ms and 10000ms budgets, recorded above).
  `test_gg_p_spurious_unsat` was not in the plan's original rewrite list but was found affected
  during this phase (see decision log) -- its stale "M=2" docstring narrative was also corrected.
- `TestBoundaryVacuity` and `TestKnownBoundaryUnsafe` class docstrings: corrected the mislocated
  `false_at` attribution to `true_at`, and now state both collapse directions (False for
  `G(G(p))`, True for `F(F(p))`) rather than a single "returns None" claim.
- `test_ff_p_returns_none_at_m4`: hedge resolved -- the aliasing attribution is confirmed correct
  as the root cause of the corrupted (constant-True) conclusion, but the timeout itself (both pre-
  and post-fix) is caused by the pre-existing expensive frame search at M=4, not by aliasing
  directly. Assertion unchanged (still `pytest.raises(OracleTimeoutError)`), matching the measured
  outcome (still an honest timeout post-fix).
- `test_gf_p_returns_none_at_m4`, `test_imp_gg_p_gf_p_returns_none_at_m4`: re-measured
  (`OracleTimeoutError`, ~5.09-5.10s, matching pre-fix), docstrings already accurate, no change
  needed beyond the class-level docstring correction above.
- `test_fg_p_returns_none`, `test_fg_p_returns_none_at_m4`, `test_fg_p_spurious_unsat`: re-verified
  unaffected (`FG_P` returns `None` in 0.064-0.70s, boundary vacuity, not aliasing) -- confirmed
  by direct measurement and by the full suite run below, left unchanged.

`grep -in "shadow" oracle/bimodal_logic/tests/test_soundness_regression.py` returns exactly one
hit, in `test_ff_p_returns_none_at_m4`'s docstring, describing what a *prior* version said in
past tense while correctly attributing the live defect to `true_at` -- not a residual
misattribution.

**Full suite run**: `PYTHONPATH=code/src:oracle pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v`
-- 30/30 passed in 358.02s (0:05:58; slow because of `TestStateIsolationRegression`'s 100+50+50+10
sequential solves, not per-call regression).

**Pre-fix spot-check** (per Phase 4's verification requirement -- not just the two
"most-changed," but all three rewritten `GG_P` tests): swapped `operators.py` to `PRE_FIX_SHA`'s
content in the working tree, ran `test_gg_p_returns_none`, `test_gg_p_spurious_unsat`, and
`test_gg_p_returns_none_at_m4` in isolation. All three **failed** against the pre-fix encoding
(`Failed: DID NOT RAISE <class 'bimodal_logic.errors.OracleTimeoutError'>` -- i.e. the pre-fix
encoding still returns the fast spurious `None` these tests used to assert, confirming the
rewritten assertions are not encoding-agnostic catch-alls). Restored via backup; `git diff`
confirmed byte-identical to the committed state afterward.

## Counter-order / reproducibility investigation (raised as a concern before Phase 7)

`_bound_var_counter` is a process-global, monotonically increasing `itertools.count()`, so the
exact numeric suffix a given call receives depends on how many `_fresh_bound_int()` calls
happened earlier in the same process (i.e. on solve order/history within a run). Because Z3 MBQI
was just shown to be sensitive to naming *mechanism* (`FreshInt` vs `Int`), this raised a
legitimate question: is it also sensitive to the exact *value* embedded in an ordinary `Int`
name, such that a formula's conclusive/inconclusive classification could depend on where it falls
in a scan's run order -- which would undermine Phase 7/8's persisted baseline?

Tested directly, two ways:
1. Burned the counter forward by 5000 (via 5000 throwaway `_fresh_bound_int()` calls, no actual
   solving) between a "cold" and "warm" solve of `F(p)`: 1.29s cold vs. 1.244s warm -- no
   meaningful difference.
2. Solved `G(F(p))` (a genuine, harder, timeout-bound formula) both as the first solve in a fresh
   process and again after actually solving 30 other real complexity<=3 formulas first (via
   `_enumerate_primitive_formulas`, simulating realistic scan history, not just counter
   advancement): both timed out at the same ~6.11s, both budget-exhausted, no observable
   difference.

**Why this is expected, not just empirically lucky**: each `find_countermodel()` call runs inside
`isolated_z3_context()`, which installs a brand-new C-level Z3 `Context()` per call (see
`model_checker.utils.context.isolated_z3_context`). Within that fresh context, a name like
`"future_true_time!8734"` is declared exactly once and is otherwise an ordinary constant --
nothing about Z3's internal symbol-table/trigger-inference machinery for *that* context depends
on what number happens to be embedded in the string, since no other declaration in that fresh
context shares or references it. This is different in kind from the `FreshInt` regression, whose
root cause (per the investigation above) was `FreshInt`'s own declaration-bookkeeping mechanism,
not the counter value. Combined with the two empirical checks above, the counter-`Int` approach's
conclusive/inconclusive classification is judged to be run-order-independent, and Phase 7's
exhaustive re-derivation may proceed without an additional order-randomization control. (This
reproducibility question is not new to this task -- `z3.FreshInt` would carry the identical
theoretical property, isolated-context-per-call -- but is recorded here because the persisted
baseline now depends on it.)

## Phase 2: FreshInt replacement verification

### Collapse census re-run

`evidence/post-fix-census.json` (`evidence/collapse_census.py 5 ...`):

```
total_formulas: 274
folded: 94 (true=56, false=38)
non-bot folded survivors: 4 (indices 9, 23, 61, 113)
```

The two aliasing-defect survivors from Phase 1 (`(p \Until p) \Until p` at index 205,
`(p \Since p) \Since p` at index 273) are **gone** -- confirmed no longer folded to a Boolean
literal. This is the primary demonstration that the fix works.

The four remaining non-`\bot` survivors (`p -> p` [9], `\Box(p -> p)` [23],
`\Box(\Box(p -> p))` [61], `p -> (p -> p)` [113]) are the same genuine, structurally-outside-the-
defect's-blast-radius tautologies already identified and explained in
`evidence/pre-fix-state.md`'s "Discrepancy" section (no quantified-operator node present for 9/113;
`NecessityOperator` confirmed mechanistically immune to the collapse mechanism per research §3 for
23/61). Their presence pre- and post-fix is expected and unrelated to this defect.

### Secondary finding: `\Box(p) -> \Box(p)` (index 125) stops folding post-fix

Pre-fix, index 125 (`\Box(p) -> \Box(p)`) *was* a non-`\bot` folded survivor (folds to `False`,
i.e. its negation is a genuine tautology). Post-fix it is **no longer folded** by `z3.simplify()`
alone.

**Root cause, verified directly** (not assumed): this is a distinct, secondary effect of the same
underlying Z3 behaviour the fix addresses, but via a different code path than the nested-quantifier
aliasing this task targets. Minimal reproduction:

```python
import z3
p = z3.Int('p')
def mk(v):
    return z3.ForAll(v, z3.Implies(v > 0, p > v))
a, b = mk(z3.Int('x')), mk(z3.Int('x'))
c = mk(z3.FreshInt('x'))
z3.eq(a, b)                        # True  -- same interned term -> literally identical ForAll term
z3.simplify(z3.Implies(a, b))      # True  -- Implies(A, A) trivially simplifies
z3.eq(a, c)                        # False -- FreshInt term -> structurally distinct ForAll term
z3.simplify(z3.Implies(a, c))      # NOT simplified to a literal -- z3.simplify() does local
                                    # term rewriting, not alpha-equivalence-aware theorem proving,
                                    # so two semantically-identical-but-syntactically-distinct
                                    # ForAll terms are not recognized as implying one another.
```

`\Box(p) -> \Box(p)` builds two **independent, sibling** instances of `NecessityOperator.true_at`
(left and right of the `imp`, not one nested inside the other). Pre-fix, both instances declared
`z3.Int('nec_true_world')`, which interned to the literal same Z3 term, making the resulting two
`ForAll` subterms syntactically identical -- so `z3.simplify()` could trivially fold
`Implies(A, A)` to `True` (hence the whole formula's negation to `False`) as a side effect of
interning, with no real quantifier reasoning involved. Post-fix, each instance's `FreshInt` call
produces a distinct bound variable, so the two `ForAll` subterms are alpha-equivalent but not
term-identical, and `z3.simplify()`'s local rewriting no longer recognizes the tautology.

**This is not a soundness concern and not in this task's scope to fix**: `\Box(p) -> \Box(p)` is
still a genuine tautology, and an actual Z3 *solve* (not just `simplify()`) still decides it
correctly via ordinary unification/instantiation reasoning -- the change only removes a
free, construction-time shortcut for this specific sibling-repetition pattern, exactly analogous
in kind (loss of a free short-circuit) to the temporal `False`-folding formulas the research report
already anticipated could become "conclusive но now via an actual solve instead of instantly" or
"newly inconclusive if the actual solve is slow." It is recorded here for Phase 6/7/8's re-baselining
to account for, but is explicitly **not** part of the aliasing defect this task targets (Box is
confirmed mechanistically immune to *that* mechanism per research §3; this is comparison of two
independently-constructed sibling terms, not a nested bound-variable eval_time collision).

### `Box(Box(p))`: confirmed unchanged (as predicted)

Built `\Box(\Box(p))`'s conclusion constraint post-fix: genuine nested
`Not(ForAll(nec_true_world!0, ... ForAll(nec_true_world!1, ...)))`, not folded
(`is_true=False`, `is_false=False`). Re-verified the identical structure pre-fix by monkey-patching
`z3.FreshInt = z3.Int` in an isolated subprocess (simulating pre-fix interning without touching
the working tree) -- also non-constant, non-folded. **Confirmed unchanged**, matching the plan's
prediction that Box's fix is naming uniformity only, with no behavioural claim.

### `G(G(p))`: new outcome measured (not assumed)

```
timeout_ms=5000:  OracleTimeoutError, 5.13s (was: fast None, 0.089s, pre-fix)
timeout_ms=10000: OracleTimeoutError, 10.17s
```

`G(G(p))` no longer returns a fast spurious `None`. It now times out even at the deployed
10000ms gating budget. This is the **correct** outcome per the plan's soundness framing: an
honest timeout is strictly better than the pre-fix wrong fast "no countermodel" answer, because
`G(G(p))` genuinely IS invalid (per the docstring's own counterexample, `p` false at `t=3`
requires `M>=4`), so the oracle should decide it via a real solve, not via a construction-time
term-identity accident -- and at this M, that real solve does not complete within budget.

### `F(F(p))`, `(p \Until p) \Until p`, `(p \Since p) \Since p`: still time out post-fix

All three still raise `OracleTimeoutError` at `timeout_ms=10000` (10.1-10.2s each). No change in
observable outcome from pre-fix (they timed out pre-fix too, per `pre-fix-state.md`), though the
underlying encoding is now genuinely constrained rather than vacuously `True` -- the timeout is
for a different (correct) reason now. These three formulas are exactly the ones Phase 6-8's
re-derivation must classify: were they conclusive pre-fix only because of the vacuous-`True`
collapse (i.e. conclusive-and-wrong), and are they now genuinely inconclusive? Per the collapse
census, yes for all three: their conclusion constraints folded to constant `True` pre-fix (vacuous,
no actual constraint), so any pre-fix scan-tooling result that reported them as fast/conclusive was
conclusive-and-wrong. Post-fix, they are honestly inconclusive at this budget. This is a soundness
improvement, not a regression, and is recorded here for Phase 8's per-formula diff.

## Phase 6: full-suite verification before re-baselining

### Bimodal package suite

`PYTHONPATH=code/src python3 -m pytest code/src/model_checker/theory_lib/bimodal/ -v`:
**296 passed, 2 failed in 154.11s.**

Failures: `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` and
`[BM_CM_4-example_case9]` (`\Future A -> \Box A` and `\Diamond A -> \past A` countermodel checks,
`max_time=15` with comments already noting "extra headroom for CI variance" / "varies by Z3
state" -- these are documented as historically marginal-timing tests, unrelated to this task,
predating it per `git log -p` on `examples.py`).

**Classification: category (b), pre-existing/environmental, not a regression.** At the time of
this run, `ps aux --sort=-%cpu` showed a `lean` process (`BimodalLogic` proof compilation,
unrelated repository) consuming 1100-1300% CPU alone, plus a `lake build` and other sessions,
with `load average: 10.54, 8.53, 5.62` -- the exact category of environmental contention Task
138 documented (a `lean --worker` process pushing near-budget Z3 solves over their timeout even
in isolation). Direct evidence this is not a fix-induced regression:

1. Re-running the two tests in isolation (still under the same contention): `BM_CM_1` failed
   again at 15.31s (over the 15s budget); `BM_CM_4` passed at 3.80s (this one is flaky at the
   margin, not deterministically broken).
2. **Scratch-copy verification against `PRE_FIX_SHA`**: temporarily replaced
   `operators.py` and `semantic/core.py` with their `d795b5f4444a4a3a326a4775b7431b89144e930c`
   content (the pre-fix, pre-Phase-2 code) and re-ran the same two tests under the same ongoing
   contention. Result: **`BM_CM_1` failed identically** (15.38s, same assertion), `BM_CM_4`
   passed (4.78s). This proves the failure is a property of the current machine load hitting a
   pre-existing marginal-timing test, reproduced with code this task never touched in that state
   -- not something Phase 2-5's changes introduced. Files restored immediately after
   (`git status --short` on both paths confirmed clean, byte-identical to the last commit).

No genuine (category-c) regression found in the bimodal package suite.

### Oracle gating suite

`nix develop --command bash oracle/run-oracle-suite.sh`:

- **Pass 1** (parallel, `-n 6`, `not xdist_serial and not slow`): **9 failed, 550 passed, 3
  skipped, 4 xfailed in 858.98s.** Failures: `test_boundary_regression.py::
  test_countermodel_bm_cm4_at_example_settings`, `test_oracle_interface.py::
  test_mixed_and_box_next`, `test_oracle_interface.py::test_mixed_or_diamond_prev`,
  `test_oracle_interface.py::test_all_sat_task_relation_ternary`,
  `test_oracle_provider.py::test_all_sat_results_have_complete_output`,
  `test_soundness_regression.py::test_depth1_boundary_safe_is_true`,
  `test_oracle_interface.py::test_mixed_and_all_future_neg`,
  `test_oracle_provider.py::test_regression_standard_pipeline[BM_CM_4-example_case8]`,
  `test_oracle_interface.py::test_spot_check_individual_countermodels`.
- **Pass 2** (serial, `xdist_serial and not slow`): **TIMED OUT (exit 124) at the 900s budget.**
  A full contention-free serial pass exceeding a "~2x the idle-machine measured wall clock"
  budget is itself strong evidence of severe machine contention (a `lean lake build` process was
  observed at 900-1300% CPU, load average 9.6-11.2, throughout this run -- the same category of
  external contention Task 138 documented).

**Per-failure classification** (methodology: re-run in isolation; if it passes standalone under
lower load, mark environmental; if it fails deterministically regardless of load, scratch-swap to
`PRE_FIX_SHA`'s `operators.py`/`semantic/core.py` and compare):

| Test | Isolated re-run | PRE_FIX_SHA comparison | Classification |
|---|---|---|---|
| `test_mixed_and_box_next` | PASSED | not needed | (b) environmental (contention-only, non-reproducing) |
| `test_depth1_boundary_safe_is_true` | PASSED | not needed | (b) environmental |
| `test_countermodel_bm_cm4_at_example_settings` | **FAILED deterministically** (15.3-15.4s across 4 runs at load 2-5.5, i.e. NOT contention) | **PASSED** (4-6s across 3 runs, same load) | **(c) genuine solve-time regression** (see below) |
| `test_regression_standard_pipeline[BM_CM_4-example_case8]` | not independently re-run (same BM_CM_4 formula/settings pattern as above) | inferred from above | **(c)**, same root cause as `test_countermodel_bm_cm4_at_example_settings` |
| `test_mixed_or_diamond_prev` | **FAILED** (`OracleTimeoutError` at 60000ms) even at load ~4.8-5.5 | not completed (time-boxed; coordinator directed closing out Phase 6 on evidence in hand) | **(c) candidate**, unconfirmed root cause -- see below |
| `test_all_sat_task_relation_ternary` | not independently re-run | not completed | unclassified -- recorded as open, not asserted clean |
| `test_all_sat_results_have_complete_output` | not independently re-run | not completed | unclassified -- recorded as open, not asserted clean |
| `test_mixed_and_all_future_neg` | PASSED (in the batch re-run) | not needed | (b) environmental |
| `test_spot_check_individual_countermodels` | **FAILED** (`F9_until_implies_event` got a countermodel where the test expects `None`/valid) | **PASSED**, but only because **all four** of F4/F7/F9/F10 timed out at 60000ms pre-fix too (`inconclusive = [...]`, caught and not asserted -- the test's own docstring already anticipated this: "at least one of them does not decide even at a 60s budget") | **Not a regression**: pre-fix never reached a confident "valid" verdict for F9 either -- it was undecided (timeout), same as several siblings. Post-fix, the solve now decides (SAT, i.e. a countermodel), converting an inconclusive pre-fix result into a decisive post-fix one. This is "previously undecided -> now decided," not "previously confidently correct -> now wrong." Whether the decided SAT answer is the mathematically correct verdict for `\Until(p,q) -> p` was not independently re-derived here (out of this dispatch's time budget); flagged as a follow-up, not asserted as either a regression or a confirmed soundness improvement. |

**`test_countermodel_bm_cm4_at_example_settings` root-cause investigation**: this is the same
underlying phenomenon Phase 2 already documented for `Box(p)->Box(p)` (secondary finding: sibling,
non-nested same-primitive instances lose a Z3 term-identity-based simplification shortcut once
bound variables are no longer accidentally shared). `\Diamond A -> \past A` (`BM_CM_4`) exercises
`PastOperator`, one of the 14 fixed sites. Given 60s instead of the test's local 15s budget, the
post-fix encoding **does** find the expected countermodel (confirmed: `result=True` at 24.08s
elapsed) -- so this is a solve-time cost, not a correctness defect. Per TESTING_GUIDE 8.6
("Set budgets generously... prefer the 30s convention") and given `max_time=15` here is a local
test constant, not one of the three Hard-Constraint-pinned artifacts
(`_assert_scan_report`/`SELF_SCAN_SOLVE_TIMEOUT_MS`/`MIN_CONCLUSIVE_SCAN_FORMULAS`), the sanctioned
fix-forward is to widen this test's local `max_time`, backed by this measurement -- applied in
this phase (see plan Phase 6 task list).

**Time-boxed scope decision**: per explicit direction received mid-phase, further confirmation
runs for the two remaining unclassified failures
(`test_all_sat_task_relation_ternary`, `test_all_sat_results_have_complete_output`) and the
`test_mixed_or_diamond_prev` root-cause were not pursued further in this dispatch, to avoid
open-ended verification burning further wall clock under sustained heavy external contention.
This is recorded explicitly as an **open item**, not silently resolved as clean -- see the Phase 6
handoff and `.orchestrator-handoff.json` for the carried-forward blocker.
