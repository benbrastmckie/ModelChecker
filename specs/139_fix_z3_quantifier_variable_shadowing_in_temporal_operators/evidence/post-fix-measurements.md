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
