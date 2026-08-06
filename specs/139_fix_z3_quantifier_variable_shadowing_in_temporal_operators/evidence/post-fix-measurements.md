# Post-fix measurements

Recorded incrementally as each phase re-measures behaviour against the `FreshInt`-fixed
`operators.py`. Every entry below is a real measurement, not an assumption.

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
