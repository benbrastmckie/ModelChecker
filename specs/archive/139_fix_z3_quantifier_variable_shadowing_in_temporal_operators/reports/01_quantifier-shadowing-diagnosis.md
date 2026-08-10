# Research Report: Z3 Quantifier Variable Shadowing in Temporal/Modal Operators

**Task**: 139 — fix_z3_quantifier_variable_shadowing_in_temporal_operators
**Scope**: `oracle/bimodal_logic/`, `code/src/model_checker/theory_lib/bimodal/`

## 1. Summary of findings

1. The shadowing diagnosis in the test docstrings is **confirmed real**, but its stated
   mechanism location is **wrong**: the docstrings blame each operator's own `false_at`
   method. Those `false_at` methods are **dead code** — the live evaluation path never
   calls them. The actual defect lives in the `true_at` methods, reached indirectly
   through `BimodalSemantics.false_at = Not(true_at(...))`.
2. The bug is a **Z3 constant-interning aliasing bug**, not scoping/shadowing in the
   classical lexical sense. `z3.Int('name')` returns the *same* underlying Z3 term for
   every call with that `name` (verified empirically). When a quantified operator's
   `true_at` recurses into an argument that is *itself* an instance of the same
   primitive operator, it passes its own not-yet-bound bound-variable term down as the
   recursive call's `eval_time`. The inner call then declares a "fresh" variable using
   the **same fixed string name**, which resolves to the identical Z3 term, producing a
   syntactically self-referential comparison (`x < x`, always `False`) at construction
   time, before either quantifier is closed.
3. This affects `FutureOperator`, `PastOperator`, `UntilOperator`, `SinceOperator`
   whenever a **directly-nested instance of an operator whose primitive expansion
   reuses the same bound-variable name** occurs in a live-evaluated position (`event`
   position always fully collapses; `guard` position partially corrupts without fully
   collapsing). `NecessityOperator` (`\Box`) shares the same *naming* defect (`true_at`
   and `false_at` both hard-code `'nec_true_world'`) but is **empirically immune** to
   the collapse mechanism, because it never compares its bound variable against the
   propagated `eval_time`.
4. **Resolves the task's open question**: G(G(p)) returns fast `None` and F(F(p))
   raises `OracleTimeoutError` under the *identical* aliasing bug. The direction the
   corrupted conclusion collapses to (`False` vs. `True`) — not whether the bug is
   present — determines the observable symptom. `False` short-circuits the whole
   solve instantly (any single `False` conjunct makes the assertion set trivially
   UNSAT). `True` is vacuous — it adds no constraint — so the solver falls through to
   deciding raw frame-constraint satisfiability at that `M`, which is independently
   expensive at `M=4` and times out. The shadowing docstrings are not stale; they are
   incomplete. Both failure directions come from one defect.
5. Found clean, minimal, non-`\bot`-based reproductions of the same collapse in the
   **primitive** operator set (`\Until`, `\Since`), directly relevant to Task 137's 13
   "resolved-and-wrong" MC/BimodalHarness divergences: `(p \Until p) \Until p` and
   `(p \Since p) \Since p` both collapse their conclusion constraint to the Z3 constant
   `True`. Confirms the task description's suspicion that 139 and 137 are linked, not
   independent — recommend investigating 137's 13 formulas for this exact pattern
   before/alongside the 139 fix.
6. Fix recommendation: replace every fixed-string `z3.Int('name')` bound-variable
   declaration in `operators.py` with `z3.FreshInt('name')` (confirmed available on
   both the `z3` and `cvc5.pythonic` backends via `z3_shim`). Apply to `true_at`
   (live) and `false_at` (dead, but latent — should not be left as a landmine) in all
   affected operators.
7. Re-measurement of the complexity-5 sweep must happen with the actual scan tooling,
   not be assumed to move in one direction — evidence below shows the fix could
   plausibly *decrease* naive "fast decisive" counts (removing free short-circuits) as
   well as increase them (restoring genuine constraints that let Z3 prune faster than
   an unconstrained frame-satisfiability search). The `known_conclusive_complexity5.json`
   baseline (103/274) and `MIN_CONCLUSIVE_GATING_FORMULAS=100` will need re-derivation
   regardless of which direction the count moves, because the *set* of which specific
   formulas are conclusive will change, not just the count.

## 2. The actual dispatch path (correcting the docstrings)

`code/src/model_checker/theory_lib/bimodal/semantic/core.py:1583-1636`:

```python
def true_at(self, sentence, eval_point):
    ...
    operator = sentence.operator
    arguments = sentence.arguments or ()
    return operator.true_at(*arguments, eval_point)   # <-- only true_at is dispatched

def false_at(self, sentence, eval_point):
    return z3.Not(self.true_at(sentence, eval_point))  # <-- never calls operator.false_at
```

`ModelConstraints.conclusion_behavior = lambda conclusion: semantics.false_at(conclusion, main_point)`
(`core.py:1532`) is the query the oracle actually asks Z3 to satisfy. Because
`BimodalSemantics.false_at` is unconditionally `Not(true_at(...))`, and `true_at`'s
recursive case dispatches only to `operator.true_at`, **no `operator.false_at` method
in `operators.py` is ever reachable from `find_countermodel()`**. I grepped the whole
`bimodal` package for direct calls to `.false_at(` and `operator.false_at` and found
none outside `semantics.false_at` itself and the dead methods calling each other.

This means `FutureOperator.false_at` (operators.py:568-593, the exact method the test
docstrings cite by name, "both nested G operators use the same Z3 variable name...in
false_at") is dead code. The true live-and-buggy code is `FutureOperator.true_at`
(operators.py:548-566), reached twice for `G(G(p))` via two `true_at` recursions, with
the outer's own `Not()`-negated result later producing the observed `false_at` value.
Same structure applies to `PastOperator`, `UntilOperator`, `SinceOperator`: their own
`false_at` methods (operators.py:744-769, 953-1004, 1181-1231) are dead; the bug lives
in their `true_at` methods (operators.py:717-742, 907-951, 1135-1179).

**Planning implication**: the fix must target `true_at` methods to change live
behavior. `false_at` methods should still be fixed (same `FreshInt` treatment) so they
are not a silent trap if a future optimization ever wires `operator.false_at` in
directly (e.g., to avoid the double-negation blowup this defect also causes — see
§4). Consider whether to keep or delete the dead `false_at` methods entirely,
consistent with the project's "no backwards compatibility / clean breaks" principle;
this is a judgment call for the planner, not resolved by this research.

## 3. Confirmed mechanism (traced and empirically verified)

`FutureOperator.true_at` (operators.py:548-566):

```python
future_time = z3.Int('future_true_time')
return semantics.ForAllTime(
    eval_world, future_time,
    z3.Implies(eval_time < future_time,
               semantics.true_at(argument, {"world": eval_world, "time": future_time}))
)
```

For `G(G(p))`, the outer call builds its body **before** its own `ForAll` is
constructed (Python evaluates arguments bottom-up). It passes its own not-yet-bound
`future_time` (call it `X`) down as `eval_time` for the recursive
`semantics.true_at(argument, {"time": X})` call. That recursion re-enters
`FutureOperator.true_at`, whose *own* `eval_time` is now `X`, and which creates its
own `future_time = z3.Int('future_true_time')`. Because Z3 interns `Int` constants by
`(name, sort)`, this inner `future_time` **is the same term as `X`**
(`z3.eq(a, b) == True`, verified — see §5). The inner body becomes
`Implies(X < X, ...)`, and Z3's own `ForAll(...)` constructor closes over `X` at that
point (before the outer `ForAll` is built), converting it to a bound reference local to
the *inner* quantifier. `X < X` is a term-level tautology-breaker (`t < t → False`)
that Z3's simplifier collapses independent of quantification, so the inner
`ForAll(X, Implies(valid(X), Implies(False, ...)))` reduces to a constant `True`,
propagating up and constant-folding the *entire* nested expression regardless of `p`.

`Box`/`NecessityOperator.true_at` (operators.py:387-417) shares the same fixed-name
hazard (`'nec_true_world'`, also reused verbatim in `false_at` at line 437 — a
first naming defect on its own) but is not vulnerable to *this* mechanism: it never
compares its own bound `other_world` against `eval_time`; it only threads
`other_world` down as the new `"world"` key, and the recursive Box call underneath
never reads `eval_point["world"]` at all (Box quantifies over all worlds
unconditionally, ignoring the caller's world). Traced by hand and confirmed by direct
`z3.simplify()` on `Box(Box(p))`'s conclusion constraint: it produces a genuine nested
`ForAll(...ForAll(...))` term, not a collapsed constant (§5).

## 4. Why G(G(p)) is fast and F(F(p)) times out — same bug, opposite collapse direction

`some_future` (`\future`, "F") is a `DefinedOperator`:
`derived_definition(arg) = [Negation, [FutureOperator, [Negation, arg]]]`
(operators.py:1505-1506). `syntactic/sentence.py`'s `derive_type()` fully expands this
**before** any Z3 term is built, so `F(F(p))` becomes the fully-primitive tree
`neg(Future(neg(neg(Future(neg(p))))))` — still two directly-nested `FutureOperator`
instances, connected through the outer's not-yet-bound var exactly as in `G(G(p))`.
The self-comparison collapse fires identically. The difference is parity: the extra
negations around `F(F(p))`'s embedded `Future`s flip the collapsed value from `False`
(as in `G(G(p))`) to `True`.

Direct verification (`oracle/bimodal_logic` on the current branch,
`Z3OracleProvider().find_countermodel(...)`, default `timeout_ms=5000`, M computed as
`max(depth+2,3)`):

| Formula | Result | Time | `z3.simplify()` of `conclusion_constraints[0]` |
|---|---|---|---|
| `G(G(p))` | `None` (fast) | 0.05s | literal `False` |
| `F(F(p))` | `OracleTimeoutError` | 5.09s (budget exhausted) | literal `True` |
| `G(F(p))` | (per test suite) `OracleTimeoutError` | — | non-constant, corrupted (no longer references `p`; collapses to a bound-only comparison — see below) |
| `F(G(p))` | `None` (fast) | — | non-constant, but structurally the genuine boundary-vacuity expression (empty-domain ForAll, correctly independent of `p`) — **not** a shadowing artifact |
| `Box(Box(p))` | n/a (not scanned) | — | non-constant, genuine nested quantifier — **not** affected by shadowing |

Mechanism for the asymmetry: a conclusion constraint that is a literal Z3 `False`
makes the entire assertion set (`frame_constraints + model_constraints +
conclusion_constraints`) trivially UNSAT via a single-conjunct short-circuit — Z3's
preprocessing recognizes this near-instantly, without ever needing to explore the
(expensive, at `M=4`) frame/abundance constraints. A conclusion constraint that is a
literal `True` contributes **no information**: the solver must decide raw
frame-constraint satisfiability at that `M` from scratch, which `provider.py`'s own
module docstring already documents as expensive ("`task_restriction`...causes solver
timeouts on examples requiring more than 3 worlds with M>=3, because it introduces a
nested ForAll/Exists quantifier alternation that MBQI handles poorly"). `G(F(p))`
undergoes only **one** level of the collapse (only the inner, F-embedded `Future` is
double-named against the outer G's bound var; G's own comparison against the genuine
top-level `main_time` is undisturbed), producing a partially-corrupted, non-constant,
non-`p`-dependent constraint rather than a full collapse — still wrong (it does not
encode "G(F(p))" at all), but not decisive either way, so it also falls through to the
same expensive frame search and times out.

**Conclusion for the "is the docstring stale?" question**: no — the diagnosis that
this is a Z3 quantifier variable aliasing defect is correct and now mechanistically
confirmed for both directions. What was stale is the assumption that the bug always
manifests as a fast `None`. It does not: whether a given nested formula times out or
resolves fast-and-wrong depends on which Boolean constant (or partial corruption) the
aliasing happens to produce, which depends on the parity of negations introduced by
however the formula reaches the nested same-operator adjacency (direct primitive
nesting for `\Future`/`\Past`, or through a `DefinedOperator`'s expansion for
`\future`/`\past`).

## 5. Reproduction commands (for the implementer to re-verify after the fix)

```bash
PYTHONPATH=code/src:oracle python3 -c "
from bimodal_logic.provider import Z3OracleProvider
from bimodal_logic.errors import OracleTimeoutError
GG_P = {'tag':'all_future','arg':{'tag':'all_future','arg':{'tag':'atom','name':'p'}}}
FF_P = {'tag':'some_future','arg':{'tag':'some_future','arg':{'tag':'atom','name':'p'}}}
provider = Z3OracleProvider()
print('GG_P:', provider.find_countermodel(GG_P))   # currently None, fast
try:
    print('FF_P:', provider.find_countermodel(FF_P))
except OracleTimeoutError as e:
    print('FF_P: TIMEOUT', e)                      # currently times out
"
```

`z3.Int` interning check (used to justify the "same term" claim):

```bash
python3 -c "
import z3
x1, x2 = z3.Int('x'), z3.Int('x')
print(x1 is x2, z3.eq(x1, x2))   # False True -- distinct wrapper, identical term
"
```

`z3.FreshInt` proposed fix primitive (guarantees distinctness regardless of name
reuse or nesting depth):

```bash
python3 -c "
import z3
x1, x2 = z3.FreshInt('future_true_time'), z3.FreshInt('future_true_time')
print(z3.eq(x1, x2))   # False
"
```

## 6. Minimal Until/Since reproductions and the Task 137 link

Enumerating all primitive-tag (`atom`, `bot`, `imp`, `untl`, `snce`) "temporal-only"
formulas at complexity≤5 with a single atom `p` (matching
`test_cross_oracle_differential.py`'s `_enumerate_primitive_formulas` /
`_is_temporal_only`, which is also what feeds the xfail'd
`test_temporal_only_agreement_complexity_5` — the test documenting the 13
resolved-and-wrong MC/BimodalHarness divergences), 158 formulas are temporal-only. Of
these, 82 (56 collapsing to `True`, 26 to `False`) have a `conclusion_constraints[0]`
that `z3.simplify()` reduces to a Boolean literal. Most of those are **genuine**
tautologies/contradictions from `\bot` (e.g. `\bot \Until \bot`, `p \rightarrow p`) —
not bugs. Filtering out every formula containing `\bot` leaves exactly two non-trivial
survivors, both matching the predicted "same primitive operator directly nested in
`event` position" pattern:

- `(p \Until p) \Until p` → conclusion constraint simplifies to literal `True`
- `(p \Since p) \Since p` → conclusion constraint simplifies to literal `True`

Both are genuinely contingent formulas (`p \Until p` is essentially "eventually p with
continuity"; nesting it again should still be contingent, not a tautology under any
frame). Their `false_at` collapsing to constant `True` is a pure encoding artifact —
the same bug as `G(G(p))`/`F(F(p))`, confirmed via the identical `UntilOperator`
naming pattern (`witness_time = z3.Int('until_witness_time')`,
operators.py:928, reused unconditionally on every `true_at` call, colliding when the
`event` argument is itself an `\Until`). Nesting in `guard` position instead
(`p \Until (p \Until p)`) does **not** fully collapse — it produces a non-constant,
partially corrupted constraint (analogous to `G(F(p))`), because only the
`guard_time` name collides, not `witness_time`.

`find_countermodel((p \Until p) \Until p)` currently raises `OracleTimeoutError` at
the default 5000ms budget — i.e., this specific pair happens to land on the
"vacuous-True, falls through to slow frame search" side of the asymmetry described in
§4, not the "fast spurious None" side. That does not mean it is irrelevant to Task
137's differential sweep: `MIN_CONCLUSIVE_SCAN_FORMULAS`/`SELF_SCAN_SOLVE_TIMEOUT_MS`
gate on decisiveness at a longer (10000ms) budget than the default 5000ms used above,
and other same-operator-nested-in-event-position formulas at complexity≤5 (there are
more once `\bot`/`\top`-involving and 2-atom variants are considered, and once
`all_future`/`some_future`/`all_past`/`some_past` enriched forms are included, which
`_enumerate_primitive_formulas` does not generate but the full 274-formula
complexity≤5 population referenced by `known_conclusive_complexity5.json` may) are
plausible candidates for resolving to a fast, decisive, *wrong* verdict that would
disagree with BimodalHarness's independently-implemented oracle — exactly the
"resolved-and-wrong" signature task 137 tracks.

`bimodal_harness` is not importable in this environment
(`ModuleNotFoundError: No module named 'bimodal_harness'`), so the specific 13
formulas in the xfail'd `test_temporal_only_agreement_complexity_5` could not be
enumerated directly during this research pass. **Recommend, as a first planning step,
running that test (or a standalone script using the same enumerator) wherever
BimodalHarness is installed, printing the 13 `resolved_and_wrong` formula dicts, and
checking each one's `conclusion_constraints[0]` against `z3.simplify()` the same way
this report did** — this would either confirm the causal link precisely (giving an
exact list of formulas the 139 fix should flip) or bound how many of the 13 remain
unexplained (a genuinely separate defect, not to be conflated with 139's scope).

## 7. Fix implementation guidance

**Sites to change** (all in
`code/src/model_checker/theory_lib/bimodal/operators.py`), replacing
`z3.Int('literal_name')` with `z3.FreshInt('literal_name')`:

| Class | Method | Line | Current name |
|---|---|---|---|
| `NecessityOperator` | `true_at` | 407 | `nec_true_world` |
| `NecessityOperator` | `false_at` (dead) | 437 | `nec_true_world` (also a same-name-as-true_at bug in its own right) |
| `FutureOperator` | `true_at` | 556 | `future_true_time` |
| `FutureOperator` | `false_at` (dead) | 583 | `future_false_time` |
| `PastOperator` | `true_at` | 732 | `past_true_time` |
| `PastOperator` | `false_at` (dead) | 759 | `past_false_time` |
| `UntilOperator` | `true_at` | 928-929 | `until_witness_time`, `until_guard_time` |
| `UntilOperator` | `false_at` (dead) | 974-975 | `until_false_witness_time`, `until_false_guard_time` |
| `SinceOperator` | `true_at` | 1156-1157 | `since_witness_time`, `since_guard_time` |
| `SinceOperator` | `false_at` (dead) | 1202-1203 | `since_false_witness_time`, `since_false_guard_time` |

`z3.FreshInt(prefix)` is confirmed available through `model_checker.z3_shim` (a
transparent `__getattr__` passthrough to the active backend module) for both the `z3`
backend and the `cvc5.pythonic` backend (`'FreshInt' in dir(cvc5.pythonic)` is
`True`), so no backend-conditional code is needed. `FreshInt` generates a distinct
term on every call (verified: `z3.eq(FreshInt('x'), FreshInt('x'))` is `False`),
which eliminates the aliasing class of bug entirely, independent of nesting depth,
without needing to thread a depth counter through `eval_point`.

**Do not** assume this alone fixes `G(F(p))`/`F(G(p))`-style *mixed*-operator nesting
into a fully correct encoding automatically — it does; once the shared name is gone,
the recursive `eval_time` correctly threads through as a distinct, genuinely-bound
outer variable at each level, restoring the intended semantics for all of Future,
Past, Until, Since nesting (same-operator or mixed). This report only needed to
special-case Box because it is structurally immune to the *specific* collapse
mechanism, not because it needs a different fix — it should receive the same
`FreshInt` treatment for defensive consistency (and to fix the true_at/false_at
same-name defect noted above), even though no live behavior change is expected from
that particular change.

**Dead code decision needed at planning time**: keep the `false_at` methods (fixed
defensively) vs. delete them as genuinely unreachable dead code. Either is compatible
with this research; flagging as an open decision rather than research scope creep.

## 8. Test rewrite implications

Tests currently asserting the bug as correct behavior, all in
`oracle/bimodal_logic/tests/test_soundness_regression.py`:

- `test_gg_p_returns_none` (line 401) and `test_gg_p_returns_none_at_m4` (line 1072):
  assert `G(G(p))` returns `None`, citing shadowing explicitly by name. Post-fix,
  `G(G(p))` is genuinely invalid (per the same docstring's own counterexample: `p`
  false at `t=3` requires `M>=4`) — expect these to need rewriting to expect a
  genuine countermodel (`result is not None`) at a sufficiently large `M`, or an
  `OracleTimeoutError` if the now-correctly-constrained solve is too slow at the
  oracle's chosen `M`. Do not assume in advance which; re-run after the fix.
- `test_fg_p_returns_none` (line 414) and `test_fg_p_returns_none_at_m4` (line 1085):
  per §4/§6, `F(G(p))`'s `None` result is **not** a shadowing artifact — it is
  genuine boundary vacuity (the simplified constraint is a real, non-constant,
  correctly-`p`-independent expression from the domain becoming empty at the
  boundary). These tests are very likely **already correct** and should not need a
  behavioral change from the fix, only a docstring correction if their prose
  currently conflates them with the shadowing class (check exact wording at
  implementation time — the task description groups both G(G(p)) and F(G(p)) as
  "quantifier variable shadowing," but this research found only G(G(p)) is actually a
  shadowing artifact).
- `test_gg_p_spurious_unsat` / `test_fg_p_spurious_unsat` (lines 777, 807): these are
  M=2 boundary-vacuity tests, orthogonal to depth via M — confirm they are unaffected
  before touching them (they test the M=2, not M=4, situation and their own docstrings
  already correctly attribute the M=2 result to boundary vacuity, not shadowing).
- `TestKnownBoundaryUnsafe` class docstring (lines 758-771) and
  `test_ff_p_returns_none_at_m4` (line 859): already correctly hedges — its own
  docstring states the prior shadowing attribution for `F(F(p))`'s timeout "is not
  confirmed by this behavior." §4 of this report resolves that: the shadowing
  attribution *is* correct as the root cause of the corrupted (constant-`True`)
  conclusion constraint, but the *timeout itself* is caused by the pre-existing
  expensive frame/abundance-quantifier solve at `M=4`, not by shadowing directly.
  Update this docstring accordingly rather than leaving it as an open question.
- `test_gf_p_returns_none_at_m4` (line 840): also times out; per §4, `G(F(p))`'s
  conclusion is a *partially* corrupted (non-constant, non-`p`-referencing)
  constraint. Re-verify post-fix; the timeout may resolve to a genuine (possibly
  still slow) decision once the real `p`-dependence is restored.

## 9. Conclusive-rate re-measurement (Phase 4) guidance

Use `oracle/scan_runner.py` and `oracle/run-oracle-exhaustive-scan.sh` (per task
context — these already exist from Task 138 and detect completion via the
`SCAN_COMPLETE` marker, never PID liveness) rather than a new harness. Do not assume
the fix raises the conclusive rate:

- Formulas whose conclusion currently collapses to constant `False` (fast, wrong
  `None`) **lose their free short-circuit** once fixed. If the newly-correct query is
  genuinely hard to decide at the oracle's `M`, some of these flip from
  "conclusive-but-wrong" to "inconclusive" (`OracleTimeoutError`) — a *decrease* in
  raw conclusive count that is nonetheless the correct outcome (a wrong fast answer is
  strictly worse than an honest timeout, per the same soundness principle the
  timeout/UNSAT-conflation fix in Task 133 already established).
- Formulas whose conclusion currently collapses to constant `True` (vacuous, forcing
  an expensive unconstrained frame search that often times out) may become *easier*
  once the real constraint is restored, since SAT solvers frequently prune faster with
  genuine constraints than with an unconstrained satisfiability question — a plausible
  *increase*.
- Net direction is an empirical question; measure, do not assume. The task
  description's "well above 38.7 percent" is a hypothesis to test, not a target to
  hit.
- Because the *set* of specific formulas that are conclusive will change (not just
  the count — §6/§9 above), `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`
  (103/274, pinned 2026-08-06) must be re-derived after the fix lands, and
  `MIN_CONCLUSIVE_GATING_FORMULAS=100` (test_cross_oracle_differential.py:147) and
  `MIN_CONCLUSIVE_SCAN_FORMULAS=90` (same file:117) should be re-derived alongside it
  using the same methodology documented in that file's own surrounding comments
  (re-run at `SELF_SCAN_SOLVE_TIMEOUT_MS=10000`, serial/contention-free, record the
  new conclusive set and count, apply the same ~97% retention-slack reasoning already
  used for the 103→100 derivation). This re-derivation is **required**, not optional,
  regardless of which direction the raw count moves — flag this explicitly for the
  planner, since the task's own open question asked whether it's required.

## 10. Files referenced

- `code/src/model_checker/theory_lib/bimodal/operators.py` (lines 387-447, 522-770,
  895-1004, 1128-1231 — the operator `true_at`/`false_at` implementations)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (lines 1519-1636 —
  `define_invalidity`, `true_at`, `false_at` dispatch)
- `code/src/model_checker/syntactic/sentence.py` (lines 184-249 — `update_types` /
  `derive_type`, where `DefinedOperator`s are expanded to primitives before Z3
  construction)
- `code/src/model_checker/models/constraints.py` (lines 44-93 — `ModelConstraints`,
  where `conclusion_behavior` is invoked)
- `oracle/bimodal_logic/provider.py` (whole file — `find_countermodel`,
  `OracleTimeoutError` contract, `M = max(depth+2, 3)`, and the module docstring's
  discussion of `task_restriction`/MBQI cost at `M>=3`)
- `oracle/bimodal_logic/tests/test_soundness_regression.py` (lines 367-877, 1060-1097
  — the tests enumerated in §8)
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (lines 87-147,
  1185-1340 — the enumerator, `_is_temporal_only`, `MIN_CONCLUSIVE_GATING_FORMULAS`,
  and the xfail'd `test_temporal_only_agreement_complexity_5` referenced in §6)
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` (baseline
  requiring re-derivation per §9)
- `specs/138_make_oracle_suite_fast_and_observable/` (prior task; scan tooling and
  the `SELF_SCAN_SOLVE_TIMEOUT_MS`/`MIN_CONCLUSIVE_SCAN_FORMULAS` pinned constants)
