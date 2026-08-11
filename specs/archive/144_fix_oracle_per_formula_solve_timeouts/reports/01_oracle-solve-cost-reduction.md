# Research Report: Reducing Oracle Per-Formula Z3 Solve Cost

- **Task**: 144 - fix_oracle_per_formula_solve_timeouts
- **Date**: 2026-08-10
- **Scope**: `oracle/bimodal_logic/provider.py`,
  `oracle/bimodal_logic/tests/test_oracle_interface.py`,
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, and the Z3 encoding they drive
  in `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and
  `code/src/model_checker/theory_lib/bimodal/operators.py`.

## 1. Summary

The three failing per-formula solves are not victims of an accidental performance regression in
the ordinary sense (no commit silently made the encoding slower by mistake). They are the
**permanent, already-accepted cost of a soundness fix** (git history section 3): the same-day
predecessor task replaced fixed-name Z3 bound variables with per-call-unique names in every
quantified temporal/modal operator to eliminate a genuine term-aliasing unsoundness bug. That fix
is correct and must not be reverted, but it removed an accidental form of term sharing that had
been keeping several formulas artificially fast. The result is that multiple formulas — not just
the three named here — now sit at 20-75s solve times against 60-150s budgets, thin enough that
Z3's own well-documented run-to-run variance (up to ~20x on an unchanged formula, per
`code/docs/core/TESTING_GUIDE.md` section 8.6) can occasionally push any one of them over budget.
Fresh isolated measurements taken today inside `nix develop` (section 4) confirm all three formulas
currently solve comfortably under budget in isolation, consistent with a marginal-not-broken
diagnosis rather than a new intervening regression.

The actionable, semantics-preserving lever is encoding-level: the quantifiers introduced or
exercised by the affected operators (`\Box`, `\Future`/`\next`, `\Past`, `\Until`, `\Since`, and the
depth-bounded Skolem abundance axiom) have **no explicit E-matching trigger patterns**, unlike
`build_forward_comp_constraint`, which already uses one (the codebase's own established
precedent). Adding patterns, plus a small, previously-untried partial-grounding of the
depth-bounded abundance axiom's shift dimension, are concrete candidates that reduce solver search
without changing what is being decided. Section 5 gives the ranked recommendations; section 6
lists the encoding changes this codebase has already tried and found to regress, so they are not
re-proposed.

## 2. Evidence Review: What the Two Full-Gate Runs Actually Showed

From `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_phase4-triage-record.md`
and its two baseline transcripts:

| Signature | Quiet run (load 1.57) | Contended run (load 5.4-7.5) |
|---|---|---|
| `test_mixed_and_box_next` (60000ms) | pass 2: OracleTimeoutError | pass 2: OracleTimeoutError |
| `test_mixed_and_all_future_neg` (60000ms) | pass 1: OracleTimeoutError | not observed |
| `test_all_sat_task_relation_ternary` (180000ms) | pass 1: OracleTimeoutError | not observed |
| `test_cross_oracle_differential.py:656` conclusive floor | not observed | pass 2: 99/103 vs floor 100, `disagreements=0` |

`test_mixed_and_box_next` is the only signature shared by both runs. Every failure carries
`disagreements=0` — no semantic disagreement anywhere, consistent across all evidence gathered for
this and the predecessor task. The error messages in the baseline transcripts report
`temporal_depth=1, time_bound M=3` for all three named tests, which matches
`provider.find_countermodel`'s `M = max(depth + 2, 3)` computation exactly (`provider.py:213-222`).

## 3. Root-Cause Chain: Why the "~44-45s" Characterization No Longer Holds Reliably

Git history on `code/src/model_checker/theory_lib/bimodal/` traces a specific mechanism, not a
mystery regression:

1. **Commit `3c0cf210` (task 139 phase 2 amendment)** replaced `z3.Int('fixed_name')` bound
   variables in 14 quantified-operator declaration sites (`operators.py`: `\Box`, `\Future`,
   `\Past`, `\Until`, `\Since` true_at/false_at) with a counter-suffixed `_fresh_bound_int()`
   helper. Rationale, quoted from the commit and the helper's own docstring: `z3.Int` interns
   constants by `(name, sort)`, so two calls with the same fixed name returned the *literal same
   Z3 term*. A quantified operator whose argument recurses into another instance of itself then
   received, as its own "fresh" bound variable, the exact term the outer call already held —
   producing a self-comparison Z3's simplifier folded to a constant **before either quantifier
   closed**. This is a genuine soundness defect (task 139's summary documents a concrete casualty:
   F4, `p Until q -> q Until p`, was mis-documented "VALID" pre-fix because two *sibling*, not even
   nested, Until instances aliased).
2. The fix is semantically required and already landed; it is not a candidate for reversion here
   (task 144's own hard constraint set forbids weakening correctness, and doing so would
   reintroduce a proven-unsound result).
3. **The archived task 139 summary already documents the fix's cost**: "`BM_CM_4`'s `max_time`
   widened 15->30 (genuine solve-time cost, **term-identity-shortcut-loss mechanism**, not a
   soundness issue)", and `test_mixed_or_diamond_prev`'s own docstring (in
   `test_oracle_interface.py`, written the same session) records a directly comparable case: "once
   the quantified operators' bound variables stopped accidentally sharing Z3 term identity via
   fixed-name interning" its solve went from ~1.5s to ~73s, reproduced via a direct scratch-copy
   comparison against the pre-fix operators.py.
4. `test_mixed_and_box_next`'s "~44-45s ... confirmed by repeated serial timing" docstring
   (commit `7f7269d6`, 10:05am) was written **after** the aliasing fix (`3c0cf210`, six days
   earlier) and after the same day's unrelated `71d437bd` (a process-global counter *reset*, item
   2 below) — i.e. it already reflects the post-fix, permanently-elevated cost, not a
   yet-to-regress baseline. No commit to `core.py` or `operators.py` postdates that measurement
   (`git log --oneline` on `semantic/` shows `71d437bd` is the newest entry touching the encoding;
   everything after is test-file-only).
5. **`71d437bd` (task 140) is a red herring, not a second regression**: it made
   `BimodalSemantics._reset_global_state()` call `operators.reset_bound_var_counter()`, restarting
   the counter at 0 for every fresh instance. Each instance already runs inside its own fresh Z3
   `Context` (`isolated_z3_context()`), so the reset only changes the *numeric suffix* attached to
   each bound-variable name within that context, never the uniqueness guarantee itself. It fixed a
   cross-test-order-dependence bug (a different `BM_CM_4` symptom), and has no plausible mechanism
   to change solve *cost* — term uniqueness, not the specific integer used, is what E-matching and
   MBQI key off.

**Conclusion on Research Goal 3**: cost did not silently regress between the "~44-45s" measurement
and today. Rather, the entire class of formulas exercising `\Box`/`\Future`/`\Past`/`\Until`/
`\Since` operators picked up a permanent, already-known, already-accepted cost increase from the
task 139 soundness fix, and `test_mixed_and_box_next`'s ~44-45s sits close enough to its 60s budget
(historically documented as "~25% headroom") that ordinary Z3 non-determinism — documented
separately and independently in `TESTING_GUIDE.md` section 8.6 as up to a 20x spread on an
*unchanged* formula — can tip it over. The same margin logic applies to
`test_mixed_and_all_future_neg` (also depth 1, same M=3, same operator family) and
`test_all_sat_task_relation_ternary` (exercises `\next` at depth 1 among its five sub-solves).

## 4. Fresh Empirical Measurements (today, inside `nix develop`, machine otherwise idle)

Run via `pytest oracle/bimodal_logic/tests/test_oracle_interface.py -k <test>` (serial, no
`-n`, no other pytest session running):

| Test | Budget | Run 1 | Run 2 |
|---|---|---|---|
| `test_mixed_and_box_next` | 60000ms | 46.75s | 44.33s |
| `test_mixed_and_all_future_neg` | 60000ms | 24.04s | - |
| `test_all_sat_task_relation_ternary` | 180000ms | 93.96s | - |

All three pass comfortably in isolation today (22-27% headroom for `and_box_next`, ~2.5x headroom
for the other two), consistent with the marginal/variance diagnosis above rather than a further
new regression: nothing changed the encoding between the "~44-45s" characterization and today, and
today's `and_box_next` timings (44.33s, 46.75s) reproduce that characterization almost exactly.

A direct pipeline reproduction of `and(box(A), next(B))` (bypassing pytest, calling
`BimodalSemantics`/`ModelConstraints`/`BimodalStructure` exactly as `provider.find_countermodel`
does) confirms `temporal_depth=1, M=3` (matching the baseline error messages exactly) and a 44.4s
solve. `structure.stored_solver`'s Z3 statistics after the solve report `rlimit count: 130120807`
— on the order of 10^8 resource-limited units of internal work for a two-atom, depth-1 formula —
which is disproportionate to the formula's surface size and consistent with the quantifier
instantiation cost this report attributes the slowness to (Z3's Python stats API did not surface a
`quant instantiations` counter without `smt.qi.profile` enabled, which was not turned on for this
measurement; a follow-up profiling pass with that flag would give a direct instantiation count if
needed before implementing section 5's changes).

## 5. Concrete, Semantics-Preserving Cost-Reduction Candidates

Ranked by expected leverage relative to risk. All are instantiation-heuristic changes only — none
alter what is being decided (soundness/completeness of the frame constraints is untouched), so
`disagreements` should remain 0 provided each change is verified against the differential suite
before being trusted.

### 5.1 Add explicit E-matching trigger patterns to the still-unpatterned quantifiers (highest leverage)

`build_forward_comp_constraint()` (`core.py:344-394`) is the **only** quantifier in the entire
frame-constraint/operator encoding that supplies an explicit `patterns=` argument:

```python
return z3.ForAll(
    [w, v, u, d1, d2],
    body,
    patterns=[z3.MultiPattern(self.task_rel(w, d1, v), self.task_rel(v, d2, u))],
)
```

Its own docstring explains why: "guide Z3 to instantiate this axiom only when both component
tasks are already in the solver's ground term set, reducing spurious instantiations." Every other
`ForAll`/`Exists` in `core.py` — including `ForAllTime`/`ExistsTime` (`core.py:396-461`, the
helper every `\Future`/`\Past`/`\Until`/`\Since` true_at/false_at method routes through),
`NecessityOperator`'s raw `z3.ForAll`/`z3.Exists` (`operators.py` ~503-545, used by `\Box`),
`lawful`, `world_uniqueness`, `enumeration_constraint`, `convex_world_ordering`, and both Skolem
abundance constraints (`capped_skolem_abundance_constraint`,
`depth_bounded_skolem_abundance_constraint`) — has no `patterns=` argument at all, leaving Z3 to
infer triggers automatically (or fall back to full MBQI when auto-inference fails to find a
covering pattern, which is the expensive path these comments already describe: "MBQI handles
poorly," "nested ForAll/Exists causes MBQI timeouts").

This is directly connected to the section 3 mechanism: before task 139, repeated calls to the same
operator returned *the same Z3 term* for their bound variable, which likely let Z3's automatic
pattern/E-graph matching treat many quantifier instances as referring to already-seen ground terms
"for free." After task 139 made every bound variable unique, that accidental assistance is gone,
and there is no explicit pattern to replace it. Extending the codebase's own established technique
(the `forward_comp` precedent) to the operator-level quantifiers is the most targeted, best-attested
fix:

- `NecessityOperator.true_at`/`false_at`: the natural single-variable trigger is
  `semantics.is_world(other_world)` — already the sole predicate mentioning the bound variable in
  the guard, so an explicit pattern here would make deliberate what Z3's default heuristic may
  currently be choosing unreliably (or falling back from).
- `ForAllTime`/`ExistsTime`: trigger on `semantics.is_valid_time(time_var)`, or, if that proves too
  weak to fire eagerly, a `MultiPattern` over `is_valid_time(time_var)` and a ground subterm from
  the recursive body's own truth predicate (e.g. `world_function`/`Select` applications at
  `time_var`) — needs a benchmarking pass since `is_valid_time` is arithmetic-flavored rather than
  a clean function application (see caveat below).
- `depth_bounded_skolem_abundance_constraint`/`capped_skolem_abundance_constraint`: trigger on
  `self.is_world(source_world)` (already the codebase's own comment identifies this as "the
  Skolem function produces a valid world" — a genuine `z3.Function` application, a legal pattern).

**Caveat**: not every guard here is pattern-eligible as-is. Z3 patterns must be matchable ground
or quantified *function applications* (uninterpreted or interpreted-but-matchable), not arbitrary
arithmetic comparisons — `is_valid_time(time_var)` (`core.py:815`, `duration > -M and duration < M`
style body) may itself need to be re-expressed as (or supplemented with) a genuine function
application before it can serve as a trigger. This needs verification against the actual
`is_valid_time`/`is_valid_duration` bodies before implementation, not assumed.

### 5.2 Partially ground the depth-bounded Skolem abundance axiom's shift dimension

`depth_bounded_skolem_abundance_constraint(max_shift)` (`core.py:1456-1499`) — the constraint
active for every M>=3, depth>0 case (i.e., exactly the case for all three failing tests, since
`M = max(depth+2, 3) = 3` whenever `depth <= 1`) — quantifies over **two** variables jointly:

```python
return z3.ForAll(
    [source_world, shift_amount],
    z3.Implies(z3.And(self.is_world(source_world), ..., shift_amount != 0,
                       shift_amount >= -max_shift, shift_amount <= max_shift),
               z3.And(..., self.matching_states_when_shifted_var(source_world, shift_amount, ...)))
)
```

For all three failing tests, `max_shift == temporal_depth == 1`, so `shift_amount` ranges over
exactly `{-1, 1}` — a two-element finite domain known at construction time (it is `self.M`/depth,
both concrete Python ints, not solver-time unknowns). Unrolling only this dimension in Python
(building `2*max_shift` separate `ForAll([source_world], ...)` constraints, one per concrete
`shift_amount` value, conjoined) is a sound finite-domain elimination — logically equivalent to the
current joint quantifier, since `shift_amount`'s range is always small and depth-bounded by
construction (that is the entire point of the depth-bounded variant over the M-bounded
`capped_skolem_abundance_constraint`). Each resulting constraint has only one bound variable
(`source_world`), a cheap and obvious trigger (`is_world(source_world)`), and no residual
polymorphism over the shift value for Z3 to search — it becomes a ground constant baked into the
body. This is a **different, smaller-blast-radius transformation** than the two grounding attempts
already tried and rejected (section 6): those grounded the *world* dimension (which is genuinely
large, `bound = 3*M` and an O(worlds^2) target enumeration); this proposal leaves the world
dimension fully quantified/Skolemized and only removes the *shift* dimension, whose range is
provably tiny for every depth-1 formula in the failing set.

Note also that `matching_states_when_shifted_var`, called from inside this axiom's body
(`core.py:1232-1265`), itself contains a **third, nested** nested `ForAll([time], ...)` with no
explicit pattern — so the "single" abundance axiom is actually a two-level quantifier chain today.
Grounding the outer `shift_amount` to a concrete value also lets `matching_states_when_shifted_var`
receive a concrete `shift` argument rather than a bound variable, which may simplify its own
`time + shift` arithmetic for Z3's arithmetic theory solver even before any pattern work is done to
its `time` quantifier.

### 5.3 Pin the Z3 random seed for measurement stability (secondary, low-risk)

No `smt.random_seed` / `sat.random_seed` is set anywhere in
`code/src/model_checker/solver/z3_adapter.py`'s `_configure_quantifier_mode()`. This does not by
itself reduce cost, but `TESTING_GUIDE.md` section 8.6's ~20x variance on an unchanged formula is
consistent with Z3's own documented sensitivity to internal term/hash ordering, which an unpinned
seed leaves to whatever the process's memory layout happens to be on a given run. Pinning a seed
converts today's "sometimes over budget by chance" into a single, reproducible number per formula,
which makes sections 5.1/5.2's effectiveness independently verifiable (compare identical seeded
runs before/after) rather than needing many repeated timings to average out noise. This should be
treated as a measurement-hygiene aid alongside 5.1/5.2, not a fix on its own — the task's hard
constraint is to reduce genuine cost, not merely to get lucky more often.

## 6. Established Dead Ends — Do Not Re-Propose

The codebase has already benchmarked and rejected the "obvious" alternative of grounding
quantifiers more aggressively, in three independent instances, all documented in `core.py`'s own
comments:

1. **Full grounding of the abundance constraint**
   (`build_grounded_abundance_constraints`, tested Task 98): regressed both SAT and UNSAT cases
   (`BM_CM_1`: 9s -> 15s timeout; `BM_TH_1`/`BM_TH_2`: 30s -> 75s+). Root cause per the codebase's
   own note: the grounded form creates *more* ground terms via eager E-matching (one Skolem term
   per world per valid shift, immediately), while the quantified MBQI form is lazy. Do not
   re-attempt full grounding of the world/target dimension — section 5.2 above deliberately avoids
   this by grounding only the depth-bounded shift dimension, not the world dimension.
2. **Array-disequality grounding of `world_uniqueness`** (Task 97 Phase 2): reverted after causing
   8 test failures, because Z3 array disequality checks *all* indices, conflicting with
   `valid_array_domain` constraints that only bind a subset of the array's domain. The current
   `ForAll`/`Exists` formulation is deliberately retained.
3. **Enabling `task_restriction`** (disabled by design, `core.py:700-754`): introduces a nested
   `ForAll[state, duration, next_state], Exists[world, time]` alternation that MBQI handles poorly;
   confirmed to cause solver timeouts on examples with >3 worlds at M>=3 during Task 91/97. It
   remains correctly disabled (soundness analysis in the same comment block explains why this is
   sound for the oracle's countermodel-generation use case) and should stay that way.
4. **`z3.FreshInt` instead of a counter-suffixed `z3.Int`** (Task 139 phase 2, superseded within
   the same task): caused a severe, unrelated MBQI performance cliff (a lone `F(p)` went from
   ~1.3s to undecided at 60s) traced to `FreshInt`'s own internal bookkeeping, not to term
   distinctness. Already replaced by `_fresh_bound_int()`; not a lever available here.
5. **`smt.mbqi.max_cexs=50`** (evaluated, Task 98): "no measurable memory reduction for our
   constraint set" and not worth the added tuning risk; left at Z3's default.
6. **`qi.max_instances`** (evaluated, unspecified task per `z3_adapter.py`'s own comment): "causes
   `unknown` results on countermodel examples that require many quantifier instantiations (`BM_CM_2`,
   `BM_CM_4`)"; explicitly noted "not safe to cap without thorough per-example profiling."

## 7. Verification Plan for Any Implemented Change

Per the task's hard constraint (no budget widening, no floor lowering, no xfail/skip) and the
oracle's role as a differential correctness reference, any implementation drawn from section 5
must be checked against:

- `oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` — the permanent regression guard
  installed by task 139 specifically to catch a reintroduction of quantifier aliasing; must stay
  green.
- `oracle/bimodal_logic/tests/test_soundness_regression.py` and the full
  `oracle/bimodal_logic/tests/` suite, both passes of `oracle/run-oracle-suite.sh` (parallel and
  `xdist_serial`), watching specifically for `disagreements != 0` anywhere, which would indicate a
  pattern change accidentally suppressed a needed instantiation and altered a verdict rather than
  merely its timing.
- The three named tests (`test_mixed_and_box_next`, `test_mixed_and_all_future_neg`,
  `test_all_sat_task_relation_ternary`) timed in isolation, multiple repeated runs (per section
  4's method), to confirm a genuine reduction in typical solve time rather than a single lucky
  measurement — consistent with `TESTING_GUIDE.md` 8.6's caution against trusting a single timing
  sample given documented ~20x same-formula variance.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s `TestGatingConclusiveScan`
  (the 99/103-vs-floor-100 test), to confirm the conclusive count returns to or above the pinned
  floor without the floor itself being touched.

## 8. Files Read / Key References

- `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_phase4-triage-record.md`
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6-quiet-attempt.txt`
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6-contended-attempt.txt`
- `specs/archive/139_fix_z3_quantifier_variable_shadowing_in_temporal_operators/summaries/01_fix-quantifier-aliasing-rebaseline-summary.md`
- `oracle/bimodal_logic/provider.py`
- `oracle/bimodal_logic/tests/test_oracle_interface.py` (`TestMixedFormulas`,
  `TestTernarySerializationAll`)
- `oracle/bimodal_logic/translation.py` (`temporal_depth`)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`build_frame_constraints`,
  `build_forward_comp_constraint`, `ForAllTime`/`ExistsTime`,
  `capped_skolem_abundance_constraint`, `depth_bounded_skolem_abundance_constraint`,
  `matching_states_when_shifted_var`, `world_interval_constraint`)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (`_fresh_bound_int`,
  `NecessityOperator`, `FutureOperator`)
- `code/src/model_checker/solver/z3_adapter.py` (`_configure_quantifier_mode`)
- `code/docs/core/TESTING_GUIDE.md` sections 8.6 and 8.8
- Git commits: `3c0cf210` (task 139 phase 2 amendment: FreshInt -> counter-suffixed Int),
  `7f7269d6` (task 140: `and_box_next` xdist_serial + ~44-45s docstring), `71d437bd` (task 140: bound-var
  counter reset, unrelated to solve cost)
- Fresh empirical measurements taken 2026-08-10 inside `nix develop` (this session; see section 4)
