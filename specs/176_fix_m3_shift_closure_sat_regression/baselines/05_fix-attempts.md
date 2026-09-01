# Phase 5: Fix Attempts

**Status as of this writing**: no candidate has reached green (SAT within the 15.0s budget) for
`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`. This file records every avenue
tried and its measurement, per the plan's requirement, whether or not a fix ultimately lands.
Phase closed `[COMPLETED WITH EXCLUSIONS]` -- see the Reasoned Exclusions in
`07_decision-record.md` and the escalated Phase 6 decision recorded there.

## Diagnostic: How Much Headroom Is Needed

Phase 4's bisection established the target precisely: pre-task-153 code (`f9cc081e^`) is
deterministically `rlimit_count = 7,850,279`, solving SAT in 3.3-8.2s. Post-task-153 (`f9cc081e`
through HEAD, unmodified), `rlimit_count` is 29M-46M and the solve is cancelled at the 15.0s wall
clock every time (5/5 in Phase 1, reconfirmed here). The fix needs to bring the combined
constraint set's cost back down near the ~8M rlimit region (or reduce wall-clock-per-rlimit-unit
enough to finish 29M+ units within 15s, which is not a lever this task controls).

## Avenue 1: Explicit E-matching Pattern on `build_interpolation_constraint`

**Rationale**: `build_interpolation_constraint` is structurally analogous to
`build_forward_comp_constraint` (both are `Implies(premise-guarded-by-task_rel, conclusion)`
axioms over `task_rel`), and `forward_comp` already carries an explicit
`z3.MultiPattern(task_rel(w,d1,v), task_rel(v,d2,u))` pattern precisely to avoid eager
instantiation. `interpolation` shipped in `f9cc081e` with NO explicit pattern -- an apparent gap
relative to its sibling, and a plausible oversight rather than a deliberate choice (unlike
`capped_skolem_abundance_constraint`/`depth_bounded_skolem_abundance_constraint`, whose
un-patterned form IS deliberate -- task 144 tried and reverted a pattern there). This is a NEW
axiom with no prior tuning history, so patterning it does not repeat a closed task-144 dead end
(those targeted different, already-shared, already-tuned axioms and were rejected because they
starved OTHER formulas depending on the axiom's *existing* untriggered behavior -- there is no
such existing dependency for an axiom introduced this same task).

**Tried**: `patterns=[self.task_rel(w, d1 + d2, v)]` (the sole premise term, covering all four
bound variables `w, v, d1, d2` in one application) on `build_interpolation_constraint`'s
`ForAll`.

**Measured** (isolated single run, pattern only, no other change): `unknown`/`canceled`,
`wall_seconds=15.0089`. No improvement over baseline in isolation.

## Avenue 2: Isolate Which of the Two New Axioms Drives the Cost

**Rationale**: before tuning further, determine whether `seriality` or `interpolation` (or both
jointly) is the dominant contributor, to target effort correctly.

**Tried**: monkeypatched `build_seriality_constraint` and `build_interpolation_constraint`
(independently and jointly) to return `z3.BoolVal(True)` in place of their real bodies, on HEAD's
otherwise-unmodified code, and re-ran the repro.

**Measured**:
| Stubbed | Result | rlimit_count |
|---|---|---|
| seriality only | unknown/canceled | 28,224,178 |
| interpolation only | unknown/canceled | 31,131,929 |
| both | unknown/canceled | 29,774,623 |

**Surprising finding**: stubbing BOTH new axioms out entirely still does not restore SAT within
budget, even though Phase 4's direct git-bisection (`f9cc081e^` vs `f9cc081e`, the same
stub-equivalent comparison via real commits rather than a monkeypatch) showed a clean 7.85M ->
29M jump. This discrepancy motivated Avenue 3 below.

## Avenue 3: Run-to-Run Non-Determinism Independent of the Two New Axioms

**Rationale**: Avenue 2's discrepancy (stubbing the axioms on HEAD's code does not reproduce
`f9cc081e^`'s low cost, even though the two commits' only real diff IS those axioms) suggested a
confound: HEAD's `rlimit_count` might not be a fixed function of the input formula alone.

**Tried**: ran the identical HEAD repro under `PYTHONHASHSEED=0/1/2` (Python's hash-randomization
seed, which can perturb `dict`/`set` iteration order and hence Z3 term/assertion construction
order for code that iterates over unordered collections).

**Measured**: `rlimit_count` varies materially with `PYTHONHASHSEED` at HEAD (19,996,241 -
24,515,351 across 3 seeds; unseeded runs elsewhere in this task ranged 11M-46M across many runs).
By contrast, `f9cc081e^`'s `rlimit_count` was **exactly** `7,850,279` across 3 repeated runs with
no seed control -- fully deterministic. **Conclusion**: HEAD's constraint-construction pipeline
has a real, measurable sensitivity to Python-level iteration-order non-determinism that the
pre-153 code does not exhibit (or exhibits below a cost cliff that doesn't matter at 11
constraints but does at 13). This is consistent with, not contradictory to, Phase 4's finding --
seriality/interpolation's addition is what pushes the formula close enough to the cliff that this
latent order-sensitivity now determines pass/fail, rather than always failing regardless of seed.
No specific unordered-collection site was root-caused within this phase's budget; recorded as an
open architectural observation, not a proven mechanism.

## Avenue 4: Reorder `seriality`/`interpolation` in `build_frame_constraints`' Returned List

**Rationale**: the method's own docstring states "order matters for Z3 MBQI seed quality." The two
new axioms are spliced between `forward_comp` and `skolem_abundance` (the most expensive shared
axiom for this formula). Moving them to the end of the list (after `skolem_abundance` and
`world_uniqueness`) tests whether their position -- independent of their content -- perturbs
`skolem_abundance`'s MBQI scheduling.

**Tried**: moved `seriality, interpolation` from immediately before `*skolem_abundance` to
immediately after `world_uniqueness` in the list `build_frame_constraints` returns.

**Measured**: `rlimit_count` improved and tightened: 18,619,240 - 20,124,097 across 3 runs (down
from the 32-46M baseline range), but still `unknown`/`canceled` every time. Real, reproducible
improvement (roughly 2x), insufficient alone.

## Avenue 5: Combine Patterns + Reordering

**Tried**: interpolation pattern (Avenue 1) + a `patterns=[serial_succ(w,x), serial_pred(w,x)]`
addition to seriality (as a plain list -- two independent single-term patterns, each an
alternative trigger, not a joint requirement) + the Avenue 4 reordering, together.

**Measured**: `rlimit_count` 11,187,869 - 20,444,633 across 6 runs. Closer to the ~8M target than
any single avenue, but never below it; still `unknown`/`canceled` in every run.

## Avenue 6: Corrected Joint `MultiPattern` for Seriality (No Unrolling, No Reordering)

**Rationale**: a plain multi-item `patterns=[t1, t2]` list is two independent single-term
patterns (either alone triggers), which is broader/more eager than a genuine joint pattern.
`build_forward_comp_constraint`'s established precedent uses `z3.MultiPattern(t1, t2)` --
requiring both terms present together before triggering, which is narrower and safer.

**Tried**: `patterns=[z3.MultiPattern(serial_succ(w, x), serial_pred(w, x))]` on seriality (in
place of the two-separate-patterns form), `patterns=[u]` on interpolation (Avenue 1's form),
original list ordering (no Avenue 4 reordering).

**Measured**: `rlimit_count` 15,401,955 - 26,064,131 across 3 runs. Still `unknown`/`canceled`
every time -- no better than, and in this small sample slightly worse than, Avenue 5's combined
form.

## Avenue 7 (recorded, not independently re-verified by this writer): Unrolling Seriality's
Duration Dimension

A variant was also observed on disk during this phase unrolling `seriality`'s `x` (duration)
dimension into `M` separate single-variable `ForAll([w], ...)` conjuncts (concrete `x_val` in
`range(0, self.M)`) combined with per-conjunct patterns, `z3.And(*conjuncts)` in place of the
single two-variable `ForAll([w, x], ...)`. This mirrors task 144 dead end 10's already-rejected
"unroll the shift/duration dimension" idea for a *different* axiom
(`depth_bounded_skolem_abundance_constraint`), which was measured there to be a genuine cost
regression (doubling independent top-level quantifiers). Combined-state runs including this
variant (Avenue 5 above) did not reach green either. Not independently isolated as its own
single-variable measurement within this phase's budget.

## Avenue 8: Clean Sole-Owner Re-Measurement (Patterns + Reordering, 5 Runs)

Earlier avenues in this phase were measured while a second, independently-dispatched agent was
concurrently editing this same file without either agent's knowledge (a dispatch-tracking error
on the orchestrating side, since corrected) -- flagged, investigated, and resolved mid-phase (see
this task's session record). Once sole ownership of the working tree was confirmed, the single
best-performing candidate from the earlier (confounded) measurements -- Avenue 6's corrected
`z3.MultiPattern(serial_succ(w, x), serial_pred(w, x))` on seriality, `patterns=[u]` on
interpolation, PLUS Avenue 4's reordering (`seriality, interpolation` moved to after
`*skolem_abundance, world_uniqueness` instead of immediately before `*skolem_abundance`) -- was
re-applied cleanly and re-measured over 5 consecutive runs with no other process touching the
file:

| Run | rlimit_count | wall_seconds | verdict |
|---|---|---|---|
| 1 | 21,012,534 | 15.0011 | unknown/canceled |
| 2 | 21,430,782 | 15.0009 | unknown/canceled |
| 3 | 19,303,774 | 15.0010 | unknown/canceled |
| 4 | 21,191,737 | 15.0012 | unknown/canceled |
| 5 | 20,338,491 | 15.0007 | unknown/canceled |

**This is the phase's authoritative measurement**, superseding the noisier, possibly
cross-contaminated numbers recorded during the concurrent-editing window (Avenues 5-7 above,
which ranged more widely, 11M-26M, and are retained here only as a record of what was tried, not
as the final verdict). Clean and reproducible: rlimit_count is tightly clustered at
19.3M-21.4M -- a real, stable, ~2.2x reduction from the unmodified-HEAD baseline (32-46M, Phase 1)
-- but still ~2.5x above the ~8M pre-regression target, and `unknown`/`canceled` in all 5 runs.
No run reached SAT.

The source edit underlying this measurement was reverted after recording it (core.py matches
committed HEAD exactly; verified via `git diff` producing no output and the target test still
failing with its original RED message) -- landing an unverified, insufficient, partial-benefit
encoding change without its own full regression-gate pass and without a deliberate decision on
what it trades against (task-153's axioms are explicitly out of scope to revert; see the plan's
Non-Goals) is not a call this phase makes unilaterally. See `07_decision-record.md` for the
escalation.

## Summary

Eight avenues tried (six independently measured under a since-corrected concurrent-editing
confound, one combined-and-observed, and one clean, authoritative sole-owner re-measurement).
Best measured result: a stable ~19.3M-21.4M rlimit_count (Avenue 8, combined interpolation
pattern + seriality `MultiPattern` + reordering) against a ~8M target -- a real, reproducible
~2.2x reduction from the unmodified baseline (32-46M), but not reaching the pre-regression floor.
No candidate reached SAT within the 15.0s budget in any run across all avenues. Task-144's
precedent (a well-tuned, already-shared axiom family that resists further trigger tuning without
starving other formulas) appears to extend to this new axiom pair as well: pattern/ordering
tuning yields real, measurable, but insufficient improvement, and the mechanism (an MBQI/
E-matching cost increase from widening the asserted TaskFrame axiom set, compounded by a latent
order-sensitivity in the constraint-construction pipeline that concurrent-editing noise had
partly obscured) resists a clean single-lever fix within this phase's scope.

No source file was left modified with an unreverted, non-working experimental state by this
avenue-tracking; `core.py` matches committed HEAD exactly at the close of this phase. See
`07_decision-record.md` for the escalated Phase 6 decision.
