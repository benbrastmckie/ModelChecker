# Phase 2: Encoding-Drift Audit Against the Post-Task-114 Baseline

## Method

Baseline source extracted via `git show 12eb4ded:code/src/model_checker/theory_lib/bimodal/semantic.py`
(pre-task-126 path; task 126 phase 21, `a404edbd`, split this file into `semantic/core.py` among
others). Compared function-by-function against
`code/src/model_checker/theory_lib/bimodal/semantic/core.py` at HEAD.

## Per-Function Verdicts

| Function | Verdict | Notes |
|----------|---------|-------|
| `depth_bounded_skolem_abundance_constraint` | **comment-only** | Logic (the `z3.ForAll(...)` body) is byte-identical. Two changes: (1) wrapped in a single-element list `[...]` instead of returned bare -- caller-contract change only, `build_frame_constraints` unwraps it with `*skolem_abundance`; (2) ~54 lines of Task 144 dead-end documentation (dead ends 8, 10) added as a docstring/comment. No semantic change. |
| `capped_skolem_abundance_constraint` | **comment-only** | Logic identical. 13-line Task 144 dead-end comment added (a trigger tried and reverted, confirmed inapplicable to this task's M=3/temporal_depth=1 case since that combination dispatches to `depth_bounded_skolem_abundance_constraint` instead -- see dispatch below). |
| `matching_states_when_shifted_var` | **comment-only** | Logic identical. 14-line Task 144 dead-end comment added (dead end 7: an E-matching trigger tried and reverted because it regressed other depth-1/M=3 formulas sharing this nested axiom). |
| `world_interval_start` / `world_interval_end` | **identical** | Not Python methods -- both are `z3.Function` declarations created in `BimodalSemantics.__init__` (`core.py:219-226`). Declaration signature (name, domain sorts `WorldIdSort -> TimeSort`) and every call-site usage pattern found via `grep -rn` are unchanged from the baseline. |
| `skolem_abundance` dispatch block in `build_frame_constraints` | **semantically changed (additive)** | The `M<=2` vs `M>=3`/`temporal_depth` dispatch logic choosing between `capped_skolem_abundance_constraint` and `depth_bounded_skolem_abundance_constraint` is unchanged. What changed: two new frame axioms (`seriality`, `interpolation`) are now computed and spliced into the returned constraint list immediately **before** `skolem_abundance`, changing the total constraint set solved together (see below). This is an addition to the surrounding dispatch context, not a change to the dispatch condition or the abundance constraints themselves. |

**Conclusion**: the three quantifier-bearing abundance/matching functions this task's formula
depends on are logically byte-identical to the post-task-114 baseline. The task-144 reverts
(`401bb58c`, `40ad9238`, `eb1639de`) were genuinely clean reverts of the *code path this test
exercises* (M=3, temporal_depth=1 dispatches to `depth_bounded_skolem_abundance_constraint`,
which the diff confirms is untouched logically) -- they left comment-only artifacts behind, not a
silent behavioral change.

## Frame-Constraint-Set Delta Since `12eb4ded`

| Baseline (`12eb4ded`) | HEAD | Delta |
|---|---|---|
| 11 constraints (per the baseline docstring: "This method constructs 11 constraints total") | 13 constraints (confirmed by `repro_m3.py --dump-constraints`: `frame_constraint_count: 13`) | **+2** |

The two additions, confirmed by diffing `build_frame_constraints` and its call-site ordering:

- `build_seriality_constraint()` -> `seriality` (TaskFrame.Serial: `∀w,x>=0. ∃u,v. task_rel(w,x,u) ∧ task_rel(v,x,w)`)
- `build_interpolation_constraint()` -> `interpolation` (TaskFrame.Interpolates: `task_rel(w,d1+d2,v) → ∃u. task_rel(w,d1,u) ∧ task_rel(u,d2,v)`)

Both landed in `f9cc081e` ("task 153 phase 4: implement and wire Skolemized Seriality/Interpolation",
2026-08-31 13:35), spliced into the returned list immediately before the `skolem_abundance` group:
```
nullity_identity, converse, forward_comp, seriality, interpolation, *skolem_abundance, world_uniqueness
```
This is confirmed to be the sole net addition to the constraint set walked by `12eb4ded..HEAD` for
this function -- no other commit in the candidate set below adds, removes, or reorders a
top-level frame constraint.

`71d437bd` (task 140, bimodal order-dependence root-cause fix) is also in the candidate set but
touches `operators.py`'s process-global `_bound_var_counter` reset timing, not `build_frame_constraints`
or the frame-constraint set itself -- confirmed by `git show --stat` showing no `semantic/` hunks.

## Candidate Commit Set: Confirmed, Not the Scope-Hypothesis List Verbatim

The plan's Scope Hypothesis proposed
`{30f97c64, a404edbd, 71d437bd, 401bb58c, 40ad9238, eb1639de, f9cc081e, a15a6dc7, 3555a864}` as the
candidate set touching the bimodal semantic package since `12eb4ded`. Re-running
`git log --oneline 12eb4ded..HEAD -- code/src/model_checker/theory_lib/bimodal/semantic/` (plus the
pre-rename path) returns one additional commit not in the hypothesis: `002fd055` ("task 117 phase 4:
register bimodal dynamic-loader module in sys.modules"). Checked and ruled out: it registers
`sys.modules[spec.name]` for the dynamic loader (fixing a pickling/`ProcessPoolExecutor` issue for
`--maximize`), touching zero constraint-construction logic.

**Additional axis checked beyond the hypothesis's stated scope** (per Phase 2's task instruction to
also check `models/` and the solver-abstraction layer): `code/src/model_checker/theory_lib/bimodal/operators.py`
was NOT in the semantic/-scoped log above, but task 139 (`b53fd9ad`, `3c0cf210`, `712dce72`,
2026-08-06/07) changed `_fresh_bound_int()` there -- the shared helper naming quantifier-bound Z3
`Int`s across the bimodal operator implementations -- from fixed names to counter-suffixed unique
names, specifically to fix a term-aliasing soundness bug. Its own commit messages independently
record "confirmed genuine solve-time regressions" from this exact class of change (loss of
Z3 term-identity shortcuts), fixed forward elsewhere by widening two *other* tests' `max_time`
15->30. **Ruled out as a direct cause for this specific formula**: `depth_bounded_skolem_abundance_constraint`,
`capped_skolem_abundance_constraint`, and `matching_states_when_shifted_var` all declare their own
bound variables locally via fixed-literal-name `z3.Int('skbnd_src')` / `z3.Int('skbnd_shift')` /
etc. directly in `semantic/core.py`, not via `operators.py`'s `_fresh_bound_int()` -- task 139's
change does not touch these three functions' own quantifiers. It remains a *possible* indirect
contributor via the shared solver instance's e-graph (this axiom's ground terms interacting with
operator-emitted terms from the same `ModelConstraints` build), but no direct mechanism was found;
recorded here for Phase 4 to weigh if the seriality/interpolation attribution proves insufficient.
Also checked and ruled out on the same basis: `models/`'s `63de5f78` (task 169 phase 3, optional
`max_rlimit`, default-off and unset by this test's settings dict) and `002fd055` above.

**Models/solver layer, checked per Phase 2's instruction**: `code/src/model_checker/models/` and
`code/src/model_checker/solver/` were git-logged separately (see command below); of the commits
found, only `63de5f78` (task 169 phase 3, deterministic rlimit budgets) is solver-behavior-adjacent,
and it is default-off/no-op for this test (confirmed: this test's settings dict carries no
`max_rlimit` key). No other `models/`/`solver/` commit in the window changes `solve()`'s control
flow, timeout handling, or constraint assembly.

## Confirming Commands

```
git log --oneline 12eb4ded..HEAD -- code/src/model_checker/theory_lib/bimodal/semantic/ code/src/model_checker/theory_lib/bimodal/semantic.py
git log --oneline 12eb4ded..HEAD -- code/src/model_checker/models/
git log --oneline 12eb4ded..HEAD -- code/src/model_checker/solver/
PYTHONPATH=code/src python3 specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py --dump-constraints
```
