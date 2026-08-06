# Phase 1: Pre-fix evidence and collapse census

## PRE_FIX_SHA

```
PRE_FIX_SHA=d795b5f4444a4a3a326a4775b7431b89144e930c
```

Recorded via `git rev-parse HEAD` before any Phase 2+ edit landed. All pinned-artifact checks
in later phases compare against this SHA, not against a moving `HEAD`.

## Collapse census

Instrument: `specs/139_fix_z3_quantifier_variable_shadowing_in_temporal_operators/evidence/collapse_census.py`.
For every formula produced by `_enumerate_primitive_formulas(5, ["p"])` (274 formulas, the same
enumerator the gating/exhaustive oracle suite uses), it builds `ModelConstraints` the same way
`Z3OracleProvider.find_countermodel` does (stopping short of `BimodalStructure`, i.e. zero
solves), takes `conclusion_constraints[0]`, and applies `z3.simplify()`. Output:
`evidence/pre-fix-census.json`.

Run at `PRE_FIX_SHA`:

```
total_formulas: 274
folded: 104 (true=64, false=40)
non-bot folded survivors (full 274-formula population): 7
```

### Discrepancy vs. the plan's Phase 1 verification criterion -- recorded, not silently resolved

The plan's verification bullet expects "its non-`\bot` folded set is exactly the two
`\Until`/`\Since` reproductions" and instructs to stop and record any discrepancy. The **actual**
non-`\bot` folded set, filtered to `_is_temporal_only` formulas (158 of 274, matching the
research report's own filtered population) is **four**, not two:

| index | folded_value | formula |
|---|---|---|
| 9   | False | `p -> p` |
| 113 | False | `p -> (p -> p)` |
| 205 | True  | `(p \Until p) \Until p` |
| 273 | True  | `(p \Since p) \Since p` |

Restricted further to the *full* (unfiltered, box-inclusive) 274-formula population, there are
**seven** non-`\bot` survivors -- the same four above, plus three Box-involving formulas:

| index | folded_value | formula |
|---|---|---|
| 23  | False | `\Box(p -> p)` |
| 61  | False | `\Box(\Box(p -> p))` |
| 125 | False | `\Box(p) -> \Box(p)` |

**Resolution**: this is not a failure of the research's mechanism claim. Both `p -> p` and
`p -> (p -> p)` are pure `imp`/`atom` trees -- they contain **no** `box`, `untl`, or `snce` node
anywhere, i.e. no quantified operator that declares a Z3 bound variable is present at all. They
are structurally outside the aliasing defect's blast radius by construction (there is no nested
same-primitive quantifier declaration to alias), and `Not(p -> p)` / `Not(p -> (p -> p))` are
genuine propositional tautologies-under-negation (both reduce to `False` from pure Boolean
algebra on a single atom evaluated at a single world/time, independent of any quantifier
encoding). The three Box-involving additions (`\Box(p->p)`, `\Box(\Box(p->p))`,
`\Box(p)->\Box(p)`) are likewise genuine: `NecessityOperator` is, per the research report §3,
*mechanistically immune* to the collapse (it never compares its own bound variable against
`eval_time`), so their folding to `False` is ordinary modal-K monotonicity/necessitation over a
propositional tautology, not the aliasing artifact.

The research report's own §6 prose actually cites `p -> p` as one of its two illustrative
examples of "genuine tautologies/contradictions" in the same sentence that also cites
`\bot \Until \bot` -- i.e. the report's own text already flags `p -> p` as a genuine (not
aliasing-caused) survivor. The immediately following claim of "exactly two...survivors" after
filtering `\bot` is therefore an arithmetic imprecision in the report (it should have said "two
aliasing-defect survivors, plus a small number of independently-genuine propositional/modal
tautologies not touching any quantified operator"), not evidence the core diagnosis is wrong.

**What is preserved and confirmed**: the *only* two non-`\bot`, non-pure-propositional survivors
-- i.e. the only two formulas whose collapse to a Boolean literal actually requires a nested
same-primitive quantified operator to alias -- are exactly `(p \Until p) \Until p` and
`(p \Since p) \Since p`, both folding to `True`. This is the specific claim Phase 2/3 must falsify
post-fix, and it holds.

## Named reproductions (via `Z3OracleProvider.find_countermodel`, default `timeout_ms=5000`)

```
GG_P: result=None time=0.089s
FF_P: OracleTimeoutError time=5.096s (temporal_depth=2, M=4)
(p Untl p) Untl p: OracleTimeoutError time=5.091s (temporal_depth=2, M=4)
(p Snce p) Snce p: OracleTimeoutError time=5.101s (temporal_depth=2, M=4)
```

Confirms research report §4/§5/§6 exactly:
- `G(G(p))` collapses to `False` -> trivially UNSAT -> fast spurious `None` (0.089s).
- `F(F(p))` collapses to `True` -> vacuous -> falls through to the expensive raw
  frame-satisfiability search at `M=4` -> exhausts the 5000ms default budget.
- `(p \Until p) \Until p` and `(p \Since p) \Since p` collapse to `True` for the same reason and
  also time out at the 5000ms default (they land on the "vacuous, falls through to slow frame
  search" side of the asymmetry, not the "fast spurious None" side, matching research §6's
  observation that this pair does not decisively resolve at all at this budget -- it becomes a
  candidate for the gating suite's `SELF_SCAN_SOLVE_TIMEOUT_MS=10000` budget instead, tracked by
  the exhaustive re-derivation in Phase 7-8).

Both collapse directions are confirmed live pre-fix.

## `bimodal_harness` import check

```
PYTHONPATH=code/src:oracle python3 -c "import bimodal_harness"
-> ModuleNotFoundError: No module named 'bimodal_harness'
```

`bimodal_harness` is not importable in this environment. The MC/BimodalHarness linkage (Task 137's
13 "resolved-and-wrong" divergences) cannot be checked directly here. The collapse census above is
the substitute instrument this plan relies on instead: it establishes that two primitive
`\Until`/`\Since` formulas resolve on a corrupted (constant-folded) encoding pre-fix, which is
independently useful evidence for that linkage even though it cannot confirm or enumerate the
specific 13 formulas. This is recorded as unverified, not assumed either way, per the plan's
instruction.

## Pinned-artifact audit at PRE_FIX_SHA (baseline check)

Running the Hard Constraint section's audit script against `PRE_FIX_SHA` itself (i.e. comparing
the file to its own state) trivially prints `PINNED OK` -- this establishes the script itself
runs cleanly and will be re-run against real post-fix changes in Phase 9.
