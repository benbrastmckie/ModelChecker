# Task 97: Strategic Direction for build_frame_constraints Optimization

**Teammate D - Horizons (Strategic Direction)**
**Date**: 2026-05-29

---

## Key Findings

### Finding 1: Tasks 97 and 98 Are the Same Root Problem

Tasks 97 (optimize build_frame_constraints) and 98 (OOM kills at M>=3) are not independent --
they share a common root cause. The OOM kills described in task 98 are the natural consequence of
the constraint complexity that task 97 aims to reduce.

The `capped_skolem_abundance_constraint` introduces a ForAll over two integer variables
(source_world, shift_amount), with a body that includes `matching_states_when_shifted_var`, which
is itself a nested ForAll over a time variable. This 3-level quantifier nesting (outer ForAll x
ForAll = 2 variables, inner ForAll = 1 variable) feeding into array Select operations is precisely
what Z3's MBQI engine expands unboundedly when combined with `forward_comp` (5 quantified variables
across BitVec and Int sorts).

At M=4/M=5, the valid shift range approximately doubles relative to M=3. Combined with more world
history interval combinations, the solver's internal instantiation tables grow superlinearly.

**Implication**: Task 97's optimization work should explicitly be scoped to also address the OOM
problem. Any approach that reduces memory footprint of the abundance constraint or tightens
quantifier scopes will directly help task 98.

**Confidence**: High -- supported by the task 98 description naming the exact same constraints
(capped_skolem_abundance_constraint + forward_comp + world_uniqueness) and by the profiling
infrastructure already present in `profile_abundance.py`.

---

### Finding 2: The classical_truth Constraint Is a Pure Tautology -- Remove It

The constraint at line 507-516 of semantic.py reads:

```python
classical_truth = z3.ForAll(
    [world_state, sentence_letter],
    z3.Or(
        self.truth_condition(world_state, sentence_letter),
        z3.Not(self.truth_condition(world_state, sentence_letter))
    )
)
```

This is `ForAll x. P(x) \/ ~P(x)`, which is a tautology for any P in classical logic. Z3 knows
this immediately but must still parse, register, and maintain this constraint. More importantly,
this adds the function symbol `truth_condition` into Z3's ground term database used for quantifier
instantiation triggers, which can expand instantiation of other quantified constraints that also
mention `truth_condition` (the `lawful` constraint references `z3.Select(self.world_function(...),
...)` which uses the world state that feeds into truth evaluations).

This is a safe removal: the constraint adds zero logical content. Its presence may have been
intended to guarantee bivalence, but Z3's uninterpreted functions already default to bivalent
Boolean outputs -- `truth_condition` returns `BoolSort()`, which is inherently bivalent.

**Implication**: Remove `classical_truth` entirely. This is a zero-risk, potentially non-trivial
win because it removes a ground term trigger that could be amplifying E-matching.

**Confidence**: High -- the constraint is textbook-tautological. The main risk is if some other
constraint somewhere implicitly relies on this being asserted, but no such dependency exists in
the current architecture.

---

### Finding 3: Solver Portability Is Already Abstracted -- Z3-Specific Tactics Are Safe

The codebase already uses `z3_shim.py` as a transitional abstraction layer over the solver. The
`MultiPattern` annotation on `build_forward_comp_constraint` (line 382-387) is already Z3-specific
syntax. The CVC5 adapter uses CEGQI (`cegqi=true`, `cegqi-bv=true`) as its quantifier strategy,
which does not interpret Z3's `MultiPattern` hints -- these are silently ignored or raise at parse
time depending on the CVC5 pythonic API version.

The architecture's existing design decision is: "use the best available Z3 features, with the
z3_shim providing a migration path to other backends." This means Z3-specific optimization
(quantifier pattern annotations, MBQI parameter tuning) is acceptable in the frame constraint
layer as long as the constraints themselves are logically equivalent when stripped of solver hints.

**Implication**: Z3-specific annotations like `MultiPattern` and `patterns=[...]` can be added
freely to the heavy quantifier blocks (lawful, converse, task_restriction, world_uniqueness,
capped_skolem_abundance) without compromising the CVC5 path. The constraints remain semantically
correct; the solver hints are ignored when using CVC5.

**Confidence**: High -- confirmed by examining both z3_adapter.py and cvc5_adapter.py; the Z3
adapter explicitly enables E-matching (`smt.ematching=True`) which is the mechanism exploited by
`MultiPattern`.

---

### Finding 4: Lean Alignment Is Structural, Not Textual -- Optimizations Are Safe

The extensive "ProofChecker Alignment" comments in semantic.py describe logical correspondence
with `Frame.lean`, `Truth.lean`, and `Soundness.lean`. These alignments are semantic (the
constraints encode the same logical properties), not syntactic (the Z3 constraint syntax need not
mirror the Lean proof structure).

Optimizations that preserve the logical content of each constraint are therefore always alignment-
safe. The risk zone is any change that:
1. Weakens a constraint (removes a required condition)
2. Strengthens a constraint (adds an unintended restriction)
3. Changes the interpretation of the primitives (task_rel, world_function, truth_condition)

Optimizations that are alignment-safe:
- Removing tautological constraints (classical_truth)
- Adding quantifier patterns/hints (they don't change the constraint's meaning)
- Reordering constraints in the list (Z3 treats the conjunction as unordered)
- Grounding constraints for specific small M values (same logical content, finite enumeration)
- Tuning solver parameters via z3_adapter.py (external to the constraint logic)

The primary alignment concern is with the `capped_skolem_abundance_constraint` and its interaction
with the perpetuity theorems (BM_TH_1, BM_TH_2). Task 96 established that this constraint is
correct and necessary -- any weakening of it would reintroduce the BM_TH_1/BM_TH_2 failure. Any
optimization of this constraint must be tested against BM_TH_1 and BM_TH_2 even though they are
currently in KNOWN_TIMEOUT_EXAMPLES.

**Confidence**: High -- based on reviewing the task 96 summary and the constraint logic.

---

### Finding 5: Constraint Ordering Has Performance Impact

The current ordering in `build_frame_constraints` (lines 667-687) places `forward_comp` (5
quantified variables, the heaviest axiom) before `skolem_abundance` and `world_uniqueness`. In
Z3's MBQI engine, earlier constraints seed the initial ground term database used for later
quantifier instantiation. Heavier axioms placed early can accelerate instantiation of later axioms
in useful ways, but also risk front-loading the most expensive pattern matching.

The existing `# NOTE: order matters!` comment acknowledges this. Task 97 should empirically
investigate constraint reordering as a low-risk performance lever that requires no logical changes.

Specifically: placing `nullity_identity` and `convex_world_ordering` first (simple, fast
constraints) before `forward_comp` and `skolem_abundance` may warm up the solver's ground term
database with simpler facts that constrain the quantifier instantiation scope of the heavier axioms.

**Confidence**: Medium -- the order-dependency is acknowledged in comments but the direction of
benefit is not established without profiling.

---

### Finding 6: The `world_interval_constraint` vs `time_interval_constraint` Split Is a Design Debt

The file contains both `world_interval_constraint` (universal quantifier version, currently in
use) and `time_interval_constraint` (enumerated version, commented out as `# time_interval`). The
enumerated version grounds out the interval choices to specific world IDs (0..max_world_id), which
avoids a universally-quantified constraint.

However, `max_world_id = M * 2^(M*N)` grows exponentially with M and N. At M=4, N=2: 4 * 2^8 =
1024 world ID constraints. At M=5, N=4: 5 * 2^20 = 5.2M constraints -- completely infeasible.

The path forward is to combine these approaches: use a quantifier but with a finite-domain
enumeration of interval options (which is already what `world_interval_constraint` does with its
`for start_time, end_time in time_intervals` loop generating the Or body).

The real opportunity is in the `valid_array_domain` helper called within `world_interval_constraint`,
which contains a nested ForAll. This creates the quantifier nesting: ForAll world -> (is_world(w)
-> Or(... ForAll time -> ...))). Flattening this into a ground-term form for small M would reduce
the nesting.

**Confidence**: Medium -- the exponential blowup of the enumerated version makes it inapplicable
for large M, but partial grounding for the interval options is worth exploring.

---

### Finding 7: Performance Monitoring Infrastructure Is Missing and Should Be Added

The project has `profile_abundance.py` as a one-off profiling script for abundance strategies.
There is no systematic benchmarking infrastructure for tracking constraint performance across M
values or across optimization iterations. Task 97 should include building lightweight benchmarking
that:
1. Records solve times for key examples (BM_TH_1/BM_TH_2, BX5, BX7, BX13) across M values
2. Reports Z3 statistics (instantiation counts, memory usage) via `z3.set_param('verbose', 10')`
   or `solver.statistics()`
3. Can be run as a standalone script or triggered via pytest marks

This infrastructure would directly benefit task 98 (OOM investigation) and all future optimization
work, preventing regression to worse performance.

**Confidence**: High (value) / Medium (feasibility within task 97 scope) -- this is clearly
valuable but may require prioritization.

---

## Recommended Approach

### Priority 1: Quick Wins (Zero Semantic Risk)

1. **Remove `classical_truth`** -- tautological constraint, zero benefit, possible E-matching cost.
   Test: run full test suite; confirm no change in valid/invalid classification.

2. **Add quantifier patterns to `lawful`, `converse`, and `world_uniqueness`** -- these heavy
   ForAll blocks currently have no pattern hints. Add `patterns=[z3.MultiPattern(...)]` annotations
   following the precedent set by `forward_comp`. The pattern should trigger on the core function
   application in each constraint.

3. **Tune Z3 solver parameters for the bimodal theory** -- the Z3 adapter at z3_adapter.py:37
   already sets `smt.mbqi=True` and `smt.ematching=True`. Consider adding bimodal-specific
   configuration: `smt.mbqi.max_iterations=100` (reduce from 1000 for faster unknown detection),
   `smt.qi.max_multi_patterns=5` (limit multi-pattern instantiation depth). These should be
   tested carefully as they may cause timeouts that currently terminate as "unknown".

### Priority 2: Medium-Risk Structural Changes

4. **Ground the abundance constraint for small M** -- for M=1 and M=2, the number of valid shifts
   is small enough (2 and 4 respectively) to enumerate all shift constraints explicitly rather than
   using a universally-quantified Skolem approach. This would improve performance for the majority
   of simple examples (most examples use M=1 or M=2) while the universally-quantified Skolem
   approach remains as the fallback for M>=3.

5. **Add memory limit configuration to Z3 adapter** -- add `set_memory_limit()` method to
   `Z3SolverAdapter` that calls `z3.set_param('memory_max_size', N)` or uses the
   `smt.max_memory` parameter. This directly addresses task 98 (OOM kills) by preventing
   earlyoom-level kills in favor of solver-controlled memory exhaustion with an `unknown` result.

6. **Investigate constraint reordering** -- empirically test whether placing lighter constraints
   (nullity, enumeration, convex ordering) before heavier ones (forward_comp, skolem_abundance)
   improves performance. This is a low-risk change with potential non-trivial benefit.

### Priority 3: Long-Term Architectural Directions (Future Tasks)

7. **Incremental/lazy constraint loading** -- the current architecture adds all frame constraints
   at initialization and never removes any. A CEGAR-style approach would start with a minimal
   constraint set and add constraints on-demand when the current model violates them. This is a
   major architectural change requiring new infrastructure.

8. **Symmetry reduction** -- world histories that are time-shifted versions of each other are
   semantically equivalent in many contexts. Adding symmetry-breaking constraints (e.g., ordering
   world IDs by their interval start times) would reduce the search space without changing which
   formulas are valid/invalid.

9. **Per-theory solver configuration** -- allow theories to specify solver parameters beyond the
   global z3_adapter defaults. The bimodal theory needs different MBQI parameters than other
   theories due to its quantifier-heavy constraint system.

---

## Evidence/Examples

### Evidence for Finding 1 (Task 97/98 same root problem)

Task 98 description explicitly names the same constraints:
> "Z3's quantifier instantiation engine has no memory cap and expands ground terms unboundedly
> when processing the capped Skolem abundance constraint combined with forward_comp (5 quantified
> variables) and world_uniqueness (ForAll/Exists)"

This matches exactly the constraints in `build_frame_constraints` lines 586 and 596-616 and 664.

### Evidence for Finding 2 (classical_truth is tautological)

`semantic.py` lines 507-516: the formula is `ForAll [world_state, sentence_letter]: P \/ ~P`.
This is the Law of Excluded Middle, which holds for any boolean-valued function in classical logic.
Z3's BoolSort guarantees bivalence -- no additional constraint is needed.

### Evidence for Finding 3 (Z3-specific tactics are safe)

`cvc5_adapter.py` uses `cegqi`, not E-matching with pattern hints. The MultiPattern on
`forward_comp` (semantic.py:386) is already present and tested. The shim architecture (`z3_shim.py`)
explicitly supports this two-path model.

### Evidence for Finding 4 (Lean alignment is semantic)

The comment on `build_forward_comp_constraint` lines 349-388 describes both the ProofChecker
alignment AND the Z3 MultiPattern optimization in the same docstring, demonstrating that the
existing codebase already treats these as compatible concerns.

### Evidence for Finding 5 (constraint ordering)

The `# NOTE: order matters!` comment at line 667 of `build_frame_constraints` explicitly
acknowledges order-sensitivity. The comment is the only documentation; no empirical investigation
has been performed.

### Evidence for Finding 7 (benchmarking infrastructure needed)

`profile_abundance.py` exists as a standalone profiling script but is not integrated into the
test suite. It profiles only one aspect (abundance strategy selection) on one example (BM_TH_1).
The file is a proof-of-concept that profiling is feasible but lacks systematic coverage.

---

## Confidence Levels

| Finding | Confidence | Basis |
|---------|-----------|-------|
| 1. Tasks 97+98 share root cause | High | Task 98 description names exact same constraints |
| 2. classical_truth is tautological | High | Logical analysis + no downstream deps found |
| 3. Z3-specific tactics are safe | High | Architecture review of both adapters |
| 4. Lean alignment is semantic | High | Task 96 precedent + constraint review |
| 5. Constraint ordering matters | Medium | Comment acknowledges it; direction unestablished |
| 6. Interval constraint design debt | Medium | Code analysis; grounding infeasible for large M |
| 7. Benchmarking infrastructure needed | High (value) / Medium (scope) | Existing profile_abundance.py as precedent |

---

## Summary for Synthesis

The most strategically important insight is that **tasks 97 and 98 should be coordinated or
merged**: the OOM kills at M>=3 are a direct consequence of the constraint complexity targeted by
task 97. Any solution to 97 that reduces quantifier instantiation overhead will also reduce memory
consumption and OOM risk.

The safe, high-confidence optimization path for task 97 is:
1. Remove `classical_truth` (zero-risk tautology removal)
2. Add `MultiPattern` hints to `lawful`, `converse`, and `world_uniqueness` (zero logical change)
3. Add memory limit configuration to `Z3SolverAdapter` (addresses task 98 directly)

These three changes can be implemented without risk to the ProofChecker alignment or the
valid/invalid classification of any existing example. They are also verifiable by the existing
43-test bimodal suite plus manual timing of BM_TH_1 and BM_TH_2.

The constraint grounding approach (Finding 6, Priority 2 item 4) is the highest-potential medium-
risk improvement: replacing the universal Skolem abundance with explicit enumeration for small M
values would dramatically speed up the M=1 and M=2 examples that constitute most of the test suite,
while preserving correctness of the harder M>=3 cases.
