"""bimodal_logic.provider - Z3OracleProvider entry point stub.

This module provides the Z3OracleProvider class that implements the
bimodal_harness oracle interface using the Z3 SMT solver.

NOTE: This is a placeholder stub. Full implementation will be provided
in task 103 (implement Z3OracleProvider).

## Z3 Frame Hierarchy and BimodalLogic Axiom Mapping

### Terminology Disambiguation

The `supported_frame_classes = frozenset({"Base"})` declaration in the oracle
refers to **TaskFrame axiom satisfaction** (the three frame axioms below), NOT
to BimodalLogic's proof-system concept `FrameClass.Base` (which encompasses
37 axioms across the full proof theory). The "Base" label here means: "the Z3
oracle's frame satisfies the three TaskFrame axioms that form the minimal
semantic base for bimodal reasoning."

### The Three TaskFrame Axioms

BimodalLogic's `TaskFrame` structure (Frame.lean) requires exactly three axioms
on the `taskRel : S -> Q -> S -> Prop` relation, where S is the state type and
Q is an additive abelian group (integers in the Z3 approximation):

| TaskFrame Field | Mathematical Property | Z3 Implementation |
|-----------------|----------------------|-------------------|
| `nullity`       | task_rel(s, 0, u) ↔ s = u | `build_nullity_identity_constraint()` |
| `converse`      | task_rel(s, d, u) ↔ task_rel(u, -d, s) | `build_converse_constraint()` |
| `compose`       | task_rel(s,d1,t) ∧ task_rel(t,d2,u) → task_rel(s,d1+d2,u) | `build_forward_comp_constraint()` |

These correspond to the additive group axioms: identity (nullity), inverse
(converse), and composition (forward_comp). Together they make (S, Q, taskRel)
a "generalized metric space" structure.

### Z3 Approximation Discrepancies

The Z3 oracle approximates the Lean BimodalLogic formulation with three known
discrepancies:

1. **Bounded domain**: Z3 uses integer time domain (-M, M) where M is a
   finite parameter. Lean uses unbounded `Int`. UNSAT results from Z3 are
   conservative (sound), not complete for the unbounded theory.

2. **Converse guard**: The Z3 `build_converse_constraint()` is guarded by
   `is_valid_duration(d) AND is_valid_duration(-d)`. The Lean axiom is
   unconditional. Within the valid duration range the two coincide; outside
   it, Z3 makes no claim (conservative).

3. **forward_comp asymmetry**: Z3's `build_forward_comp_constraint()` uses
   duration validity guards `is_valid_duration(d1)`, `is_valid_duration(d2)`,
   `is_valid_duration(d1+d2)`. Lean's `compose` axiom restricts to
   `0 <= x, 0 <= y` (non-negative durations). These are equivalent via the
   converse axiom (any negative-duration task reverses a non-negative one).

### Additional Model-Building Constraints (Not TaskFrame Axioms)

The Z3 oracle adds 8 further constraints beyond the 3 TaskFrame axioms to
produce well-structured countermodels:

| # | Constraint | Purpose |
|---|------------|---------|
| 1 | valid_main_world | main_world ∈ valid worlds |
| 2 | valid_main_time | main_time ∈ valid times |
| 3 | enumeration_constraint | worlds start at ID 0, non-negative |
| 4 | convex_world_ordering | no gaps in world ID sequence |
| 5 | world_interval | each world has a valid time interval |
| 6 | lawful | consecutive world-states connected by task_rel(s,1,s') |
| 8 | skolem_abundance | time-shifted world copies exist (ShiftClosed) |
| 9 | world_uniqueness | distinct world IDs → distinct histories |

Constraints 7-9 in `build_frame_constraints()` are the TaskFrame axioms (items
nullity_identity, converse, forward_comp). Constraints 1-6 and 8-9 (the
non-TaskFrame ones) are model-building. The disabled constraint 10
(task_restriction) is discussed below.

### Disabled Constraint: task_restriction (Soundness Analysis)

Constraint 10, `task_restriction`, would require every `task_rel(s, d, u)` to
be grounded in an actual world history -- i.e., there must exist a world `w`
and time `t` such that `w(t) = s` and `w(t+d) = u`.

**Why it is disabled**: Adding this constraint causes solver timeouts on
examples requiring more than 3 worlds with M>=3, because it introduces a
nested ForAll/Exists quantifier alternation that MBQI handles poorly.

**Soundness for countermodel generation**: Disabling `task_restriction` is
sound for the oracle's primary use case (countermodel generation / validity
checking). The oracle answers "is formula F valid?" by checking whether the
negation ~F is satisfiable. If Z3 finds ~F satisfiable, it returns a
countermodel. If the countermodel contains "phantom" task_rel pairs (pairs not
grounded in any world history), these pairs are still consistent with the three
TaskFrame axioms (nullity, converse, forward_comp). Since BimodalLogic semantics
evaluates formulas over world histories -- not over task_rel pairs directly --
the phantom pairs do not affect the evaluation of temporal/modal operators. The
countermodel is therefore a genuine countermodel in the larger (task_restriction-
free) frame class.

**The phantom task-pair gap**: In the disabled state, task_rel may hold for
(s, d, u) triples that are not realized by any world history. This means the
Z3 oracle operates in a strictly larger frame class than BimodalLogic's
"grounded" frame class. Validity results (UNSAT) from Z3 are therefore
conservative: if Z3 says UNSAT, the formula is valid in the larger class, which
includes BimodalLogic's class. If Z3 says SAT (countermodel), the countermodel
may use phantom pairs, but the formula still fails in that model.

**Post-hoc mitigation**: The `test_frame_class_mapping.py` test suite performs
post-hoc validation of extracted countermodels against the three TaskFrame
axioms (nullity, converse, forward_comp) to confirm the oracle's frame
guarantees are intact in practice.
"""

from __future__ import annotations


class Z3OracleProvider:
    """Z3-based oracle provider for bimodal logic reasoning.

    This class implements the oracle provider interface for the bimodal_harness,
    using Z3 as the underlying SMT solver for temporal and modal reasoning.

    The oracle's `supported_frame_classes = frozenset({"Base"})` indicates that
    the Z3 frame satisfies the three TaskFrame axioms (nullity_identity, converse,
    forward_comp) as documented in the module-level docstring above. See the module
    docstring for the complete Z3-to-BimodalLogic axiom mapping and the soundness
    analysis of the disabled task_restriction constraint.

    NOTE: Placeholder stub - full implementation in task 103.
    """

    supported_frame_classes = frozenset({"Base"})

    pass
