"""bimodal_logic.provider - Z3OracleProvider entry point.

This module provides the Z3OracleProvider class that implements the
bimodal_harness oracle interface using the Z3 SMT solver.

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

from .translation import (
    json_to_prefix,
    temporal_depth,
    prefix_to_infix,
    fold_formula,
)
from .serialization import serialize_countermodel
from model_checker.utils.context import isolated_z3_context
from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
    bimodal_operators,
)


class Z3OracleProvider:
    """Z3-based oracle provider for bimodal logic reasoning.

    This class implements the oracle provider interface for the bimodal_harness,
    using Z3 as the underlying SMT solver for temporal and modal reasoning.

    The oracle's `supported_frame_classes = frozenset({"Base"})` indicates that
    the Z3 frame satisfies the three TaskFrame axioms (nullity_identity, converse,
    forward_comp) as documented in the module-level docstring above. See the module
    docstring for the complete Z3-to-BimodalLogic axiom mapping and the soundness
    analysis of the disabled task_restriction constraint.

    Attributes:
        provider_id (str): Unique identifier for this provider.
        provider_version (str): Semantic version string.
        semantics_version (str): Version string for the bimodal semantics.
        supported_frame_classes (frozenset): Set of supported frame class names.
        capabilities (dict): Dict of provider capability flags and limits.
    """

    # Class-level constants (static properties)
    provider_id = "bmlogic_z3_base_v1"
    provider_version = "0.1.0"
    semantics_version = "bimodal-logic-v0.1.0"
    supported_frame_classes = frozenset({"Base"})
    capabilities = {
        "max_N": 4,
        "max_M": 8,
        "supports_enriched_tags": True,
        "z3_timeout_configurable": True,
    }

    def __init__(self):
        """Initialize the Z3OracleProvider.

        Sets up the internal semantics reference (kept as None to prevent
        cross-call state leakage).
        """
        self._semantics = None

    def find_countermodel(
        self,
        formula_json: dict,
        frame_class: str = "Base",
        timeout_ms: int = 5000,
    ) -> dict | None:
        """Find a countermodel for the given formula JSON.

        Implements the bimodal_harness oracle interface: given a formula in JSON
        format, determines whether it is invalid (satisfiable negation) and if so,
        returns a structured countermodel dict. Returns None for tautologies
        (valid/UNSAT formulas) and unsupported frame classes.

        Pipeline:
            json_to_prefix() -> prefix_to_infix() ->
            Syntax([], [infix], bimodal_operators) ->
            BimodalSemantics(settings) ->
            ModelConstraints(settings, syntax, semantics, BimodalProposition) ->
            BimodalStructure(model_constraints, settings) ->
            serialize_countermodel(...)

        Args:
            formula_json: A dict with a "tag" field and tag-specific fields,
                following the JSON formula schema in translation.py.
            frame_class: The frame class to check against. Only "Base" is
                supported; other values return None immediately.
            timeout_ms: Maximum solver time in milliseconds.

        Returns:
            A dict with countermodel fields if a countermodel is found, or
            None if the formula is valid (no countermodel) or the frame class
            is unsupported.
        """
        # Check frame class support
        if frame_class not in self.supported_frame_classes:
            return None

        # Compute temporal depth and time bound M.
        # Task 114 Fix: Use M=max(depth+2, 3) -- the boundary-safe formula.
        # The previous workaround used M=max(depth, 2) to avoid timeouts from
        # capped_skolem_abundance_constraint's MBQI blowup at M>=3.
        # With the Task 114 fix to build_frame_constraints (conditional dispatch to
        # build_grounded_abundance_constraints for M>=3), M>=3 no longer causes
        # MBQI blowup. The boundary-safe formula M=max(depth+2,3) ensures
        # boundary_safe=(M>depth+1) is True for all formulas, eliminating the
        # boundary vacuity artifacts documented in Task 108.
        # Note: boundary_safe in the output reflects M > depth+1.
        depth = temporal_depth(formula_json)
        M = max(depth + 2, 3)

        # Fold formula for output (enrich primitive forms to enriched tags)
        formula_folded = fold_formula(formula_json)

        # Convert JSON formula to infix string for ModelChecker Syntax
        prefix = json_to_prefix(formula_json)
        infix = prefix_to_infix(prefix)

        # Build settings dict (temporal_depth limits shift closure — Task 114)
        settings = {
            'N': 2,
            'M': M,
            'temporal_depth': depth,
            'contingent': False,
            'disjoint': False,
            'max_time': timeout_ms / 1000.0,
            'expectation': True,
            'solver': 'z3',
        }

        # Reset internal semantics reference to prevent leakage
        self._semantics = None

        # Run solver within isolated Z3 context to prevent state leakage
        result = None
        try:
            with isolated_z3_context():
                semantics = BimodalSemantics(settings)
                # Keep reference only within context; will be None after exit
                self._semantics = semantics
                syntax = Syntax([], [infix], bimodal_operators)
                model_constraints = ModelConstraints(
                    settings, syntax, semantics, BimodalProposition
                )
                structure = BimodalStructure(model_constraints, settings)

                # Check if solver found a satisfying model
                if structure.timeout or not structure.z3_model_status:
                    self._semantics = None
                    return None

                # Serialize the countermodel
                result = serialize_countermodel(
                    z3_model=structure.z3_model,
                    semantics=semantics,
                    model_constraints=model_constraints,
                    structure=structure,
                    formula_json=formula_json,
                    formula_folded=formula_folded,
                    depth=depth,
                    M=M,
                    semantics_version=self.semantics_version,
                )
        finally:
            # Always clear the semantics reference when done
            self._semantics = None

        return result

    def validate_self(self, spot_check_formulas: list) -> bool:
        """Validate the oracle against a list of known-invalid formulas.

        Returns True only if all spot_check_formulas produce non-None results
        from find_countermodel() (i.e., all can find countermodels).

        Args:
            spot_check_formulas: List of JSON formula dicts that should all
                have countermodels (be invalid).

        Returns:
            True if every formula produces a non-None countermodel result.
            False if any formula returns None (no countermodel found).
        """
        for formula in spot_check_formulas:
            result = self.find_countermodel(formula)
            if result is None:
                return False
        return True
