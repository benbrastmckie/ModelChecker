"""Core semantics implementation for the bimodal theory.

This module contains BimodalSemantics, the semantic framework for bimodal logic
(combined tangential modal and temporal operators), providing world-time evaluation
points, the task_rel accessibility relation, and witness-predicate-based modal
accessibility.

Migration Note (2026-05-29):
  The task relation has been refactored from binary task(w, u) to
  ternary task_rel(w, d, u) where d is the explicit duration parameter.

  This aligns with the Lean ProofChecker's taskRel : S -> Q -> S -> Prop
  (see Frame.lean:72). All code using the old binary task() function must
  be updated to use task_rel() with an explicit duration argument.

  For consecutive state transitions (unit duration), use:
    task_rel(state1, 1, state2)
"""

import time

from model_checker import z3_shim as z3

from model_checker.solver import is_true
from model_checker.models.semantic import SemanticDefaults
from model_checker.utils import ForAll, Exists, bitvec_to_worldstate
from model_checker.syntactic.atoms import get_atom_sort

# Witness predicate components (Phase 4 integration)
from .witness_registry import WitnessRegistry
from .witness_constraints import WitnessConstraintGenerator


##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class BimodalSemantics(SemanticDefaults):
    """Defines the semantic model for bimodal logic, including primitive relations,
    frame constraints for task transitions between world states, and evaluation
    of truth conditions."""

    DEFAULT_EXAMPLE_SETTINGS = {
        # Number of world_states
        'N': 2,
        # Number of times
        'M': 2,
        # Whether sentence_letters are assigned to contingent propositions
        'contingent': False,
        # Whether sentence_letters are assigned to distinct world_states
        'disjoint': False,
        # Maximum time Z3 is permitted to look for a model
        'max_time': 1,
        # Whether a model is expected or not (used for unit testing)
        'expectation': True,
        # Number of model iterations to generate
        'iterate': 1,
        # Solver backend: 'z3' or 'cvc5'
        'solver': 'z3',
    }
    
    # Optional: Add bimodal-specific general settings
    ADDITIONAL_GENERAL_SETTINGS = {
        "align_vertically": True,  # Display option for temporal models
    }

    def __init__(self, settings):
        # Initialize the superclass to set defaults and reset global state
        super().__init__(settings)

        # Task 114: temporal_depth limits shift closure to formula's nesting depth.
        # None = use capped Skolem (backward compat for direct BimodalSemantics use).
        # 0 = skip abundance (oracle sets this for depth-0 formulas).
        # >0 = depth-bounded Skolem at M>=3 (oracle sets this for temporal formulas).
        self.temporal_depth = settings.get('temporal_depth', None)

        # Initialize always true/false worlds, updated in the model_structure
        self.all_true = {}
        self.all_false = {}

        # Initialize witness components (Phase 4: Modal Operator Integration)
        self.witness_registry = WitnessRegistry(self.N, self.M)
        self.constraint_generator = WitnessConstraintGenerator(self)

        # Initialize sorts, primitives, and frame_constraints
        self.define_sorts()
        self.define_primitives()
        self.frame_constraints = self.build_frame_constraints()
        self.premise_behavior, self.conclusion_behavior = self.define_invalidity()
        
    def _reset_global_state(self):
        """Reset any global state that could cause interference between examples.
        
        This implementation ensures that each new instance of BimodalSemantics 
        starts with a clean slate by resetting all shared resources that could
        potentially cause interference between different examples.
        
        IMPORTANT: This method is critical for ensuring that examples run independently
        and don't affect each other's results or performance. The BimodalSemantics
        implementation demonstrates best practices for implementing this method in
        theory-specific semantics classes:
        
        1. Call the parent implementation first using super()._reset_global_state()
        2. Clear any theory-specific cache dictionaries
        3. Reset mutable state while preserving necessary immutable definitions
        4. Explicitly force garbage collection to release Z3 resources
        
        For more information, see theory_lib/notes/separation.md.
        """
        # Call parent implementation first
        super()._reset_global_state()
        
        # Clear any cached world time intervals from previous examples
        self.world_time_intervals = {}
        
        # Clear model cache values
        if hasattr(self, 'model_structure'):
            delattr(self, 'model_structure')
        
        # Reset mutable caches
        self.all_true = {}
        self.all_false = {}
        
        # Reset main point references (but not the definitions created in __init__)
        self.main_world = 0
        self.main_time = None
        self.main_point = None
        
        # Force garbage collection to free any Z3 resources
        import gc
        gc.collect()
        

    def define_sorts(self):
        """Define the Z3 sorts used in the bimodal logic model.

        Create three sorts:
        - WorldStateSort: BitVecSort for representing world states as bitvectors
        - TimeSort: IntSort for representing time points
        - WorldIdSort: IntSort for mapping world IDs to world arrays
        """            
        self.WorldStateSort = z3.BitVecSort(self.N)
        self.TimeSort = z3.IntSort()
        self.WorldIdSort = z3.IntSort()


    def define_primitives(self):
        """Define the Z3 primitive functions and relations used in the bimodal logic model.

        In bimodal logic we distinguish between:
        - World States: Instantaneous configurations of the system (e.g., {a, b, c})
        - World Histories: Temporally extended sequences of states that follow lawful transitions

        Primitives:
        - task_rel: Ternary relation R(s, d, u) where:
            - s: source world state (BitVec[N])
            - d: duration of task (Int)
            - u: target world state (BitVec[N])
          Represents: "state s transitions to state u over duration d"

          ProofChecker Alignment: Matches taskRel : S -> Q -> S -> Prop
          from Frame.lean:72. The quantity type Q is represented as Int.

        - world_function: A mapping from world IDs to world histories (arrays mapping time -> world state)
        - truth_condition: A function assigning truth values to atomic propositions at instantaneous world states
        - main_world: The primary world history used for evaluation (world_function applied to ID 0)
        - main_time: The time point at which sentences are evaluated
        - main_point: Dictionary containing the main world history and evaluation time
        - is_world: A boolean function indicating whether a world_id maps to a valid world history
        """
        # Define the ternary task relation between world states with explicit duration
        # Signature: task_rel(source_state, duration, target_state) -> Bool
        # Aligns with ProofChecker's taskRel : S -> Q -> S -> Prop (Frame.lean:72)
        self.task_rel = z3.Function(
            "TaskRel",
            self.WorldStateSort,  # source state: BitVec[N]
            z3.IntSort(),         # duration: Int (matches TimeSort)
            self.WorldStateSort,  # target state: BitVec[N]
            z3.BoolSort()         # result: Bool
        )

        # Mapping from world IDs to world histories (arrays from time to state)
        self.world_function = z3.Function(
            'world_function', 
            self.WorldIdSort,  # Input: world ID 
            z3.ArraySort(self.TimeSort, self.WorldStateSort)  # Output: world history
        )

        # Function to determine if a world_id maps to a valid world history
        self.is_world = z3.Function(
            'is_world',
            self.WorldIdSort,  # Input: world ID
            z3.BoolSort()      # Output: whether it's a valid world history
        )

        # Set a reasonable limit on world IDs for efficiency
        self.max_world_id = self.M * (2 ** (self.M * self.N))  # Number of possible world histories
        
        # Truth condition for atomic propositions at world states
        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
            get_atom_sort(),
            z3.BoolSort()
        )

        # Define interval tracking functions
        self.world_interval_start = z3.Function(
            'world_interval_start',
            self.WorldIdSort,  # World ID
            self.TimeSort      # Start time of interval
        )
        
        self.world_interval_end = z3.Function(
            'world_interval_end',
            self.WorldIdSort,  # World ID
            self.TimeSort      # End time of interval
        )
        
        # Dictionary to store world time intervals after extraction
        self.world_time_intervals = {}
        
        # Main point of evaluation includes a world ID and time
        self.main_world = 0             # Store world ID, not array reference
        self.main_time = z3.IntVal(0)   # Fix the main time to 0
        self.main_point = {
            "world": self.main_world,
            "time": self.main_time,
        }

    def is_valid_duration(self, duration):
        """Check if a duration is within the valid range for the time domain.

        Valid durations range from -(M-1) to (M-1) inclusive, which corresponds
        to the maximum possible temporal shift within the time domain (-M, M).

        Args:
            duration: The duration value to check (Z3 Int or Python int)

        Returns:
            Z3 formula that is true if the duration is within valid bounds

        ProofChecker Alignment: Duration bounds ensure task transitions stay
        within the frame's time domain D.
        """
        return z3.And(duration > -self.M, duration < self.M)

    def build_task_rel_at(self, world, time, duration):
        """Build a task_rel constraint at a specific world and time with given duration.

        This helper constructs the task relation between the state at (world, time)
        and the state at (world, time + duration).

        Args:
            world: World ID (Z3 Int or Python int)
            time: Time point (Z3 Int or Python int)
            duration: Duration of the task (Z3 Int or Python int)

        Returns:
            Z3 formula: task_rel(state_at_time, duration, state_at_time_plus_duration)

        ProofChecker Alignment: Matches the pattern used in IsEvolution where
        task_rel relates states at different times in the same world history.
        """
        source_state = z3.Select(self.world_function(world), time)
        target_state = z3.Select(self.world_function(world), time + duration)
        return self.task_rel(source_state, duration, target_state)

    def build_nullity_identity_constraint(self):
        """Build constraint: task_rel(w, 0, u) <-> w = u

        Zero duration task implies and is implied by state identity.
        A task of zero duration is a self-task: it relates a state to itself
        and only to itself.

        ProofChecker Alignment: Corresponds to the property that self-tasks
        (tasks of zero duration) relate a state to itself. Aligns with the
        nullity axiom of the additive group structure on durations (Q in Lean).

        Returns:
            Z3 ForAll formula asserting that task_rel(w, 0, u) <-> (w == u)
            for all world states w, u : BitVec[N]
        """
        w = z3.BitVec('nullity_w', self.N)
        u = z3.BitVec('nullity_u', self.N)

        # Biconditional: task_rel(w, 0, u) iff w == u
        # In Z3, A == B for BoolRef expressions is equivalent to Iff(A, B)
        return z3.ForAll(
            [w, u],
            self.task_rel(w, z3.IntVal(0), u) == (w == u)
        )

    def build_converse_constraint(self):
        """Build time reversal symmetry constraint: task_rel(w, d, u) <-> task_rel(u, -d, w)

        Going from world state w to u in duration d is equivalent to going
        from u to w in duration -d (time reversal). This is the group converse
        property of the additive group structure on durations.

        The constraint is guarded by duration validity to ensure both d and -d
        are within the time domain bounds.

        ProofChecker Alignment: Corresponds to the group converse property
        of the additive group structure on durations (Q in Lean), where Q is an
        AddCommGroup. Relates to the inverse element property: if task_rel(s, d, u)
        then task_rel(u, -d, s).

        Returns:
            Z3 ForAll formula asserting that under valid duration guards,
            task_rel(w, d, u) <-> task_rel(u, -d, w)
            for all world states w, u : BitVec[N] and duration d : Int
        """
        w = z3.BitVec('converse_w', self.N)
        u = z3.BitVec('converse_u', self.N)
        d = z3.Int('converse_d')

        # Guard: both d and -d must be within valid duration bounds
        guard = z3.And(
            self.is_valid_duration(d),
            self.is_valid_duration(-d)
        )

        # Biconditional under guard: task_rel(w, d, u) <-> task_rel(u, -d, w)
        return z3.ForAll(
            [w, u, d],
            z3.Implies(
                guard,
                self.task_rel(w, d, u) == self.task_rel(u, -d, w)
            )
        )

    def build_forward_comp_constraint(self):
        """Build compositionality constraint for sequential tasks.

        If task_rel(w, d1, v) and task_rel(v, d2, u) then task_rel(w, d1+d2, u).
        Sequential tasks compose: the composition of two tasks is itself a task
        whose duration is the sum of the component durations.

        The constraint uses Z3 multi-patterns on the two premise terms to guide
        quantifier instantiation and reduce solver overhead from the 5 quantified
        variables (w, v, u, d1, d2).

        ProofChecker Alignment: Matches Compositional.compose from Frame.lean:112-114:
          compose : forall s t r : S, forall x y : Q,
            f.taskRel s x t -> f.taskRel t y r -> f.taskRel s (x + y) r

        Returns:
            Z3 ForAll formula with multi-pattern asserting compositionality:
            (task_rel(w,d1,v) AND task_rel(v,d2,u) AND valid_durations) ->
            task_rel(w, d1+d2, u)
            for all w, v, u : BitVec[N] and d1, d2 : Int
        """
        w = z3.BitVec('comp_w', self.N)
        v = z3.BitVec('comp_v', self.N)
        u = z3.BitVec('comp_u', self.N)
        d1 = z3.Int('comp_d1')
        d2 = z3.Int('comp_d2')

        body = z3.Implies(
            z3.And(
                # Premise: both component tasks exist
                self.task_rel(w, d1, v),
                self.task_rel(v, d2, u),
                # Duration validity guards to narrow instantiation scope
                self.is_valid_duration(d1),
                self.is_valid_duration(d2),
                self.is_valid_duration(d1 + d2)
            ),
            # Conclusion: composed task exists with summed duration
            self.task_rel(w, d1 + d2, u)
        )

        # Multi-pattern on the two premise terms guides Z3 to instantiate
        # this axiom only when both component tasks are already in the solver's
        # ground term set, reducing spurious instantiations.
        return z3.ForAll(
            [w, v, u, d1, d2],
            body,
            patterns=[
                z3.MultiPattern(self.task_rel(w, d1, v), self.task_rel(v, d2, u))
            ]
        )

    def ForAllTime(self, world, time_var, body):
        """Universal quantification over all valid times in domain D.

        ProofChecker Alignment: Quantifies over ALL times in domain D, not just the
        world's interval. This matches the ProofChecker (Lean) semantics where
        temporal operators like G and H quantify over the global time domain.

        Boundary Vacuity Mechanism:
            The domain D = (-M, M) is a finite open interval with 2*M-1 integer time
            points: {-(M-1), ..., 0, ..., M-1}. ForAllTime universally quantifies
            over all times in D using is_valid_time(time_var) as the guard.

            Boundary vacuity occurs when a temporal operator is evaluated near the
            domain boundary. For example, G(p) evaluated at t = M-1 (the last future
            time point) is vacuously true: the universal quantifier "for all t' > M-1
            in D" is satisfied vacuously because no such t' exists.

            For a formula of depth d, boundary vacuity can propagate:
            - G(G(p)) at t=M-1: outer G vacuously true (no t'>M-1)
            - G(G(p)) at t=M-2: outer G checks t=M-1, inner G(p) at t=M-1 vacuously true
            - This means with insufficient M, a depth-d formula may produce a spurious
              SAT/UNSAT result due to vacuous evaluation near the boundary.

            Safety criterion: M >= d+2 ensures that evaluation from t=0 along a
            depth-d chain reaches at most t=d, which satisfies M-1-d >= 1, meaning
            at least one more time point exists. The boundary time t=M-1 is unreachable
            from t=0 via a chain of length d when M >= d+2.

        Args:
            world: World ID (z3.IntSort) - kept for API compatibility, not used for scope
            time_var: Time variable (z3.IntSort) to quantify over
            body: Z3 expression to evaluate for each time

        Returns:
            z3.ForAll expression with validity implications over domain D
        """
        return z3.ForAll(
            time_var,
            z3.Implies(
                self.is_valid_time(time_var),  # All times in D, not world-specific
                body
            )
        )

    def ExistsTime(self, world, time_var, body):
        """Existential quantification over valid times in domain D.

        ProofChecker Alignment: Quantifies over ALL times in domain D, not just the
        world's interval. This matches the ProofChecker (Lean) semantics where
        temporal operators like F and P quantify over the global time domain.

        Args:
            world: World ID (z3.IntSort) - kept for API compatibility, not used for scope
            time_var: Time variable (z3.IntSort) to quantify over
            body: Z3 expression to evaluate

        Returns:
            z3.Exists expression with validity conjunction over domain D
        """
        return z3.Exists(
            time_var,
            z3.And(
                self.is_valid_time(time_var),  # All times in D, not world-specific
                body
            )
        )

    def _get_formula_string(self, formula_ast):
        """Convert formula AST to unique string identifier for witness registration.

        Args:
            formula_ast: Sentence object representing the formula

        Returns:
            str: Unique string identifier (e.g., "box_p", "diamond_and_p_q")

        Note: This is a simple implementation. For production, might need to handle
        more complex formulas and ensure uniqueness across nested structures.
        """
        # Base case: sentence letter
        if hasattr(formula_ast, 'sentence_letter') and formula_ast.sentence_letter:
            return str(formula_ast.sentence_letter)

        # Recursive case: operator with arguments
        if hasattr(formula_ast, 'operator') and formula_ast.operator:
            operator_name = formula_ast.operator.name.replace('\\', '')  # Remove backslash

            if hasattr(formula_ast, 'arguments') and formula_ast.arguments:
                # Build argument strings recursively
                arg_strings = [self._get_formula_string(arg) for arg in formula_ast.arguments]
                args_combined = '_'.join(arg_strings)
                return f"{operator_name}_{args_combined}"
            else:
                return operator_name

        # Fallback: use string representation
        return str(formula_ast)

    def build_frame_constraints(self):
        """Build the frame constraints for the bimodal logic model.

        Optimization history (Task 97, 2026-05-29):
          Phase 2: Removed tautological classical_truth constraint (Or(P, Not(P)));
                   world_uniqueness grounding (array inequality) was reverted due to
                   regressions; the original ForAll/Exists formulation is retained.

        Task 98 investigation (2026-05-29):
          Tested build_grounded_abundance_constraints() to replace the doubly-quantified
          capped_skolem_abundance_constraint, but found it caused regressions for both
          SAT and UNSAT examples. OOM is handled by max_memory=4096 in Z3SolverAdapter.

        ## Frame Hierarchy and TaskFrame Axiom Mapping

        This method constructs 11 constraints total, split into two categories:

        **TaskFrame Axioms (items 7-9)** -- correspond directly to BimodalLogic's
        `TaskFrame` structure fields in Frame.lean. These are the semantic guarantees
        that justify `supported_frame_classes = frozenset({"Base"})` in the oracle:

          7. nullity_identity  -> TaskFrame.nullity:  task_rel(w, 0, u) ↔ w = u
          8. converse          -> TaskFrame.converse: task_rel(w, d, u) ↔ task_rel(u, -d, w)
          9. forward_comp      -> TaskFrame.compose:  task_rel(w,d1,v) ∧ task_rel(v,d2,u) → task_rel(w,d1+d2,u)

        **Model-building constraints (items 1-6, 8-9)** -- not TaskFrame axioms; these
        structure the Z3 search space to produce well-formed countermodels:

          1. valid_main_world      - main_world is a valid world ID
          2. valid_main_time       - main_time is in the time domain
          3. enumeration           - world IDs start at 0, are non-negative
          4. convex_world_ordering - world IDs form a contiguous sequence
          5. world_interval        - each world has exactly one valid time interval
          6. lawful                - consecutive world-states connected via task_rel(s, 1, s')
          8. skolem_abundance      - time-shifted world copies exist (ShiftClosed alignment)
          9. world_uniqueness      - distinct world IDs map to distinct histories

        **Disabled constraint (item 10)** -- task_restriction is preserved but not active:

         10. task_restriction (DISABLED) - would ground every task_rel pair in a world
             history; disabled due to solver performance (nested ForAll/Exists causes
             MBQI timeouts). See the soundness analysis comment near the disabled
             constraint for a full explanation of why this is sound for countermodel
             generation. The post-hoc test suite (test_frame_class_mapping.py)
             validates the three TaskFrame axioms hold in extracted countermodels.

        This method constructs the fundamental constraints that define the behavior of the model:
        1. Time constraints - Ensures main_time is within valid range
        2. World enumeration - Ensures world IDs start at 0 and are contiguous
        3. Lawful transitions - Each world history must follow the task relation between consecutive states
        4. World interval constraint - Ensures each world has a valid time interval
        5. Abundance constraint - Ensures time-shifted worlds exist for all valid shifts (capped Skolem)
        6. World uniqueness - Each world ID maps to a distinct world history
        7-9. Frame axioms - TaskFrame constraints (nullity, converse, compositionality)

        The abundance constraint (item 5) uses capped_skolem_abundance_constraint which
        provides time-shifted world copies for all shift amounts that keep the shifted
        interval within the global time range. This aligns with:
        - JPL paper (app:auto_existence, lines 2154-2178): closed under arbitrary time shifts
        - Lean BimodalLogic (ShiftClosed, Truth.lean line 295): Omega is shift-closed

        Together with removing the is_valid_time_for_world guard from NecessityOperator
        (operators.py), these constraints make the perpetuity principles BM_TH_1
        (Box A -> Future A) and BM_TH_2 (Box A -> Past A) valid (no countermodel).
        Sufficient M (>=3) is needed for the shift closure to cover all relevant shifts.

        The frame constraints ensure that world histories represent lawful evolutions of world states
        over time, following the task relation which specifies valid state transitions.

        Returns:
            list: A list of Z3 constraints that define the frame conditions for the model
        """
        # 1. The main_world must be valid
        valid_main_world = self.is_world(self.main_world)

        # 2. The main_time must be valid
        valid_main_time = self.is_valid_time(self.main_time)

        # NOTE: classical_truth (Or(P, Not(P))) was removed in Task 97 Phase 2.
        # It was a tautology (always true by LEM) and added no solver information,
        # only wasting E-matching index budget on a trivially satisfied constraint.

        # 3. World enumeration starts at 0
        enumerate_world = z3.Int('enumerate_world')
        enumeration_constraint = z3.ForAll(
            [enumerate_world],
            z3.Implies(
                # If enumerate_world is a world
                self.is_world(enumerate_world),
                # Then it's non-negative
                enumerate_world >= 0,
            )
        )
        
        # 4. The worlds form a convex ordering (no gaps)
        # Implements "lazy" world creation by ensuring worlds are created in sequence
        convex_world = z3.Int('convex_world')
        convex_world_ordering = z3.ForAll(
            [convex_world],
            z3.Implies(
                # If both:
                z3.And(
                    # The convex_world is a world
                    self.is_world(convex_world),
                    # And greater than 0
                    convex_world > 0,
                ),
                # Then world_id - 1 must be valid
                self.is_world(convex_world - 1)
            )
        )

        # 5. World interval constraint -- placed before lawful so Z3's MBQI can seed
        # interval bounds before instantiating the more complex lawful axiom.
        # NOTE: time_interval_constraint() is a grounded (non-quantified) alternative.
        # It was tested but is not currently used (world_interval_constraint() is active).
        # Both produce equivalent valid-world interval constraints; the grounded form
        # may be faster for small max_world_id but was not benchmarked in Task 97.
        world_interval = self.world_interval_constraint()

        # 6. Worlds are lawful (each world state has task_rel to its successor with unit duration)
        # ProofChecker Alignment: Uses task_rel with explicit duration=1 for consecutive states
        lawful_world = z3.Int('lawful_world_id')
        lawful_time = z3.Int('lawful_time')
        lawful = z3.ForAll(
            [lawful_world, lawful_time],
            # If for any lawful_world and lawful time
            z3.Implies(
                z3.And(
                    # The lawful_world is a valid world
                    self.is_world(lawful_world),
                    # The lawful_time is in (-M - 1, M - 1), so has a successor
                    self.is_valid_time(lawful_time, -1),
                    # The lawful_time is in the lawful_world
                    self.is_valid_time_for_world(lawful_world, lawful_time),
                    # The successor of the lawful_time is in the lawful_world
                    self.is_valid_time_for_world(lawful_world, lawful_time + 1),
                ),
                # Then there is a task with unit duration (duration = 1)
                self.task_rel(
                    # From the lawful_world at the lawful_time
                    z3.Select(self.world_function(lawful_world), lawful_time),
                    # With unit duration (explicit)
                    z3.IntVal(1),
                    # To the lawful_world at the successor of the lawful_time
                    z3.Select(self.world_function(lawful_world), lawful_time + 1)
                )
            )
        )

        # 7. Frame axioms: TaskFrame constraints aligning with ProofChecker's Frame.lean
        # nullity_identity: task_rel(w, 0, u) <-> w == u
        nullity_identity = self.build_nullity_identity_constraint()
        # converse: task_rel(w, d, u) <-> task_rel(u, -d, w) under duration validity guards
        converse = self.build_converse_constraint()
        # forward_comp: compositionality -- if task_rel(w,d1,v) and task_rel(v,d2,u) then task_rel(w,d1+d2,u)
        forward_comp = self.build_forward_comp_constraint()

        # 8. All valid time-shifted worlds exist (depth-aware)
        # Task 114 Fix: When temporal_depth is explicitly set via settings:
        # - 0: skip abundance (oracle depth-0 formulas, no temporal operators)
        # - >0 at M>=3: depth-bounded Skolem (shift range = temporal_depth)
        # When temporal_depth is None (not in settings): use capped Skolem
        # at all M values (backward compat for direct BimodalSemantics use).
        temporal_depth = getattr(self, 'temporal_depth', None)
        if temporal_depth is None:
            skolem_abundance = [self.capped_skolem_abundance_constraint()]
        elif temporal_depth == 0:
            skolem_abundance = []
        elif self.M <= 2:
            skolem_abundance = [self.capped_skolem_abundance_constraint()]
        else:
            skolem_abundance = [self.depth_bounded_skolem_abundance_constraint(
                max_shift=temporal_depth
            )]

        # 9. Every valid world is unique
        # Original ForAll/Exists formulation preserved: worlds must differ at a time
        # point that is valid for BOTH worlds. Array inequality was tested but caused
        # regressions (8 failures) because Z3 array disequality checks ALL indices,
        # not just the shared interval, conflicting with valid_array_domain constraints.
        world_one = z3.Int('world_one')
        world_two = z3.Int('world_two')
        some_time = z3.Int('some_time')
        world_uniqueness = z3.ForAll(
            [world_one, world_two],
            z3.Implies(
                z3.And(
                    self.is_world(world_one),
                    self.is_world(world_two),
                    world_one != world_two
                ),
                # Worlds must differ at some time point that is valid for both
                z3.Exists(
                    [some_time],
                    z3.And(
                        self.is_valid_time(some_time),
                        self.is_valid_time_for_world(world_one, some_time),
                        self.is_valid_time_for_world(world_two, some_time),
                        z3.Select(self.world_function(world_one), some_time) !=
                        z3.Select(self.world_function(world_two), some_time)
                    )
                )
            )
        )

        # 10. Task relation only holds between states in lawful world histories
        # ProofChecker Alignment: task_rel(s, d, u) requires existence of a world where
        # the transition from s to u over duration d is realized
        #
        # SOUNDNESS ANALYSIS FOR DISABLED task_restriction (Task 110)
        # ==============================================================
        # This constraint is currently DISABLED (see the return list at the end of this
        # method). Disabling it is SOUND for the oracle's primary use case (countermodel
        # generation / formula validity checking). Here is the full analysis:
        #
        # What task_restriction would enforce:
        #   For every task_rel(s, d, u) that holds in the model, there must exist a
        #   world w and time t such that w(t) = s and w(t+d) = u (the transition is
        #   "grounded" in a concrete world history).
        #
        # Why it is disabled:
        #   The constraint introduces a nested ForAll/Exists quantifier alternation
        #   (ForAll[state, duration, next_state], Exists[world, time]) that Z3's MBQI
        #   (Model-Based Quantifier Instantiation) handles poorly. With M>=3 and more
        #   than 3 worlds, adding task_restriction causes solver timeouts on examples
        #   that previously solved in seconds. Performance regression was confirmed
        #   empirically during Task 91/97 implementation.
        #
        # Soundness for UNSAT (theorem validation):
        #   If the oracle returns UNSAT (formula is valid), this holds in the larger
        #   frame class WITHOUT task_restriction. Since BimodalLogic's semantics uses
        #   world histories (not task_rel pairs) to evaluate formulas, and UNSAT means
        #   no countermodel exists even with phantom task_rel pairs, the UNSAT result
        #   is conservative: it is at least as strong as validity in the grounded class.
        #
        # Soundness for SAT (countermodel generation):
        #   If the oracle returns SAT (countermodel found), the countermodel may contain
        #   "phantom" task_rel pairs -- pairs (s, d, u) where task_rel(s,d,u) holds but
        #   no world w with w(t)=s and w(t+d)=u exists. Importantly:
        #   1. The three TaskFrame axioms (nullity, converse, forward_comp) still hold.
        #   2. BimodalLogic's modal/temporal operators are evaluated over world histories
        #      (world_function arrays), not over task_rel pairs directly. Phantom pairs
        #      do not affect operator truth values.
        #   3. The formula being falsified by the countermodel depends only on the world
        #      history structure and the truth values of atomic propositions, not on
        #      whether task_rel is grounded. The countermodel is therefore a genuine
        #      countermodel in the larger (phantom-pair-allowed) frame class.
        #
        # The phantom task-pair gap:
        #   Operating without task_restriction means the oracle's frame class is strictly
        #   larger than BimodalLogic's "grounded TaskFrame" class. UNSAT results transfer
        #   upward (sound); SAT results (countermodels) may not transfer downward (the
        #   formula might still be valid in the strictly grounded class). In practice,
        #   the oracle is used to find countermodels (SAT) for formula falsification and
        #   to confirm tautologies (UNSAT), so this asymmetry is acceptable.
        #
        # Post-hoc mitigation:
        #   The test_frame_class_mapping.py test suite validates that extracted
        #   countermodels satisfy the three TaskFrame axioms post-hoc, confirming the
        #   oracle's frame guarantees are intact even without task_restriction.
        some_state = z3.BitVec('task_restrict_some_state', self.N)
        some_duration = z3.Int('task_restrict_duration')
        next_state = z3.BitVec('task_restrict_next_state', self.N)
        task_world = z3.Int('task_world')
        time_shifted = z3.Int('time_shifted')
        task_restriction = z3.ForAll(
            [some_state, some_duration, next_state],
            z3.Implies(
                # If there is a task_rel from some_state to next_state with some_duration
                self.task_rel(some_state, some_duration, next_state),
                # Then for some task_world at time_shifted:
                z3.Exists(
                    [task_world, time_shifted],
                    z3.And(
                        # The task_world is a valid world
                        self.is_world(task_world),
                        # Duration bounds: must fit within time domain
                        self.is_valid_duration(some_duration),
                        # Time validity for source endpoint
                        self.is_valid_time(time_shifted),
                        # Time validity for target endpoint
                        self.is_valid_time(time_shifted + some_duration),
                        # Source time is in the task_world
                        self.is_valid_time_for_world(task_world, time_shifted),
                        # Target time is in the task_world
                        self.is_valid_time_for_world(task_world, time_shifted + some_duration),
                        # The task_world is in some_state at time_shifted
                        some_state == z3.Select(self.world_function(task_world), time_shifted),
                        # And the task_world is in next_state at time_shifted + some_duration
                        next_state == z3.Select(self.world_function(task_world), time_shifted + some_duration)
                    )
                )
            )
        )

        # 11. Task state minimization - Encourages minimal changes between consecutive world states
        task_minimization = self.build_task_minimization_constraint()

        return [
            # NOTE: order matters for Z3 MBQI seed quality.
            # World structure constraints first (ground facts), then interval bounds
            # (so MBQI can seed world intervals before the lawful axiom fires),
            # then frame axioms, then abundance (shift closure), then uniqueness.
            valid_main_world,
            valid_main_time,
            enumeration_constraint,
            convex_world_ordering,
            world_interval,       # interval bounds before lawful (MBQI seeding)
            lawful,
            # Frame axioms (TaskFrame, ProofChecker alignment):
            nullity_identity,
            converse,
            forward_comp,
            *skolem_abundance,    # list of constraints (1 for M=2, multiple for M>=3)
            world_uniqueness,
            # MAYBE (not yet enabled, preserved for future experimentation):
            # task_restriction,     # restricts task_rel to lawful histories
            # task_minimization,    # encourages minimal state changes
        ]

    def is_valid_time(self, given_time, offset=0):
        """Check if a time point exists in the expanded time domain.

        Modified to support an expanded time domain that includes negative values.

        Domain Structure:
            The time domain is the open integer interval (-M, M), giving the 2*M-1
            integer time points: {-(M-1), -(M-2), ..., -1, 0, 1, ..., M-2, M-1}.
            Evaluation is always fixed at t=0 (the main_time constraint).

            Boundary safety: For a formula of temporal depth d, M >= d+2 ensures
            that genuine (non-vacuous) evaluation can occur from t=0 along a
            depth-d chain. With M >= d+2, a chain of d future steps from t=0
            reaches at most t=d, which satisfies M-1-d >= 1 (the point t=d is
            not the last time point, so further evaluation is non-vacuous).

            Equivalently, M >= d+2 ensures d+1 future time points exist from t=0:
            {1, 2, ..., d+1}, all within the domain (-M, M).

        Args:
            given_time: The time point to check (Z3 Int expression)
            offset: Optional offset to add to the bounds (used for shifted checks)

        Returns:
            Z3 formula that is true if the time point exists in (-M+offset, M+offset)
        """
        # Allow times in the range (-M, M)
        return z3.And(given_time > -self.M + offset, given_time < self.M + offset)
        
    def is_valid_time_for_world(self, given_world, given_time):
        """Check if a time is valid for a specific world.
        
        Args:
            world_id: World identifier
            time: Time point to check
            
        Returns:
            Z3 formula that is true if the time is within the world's interval
        """
        return z3.And(
            given_time >= self.world_interval_start(given_world),
            given_time <= self.world_interval_end(given_world)
        )

    def can_shift_forward(self, given_world):
        """Check if a world can be shifted forward by 1 (Z3 expression).
        
        Args:
            world_id: World identifier
            
        Returns:
            Z3 formula that is true if the world can be shifted forward
        """
        # A world can shift forward if its end time + 1 is still within global range
        return self.world_interval_end(given_world) < z3.IntVal(self.M - 1)
    
    def is_shifted_by(self, source_world, shift, target_world):
        """Predicate that target_id is a world shifted from source_id by shift amount.
        
        Args:
            source_id: Source world identifier
            shift: Shift amount
            target_id: Target world identifier
            
        Returns:
            Z3 formula that is true if target is shifted from source by amount
        """
        return z3.And(
            # Target interval must be shifted by the specified amount
            self.world_interval_start(target_world) == self.world_interval_start(source_world) + z3.IntVal(shift),
            self.world_interval_end(target_world) == self.world_interval_end(source_world) + z3.IntVal(shift),
            # World states must match when shifted
            self.matching_states_when_shifted(source_world, shift, target_world)
        )

    def matching_states_when_shifted(self, source_world, shift, target_world):
        """Check if states match when shifted between world arrays.
        
        Args:
            source_id: Source world identifier
            shift: Shift amount
            target_id: Target world identifier
            
        Returns:
            Z3 formula that is true if states match when shifted
        """
        time = z3.Int('shift_check_time')
        source_array = self.world_function(source_world)
        target_array = self.world_function(target_world)
        
        return z3.ForAll(
            [time],
            z3.Implies(
                z3.And(
                    # Time is within source interval
                    z3.And(
                        time >= self.world_interval_start(source_world),
                        time <= self.world_interval_end(source_world)
                    ),
                    # Shifted time is within target interval
                    z3.And(
                        time + z3.IntVal(shift) >= self.world_interval_start(target_world),
                        time + z3.IntVal(shift) <= self.world_interval_end(target_world)
                    )
                ),
                # States must match when shifted
                z3.Select(source_array, time) == z3.Select(target_array, time + z3.IntVal(shift))
            )
        )
    
    def can_shift_backward(self, world_id):
        """Check if a world can be shifted backward by 1 (Z3 expression).
        
        Args:
            world_id: World identifier
            
        Returns:
            Z3 formula that is true if the world can be shifted backward
        """
        # A world can shift backward if its start time - 1 is still within global range
        return self.world_interval_start(world_id) > z3.IntVal(-self.M + 1)
    
    def world_interval_constraint(self):
        """Build constraint ensuring each world has a valid time interval."""
        # Define all valid time intervals
        time_intervals = self.generate_time_intervals(self.M)
        
        # Variable for world being constrained
        interval_world = z3.Int('interval_world')
        
        # Stock of intervals to populate
        interval_options = []

        # For any time interval in time_intervals with start_time and end_time
        for start_time, end_time in time_intervals:
            interval_constraint = z3.And(
                # The interval_world starts at the start_time and ends at the end_time
                self.has_interval(interval_world, start_time, end_time),
                # Constraints to ensure the world array is defined only for this interval
                self.valid_array_domain(interval_world, start_time, end_time)
            )
            interval_options.append(interval_constraint)
        
        # For any interval_world
        world_interval_constraint = z3.ForAll(
            [interval_world],
            z3.Implies(
                # If interval_world is a valid world
                self.is_world(interval_world),
                # Must have exactly one of the valid time intervals in time_intervals
                z3.Or(*interval_options)
            )
        )
        return world_interval_constraint

    def time_interval_constraint(self):
        """Build an optimized constraint ensuring each world has a valid time interval.
        
        This optimized version avoids nested universal quantifiers by directly
        constraining the interval functions to specific values for each world.
        It pre-computes the valid interval options and creates direct constraints
        rather than using nested quantification.
        
        Returns:
            Z3 formula that constrains world intervals to valid values
        """
        # Generate valid time intervals
        time_intervals = self.generate_time_intervals(self.M)
        
        # Variable for world being constrained
        interval_world = z3.Int('interval_world')
        
        # Create direct mapping for interval bounds
        interval_constraints = []
        
        # For each valid world ID, create direct interval constraints
        for world_id in range(self.max_world_id):
            # Create a condition for this specific world ID
            world_condition = (interval_world == world_id)
            
            # Create interval options for this world
            world_interval_options = []
            
            # For any time interval in time_intervals with start_time and end_time
            for i, (start_time, end_time) in enumerate(time_intervals):
                # Create a direct constraint for this interval option
                interval_option = z3.And(
                    self.world_interval_start(world_id) == z3.IntVal(start_time),
                    self.world_interval_end(world_id) == z3.IntVal(end_time)
                )
                world_interval_options.append(interval_option)
            
            # A world must have exactly one of the valid intervals if it exists
            world_constraint = z3.Implies(
                self.is_world(world_id),
                z3.Or(*world_interval_options)
            )
            
            interval_constraints.append(world_constraint)
        
        # Combine all world constraints
        return z3.And(*interval_constraints)

    def has_interval(self, given_world, start_time, end_time):
        """Predicate indicating a world has a specific interval.
        
        Args:
            world_id: World identifier
            start: Start time of interval
            end: End time of interval
            
        Returns:
            Z3 formula that is true if world has the specified interval
        """
        return z3.And(
            # The given_world starts at start_time
            self.world_interval_start(given_world) == z3.IntVal(start_time),
            # The given_world ends at end_time
            self.world_interval_end(given_world) == z3.IntVal(end_time)
        )
    
    def valid_array_domain(self, given_world, start_time, end_time):
        """Ensure world array is defined only for times in its interval.
        
        Args:
            world_id: World identifier
            start: Start time of interval
            end: End time of interval
            
        Returns:
            Z3 formula that ensures array is properly defined for this interval
        """
        other_time = z3.Int('other_time')
        return z3.ForAll(
            [other_time],
            z3.Implies(
                # If other_time is valid in the given_world
                self.is_valid_time_for_world(given_world, other_time),
                # Then other_time is both:
                z3.And(
                    # At or after the start_time
                    z3.IntVal(start_time) <= other_time,
                    # And at or before the end_time
                    other_time <= z3.IntVal(end_time)
                )
            )
        )
    
    def build_abundance_constraint(self):
        """Build constraint ensuring necessary time-shifted worlds exist.

        DEPRECATED: Replaced by capped_skolem_abundance_constraint which provides
        full shift coverage (not just +/-1) with better Z3 performance characteristics.
        This method is retained for reference and fallback comparison.

        The abundance property ensures that for any world that can be shifted forward
        or backward in time (while staying within valid time bounds), there exists a
        corresponding world that represents that time shift.
        """
        source_world = z3.Int('abundance_source_id')
        forward_world = z3.Int('forward_world')
        backwards_world = z3.Int('backwards_world')
        
        # Each world must have appropriate time-shifted counterparts
        abundance_constraint = z3.ForAll(
            [source_world],
            z3.Implies(
                # If the source_world is a valid world
                self.is_world(source_world),
                # Then both:
                z3.And(
                    # Forwards condition
                    z3.Implies(
                        # If source can shift forward
                        self.can_shift_forward(source_world),
                        # Then some forward-shifted world exists
                        z3.Exists(
                            [forward_world],
                            z3.And(
                                self.is_world(forward_world),
                                self.is_shifted_by(source_world, 1, forward_world)
                            )
                        )
                    ),
                    # Backwards condition
                    z3.Implies(
                        # If source can shift backwards
                        self.can_shift_backward(source_world),
                        # Then some backwards-shifted world exists
                        z3.Exists(
                            [backwards_world],
                            z3.And(
                                self.is_world(backwards_world),
                                self.is_shifted_by(source_world, -1, backwards_world)
                            )
                        )
                    )
                )
            )
        )
        return abundance_constraint

    def skolem_abundance_constraint(self):
        """Build constraint ensuring necessary time-shifted worlds exist using Skolemization.

        DEPRECATED: Replaced by capped_skolem_abundance_constraint which provides
        full shift coverage (not just +/-1) and is necessary for the perpetuity
        principles (BM_TH_1/BM_TH_2) to hold. This method is retained for reference
        and fallback comparison.

        The abundance property ensures that for any world that can be shifted forward
        or backward in time (while staying within valid time bounds), there exists a
        corresponding world that represents that time shift.

        This implementation uses Skolem functions to eliminate nested quantifiers,
        which can improve Z3 performance.
        """
        # Define Skolem functions that directly compute the necessary worlds
        forward_of = z3.Function('forward_of', self.WorldIdSort, self.WorldIdSort)
        backward_of = z3.Function('backward_of', self.WorldIdSort, self.WorldIdSort)
        
        # Variable for world being constrained
        source_world = z3.Int('abundance_source_id')
        
        # Use Skolem functions instead of existential quantifiers
        return z3.ForAll(
            [source_world],
            z3.Implies(
                # If the source_world is a valid world
                self.is_world(source_world),
                # Then both:
                z3.And(
                    # Forwards condition - if source can shift forward
                    z3.Implies(
                        self.can_shift_forward(source_world),
                        z3.And(
                            # The forward_of function must produce a valid world
                            self.is_world(forward_of(source_world)),
                            # The produced world must be properly shifted
                            self.is_shifted_by(source_world, 1, forward_of(source_world))
                        )
                    ),
                    # Backwards condition - if source can shift backwards
                    z3.Implies(
                        self.can_shift_backward(source_world),
                        z3.And(
                            # The backward_of function must produce a valid world
                            self.is_world(backward_of(source_world)),
                            # The produced world must be properly shifted
                            self.is_shifted_by(source_world, -1, backward_of(source_world))
                        )
                    )
                )
            )
        )

    def full_abundance_constraint(self):
        """Build abundance constraint covering ALL valid integer shifts.

        Replaces the +/-1 Skolem abundance with a constraint requiring that for
        every valid world and every valid shift amount (within the valid duration
        range), there exists a corresponding time-shifted world.

        The valid shift range is {-(2*(M-1)), ..., 2*(M-1)} to cover all possible
        time translations between worlds in the finite domain. However, a shift is
        only required to produce a world if the shifted interval would be valid
        (i.e., both start and end of the shifted interval fall within the global
        time range (-M, M)).

        This implementation uses existential quantifiers over target worlds
        (nested ForAll/Exists pattern).

        Paper alignment: Corresponds to app:auto_existence (JPL paper, lines 2154-2178)
        which provides time-shifted copies for any pair of times x, y in D.
        """
        source_world = z3.Int('abund_src')
        target_world = z3.Int('abund_tgt')
        shift_amount = z3.Int('abund_shift')

        return z3.ForAll(
            [source_world, shift_amount],
            z3.Implies(
                z3.And(
                    # Source must be a valid world
                    self.is_world(source_world),
                    # Shift must be within the valid duration range
                    self.is_valid_duration(shift_amount),
                    # The shifted start must remain in the global time range
                    self.is_valid_time(
                        self.world_interval_start(source_world) + shift_amount
                    ),
                    # The shifted end must remain in the global time range
                    self.is_valid_time(
                        self.world_interval_end(source_world) + shift_amount
                    ),
                ),
                # Then a properly shifted target world must exist
                z3.Exists(
                    [target_world],
                    z3.And(
                        self.is_world(target_world),
                        # Target interval is source interval shifted by shift_amount
                        self.world_interval_start(target_world) == (
                            self.world_interval_start(source_world) + shift_amount
                        ),
                        self.world_interval_end(target_world) == (
                            self.world_interval_end(source_world) + shift_amount
                        ),
                        # Target states match source states when shifted
                        self.matching_states_when_shifted_var(
                            source_world, shift_amount, target_world
                        ),
                    )
                )
            )
        )

    def matching_states_when_shifted_var(self, source_world, shift, target_world):
        """Check if states match when shifted between world arrays (variable shift amount).

        Like matching_states_when_shifted but accepts a Z3 expression for the shift
        amount rather than a Python integer, enabling use in universally-quantified
        abundance constraints.

        Args:
            source_world: Source world identifier (Z3 Int)
            shift: Shift amount (Z3 Int expression, may be a quantified variable)
            target_world: Target world identifier (Z3 Int)

        Returns:
            Z3 formula that is true if states match when shifted
        """
        time = z3.Int('shift_var_check_time')
        source_array = self.world_function(source_world)
        target_array = self.world_function(target_world)

        return z3.ForAll(
            [time],
            z3.Implies(
                z3.And(
                    # Time is within source interval
                    time >= self.world_interval_start(source_world),
                    time <= self.world_interval_end(source_world),
                    # Shifted time is within target interval
                    time + shift >= self.world_interval_start(target_world),
                    time + shift <= self.world_interval_end(target_world),
                ),
                # States must match when shifted
                z3.Select(source_array, time) == z3.Select(target_array, time + shift)
            )
        )

    def skolem_full_abundance_constraint(self):
        """Build full abundance constraint using a Skolem function for target worlds.

        Uses a Skolem function `shift_of(world, delta)` that maps a source world
        and shift amount to the target world, avoiding the nested ForAll/Exists
        pattern which can be expensive for Z3 to reason about.

        The shift_of function is required to produce:
        1. A valid world
        2. With the correctly shifted interval
        3. With matching states when shifted

        This is the primary abundance strategy for performance-critical use.

        Paper alignment: Skolemizes app:auto_existence -- the existence is
        witnessed by an explicit function rather than a bare existential.
        """
        # Define Skolem function: (world_id, shift_amount) -> target_world_id
        shift_of = z3.Function(
            'shift_of', self.WorldIdSort, self.TimeSort, self.WorldIdSort
        )

        source_world = z3.Int('skfull_src')
        shift_amount = z3.Int('skfull_shift')

        return z3.ForAll(
            [source_world, shift_amount],
            z3.Implies(
                z3.And(
                    # Source must be a valid world
                    self.is_world(source_world),
                    # Shift must be within the valid duration range
                    self.is_valid_duration(shift_amount),
                    # The shifted start must remain in the global time range
                    self.is_valid_time(
                        self.world_interval_start(source_world) + shift_amount
                    ),
                    # The shifted end must remain in the global time range
                    self.is_valid_time(
                        self.world_interval_end(source_world) + shift_amount
                    ),
                ),
                z3.And(
                    # The Skolem function produces a valid world
                    self.is_world(shift_of(source_world, shift_amount)),
                    # Target interval is source interval shifted by shift_amount
                    self.world_interval_start(shift_of(source_world, shift_amount)) == (
                        self.world_interval_start(source_world) + shift_amount
                    ),
                    self.world_interval_end(shift_of(source_world, shift_amount)) == (
                        self.world_interval_end(source_world) + shift_amount
                    ),
                    # Target states match source states when shifted
                    self.matching_states_when_shifted_var(
                        source_world, shift_amount, shift_of(source_world, shift_amount)
                    ),
                )
            )
        )

    def build_grounded_abundance_constraints(self, max_shift=None):
        """Build abundance constraints with shift range limited to max_shift.

        Task 114 Fix: Enumerates (source_world_id, interval, shift) triples but
        limits shift magnitudes to max_shift (defaults to temporal_depth). This
        ensures constraint count scales with formula depth, not M.

        Args:
            max_shift: Maximum absolute shift magnitude. Defaults to M-1 (full closure).

        Returns:
            list: Ground Implies constraints, one per (source_id, interval, shift) triple
        """
        if max_shift is None:
            max_shift = self.M - 1
        constraints = []
        intervals = self.generate_time_intervals(self.M)
        bound = 3 * self.M

        for src_id in range(bound):
            src_val = z3.IntVal(src_id)
            src_is_world = self.is_world(src_val)

            for (start, end) in intervals:
                src_has_interval = z3.And(
                    self.world_interval_start(src_val) == z3.IntVal(start),
                    self.world_interval_end(src_val) == z3.IntVal(end),
                )
                antecedent = z3.And(src_is_world, src_has_interval)

                for delta in range(-max_shift, max_shift + 1):
                    if delta == 0:
                        continue
                    new_start = start + delta
                    new_end = end + delta
                    if not (-self.M + 1 <= new_start and new_end <= self.M - 1):
                        continue

                    # Build target options as a disjunction over bounded world IDs
                    target_options = []
                    for tgt_id in range(bound):
                        tgt_val = z3.IntVal(tgt_id)
                        state_eqs = [
                            z3.Select(self.world_function(src_val), z3.IntVal(t)) ==
                            z3.Select(self.world_function(tgt_val), z3.IntVal(t + delta))
                            for t in range(start, end + 1)
                        ]
                        target_options.append(z3.And(
                            self.is_world(tgt_val),
                            self.world_interval_start(tgt_val) == z3.IntVal(new_start),
                            self.world_interval_end(tgt_val) == z3.IntVal(new_end),
                            *state_eqs
                        ))

                    # Assert: if src has this interval, some bounded target is the shift
                    constraints.append(z3.Implies(antecedent, z3.Or(*target_options)))

        return constraints

    def capped_skolem_abundance_constraint(self):
        """Build abundance constraint with Skolem functions and shift caps.

        Like skolem_full_abundance_constraint but limits the shift amount based
        on the actual interval lengths of worlds, capping shifts to those that
        keep the shifted interval within the global time range. This reduces
        unnecessary constraint complexity for worlds near the time boundaries.

        The shift cap ensures: for a world with interval [s, e], only shifts delta
        where s+delta >= -M+1 and e+delta <= M-1 are required (i.e., the shifted
        world's interval stays within the valid time range).

        This is equivalent to: -M+1 - s <= delta <= M-1 - e, or equivalently:
        delta >= -M+1 - s  AND  delta <= M-1 - e
        combined with the is_valid_duration check.

        Task 98 Note: build_grounded_abundance_constraints() was tested as an alternative
        but found counterproductive -- the per-interval grounded form creates MORE ground
        terms via eager E-matching (one Skolem term per world per valid shift immediately),
        while the quantified MBQI form is lazy (only instantiated when needed by the
        solver). For both SAT (BM_CM_1: 9s -> 15s timeout) and UNSAT (BM_TH_1/2: 30s ->
        75s+) the quantified form is faster. OOM is handled by max_memory=4096 (Task 97).

        Uses Skolem functions to eliminate existential quantifiers.
        """
        # Define Skolem function: (world_id, shift_amount) -> target_world_id
        shift_of_capped = z3.Function(
            'shift_of_capped', self.WorldIdSort, self.TimeSort, self.WorldIdSort
        )

        source_world = z3.Int('skcap_src')
        shift_amount = z3.Int('skcap_shift')

        # Compute boundary-constrained shift conditions inline
        source_start = self.world_interval_start(source_world)
        source_end = self.world_interval_end(source_world)

        return z3.ForAll(
            [source_world, shift_amount],
            z3.Implies(
                z3.And(
                    # Source must be a valid world
                    self.is_world(source_world),
                    # Shift keeps the start within valid global range
                    source_start + shift_amount >= z3.IntVal(-self.M + 1),
                    # Shift keeps the end within valid global range
                    source_end + shift_amount <= z3.IntVal(self.M - 1),
                    # Shift is non-zero (identity already satisfied by source_world itself)
                    shift_amount != z3.IntVal(0),
                ),
                z3.And(
                    # The Skolem function produces a valid world
                    self.is_world(shift_of_capped(source_world, shift_amount)),
                    # Target interval is source interval shifted by shift_amount
                    self.world_interval_start(
                        shift_of_capped(source_world, shift_amount)
                    ) == source_start + shift_amount,
                    self.world_interval_end(
                        shift_of_capped(source_world, shift_amount)
                    ) == source_end + shift_amount,
                    # Target states match source states when shifted
                    self.matching_states_when_shifted_var(
                        source_world,
                        shift_amount,
                        shift_of_capped(source_world, shift_amount)
                    ),
                )
            )
        )

    def depth_bounded_skolem_abundance_constraint(self, max_shift):
        """Build Skolem abundance constraint with shift magnitude bounded by max_shift.

        Like capped_skolem_abundance_constraint but adds explicit bounds on the shift
        amount: -max_shift <= shift_amount <= max_shift. This reduces MBQI instantiation
        scope from O(M) to O(temporal_depth), preventing the blowup at M>=3.
        """
        shift_of_bounded = z3.Function(
            'shift_of_bounded', self.WorldIdSort, self.TimeSort, self.WorldIdSort
        )

        source_world = z3.Int('skbnd_src')
        shift_amount = z3.Int('skbnd_shift')

        source_start = self.world_interval_start(source_world)
        source_end = self.world_interval_end(source_world)

        return z3.ForAll(
            [source_world, shift_amount],
            z3.Implies(
                z3.And(
                    self.is_world(source_world),
                    source_start + shift_amount >= z3.IntVal(-self.M + 1),
                    source_end + shift_amount <= z3.IntVal(self.M - 1),
                    shift_amount != z3.IntVal(0),
                    shift_amount >= z3.IntVal(-max_shift),
                    shift_amount <= z3.IntVal(max_shift),
                ),
                z3.And(
                    self.is_world(shift_of_bounded(source_world, shift_amount)),
                    self.world_interval_start(
                        shift_of_bounded(source_world, shift_amount)
                    ) == source_start + shift_amount,
                    self.world_interval_end(
                        shift_of_bounded(source_world, shift_amount)
                    ) == source_end + shift_amount,
                    self.matching_states_when_shifted_var(
                        source_world,
                        shift_amount,
                        shift_of_bounded(source_world, shift_amount)
                    ),
                )
            )
        )

    def build_task_minimization_constraint(self):
        """Build constraint encouraging minimal changes between consecutive world states.

        This constraint guides Z3 to prefer solutions where consecutive world states
        are identical when possible, reducing unnecessary state changes and potentially
        reducing the search space.
        
        Returns:
            Z3 formula: Constraint encouraging minimal state changes
        """
        world_id = z3.Int('minimal_world')
        time_point = z3.Int('minimal_time')
        
        return z3.ForAll(
            [world_id, time_point],
            z3.Implies(
                z3.And(
                    self.is_world(world_id),
                    self.is_valid_time_for_world(world_id, time_point),
                    self.is_valid_time_for_world(world_id, time_point + 1)
                ),
                # Encourage identical states if possible (soft constraint)
                z3.Select(self.world_function(world_id), time_point) == 
                z3.Select(self.world_function(world_id), time_point + 1)
            )
        )
    
    def define_invalidity(self):
        """Define the behavior for premises and conclusions in invalidity checks.

        This method sets up two lambda functions that specify how premises and conclusions 
        should be evaluated when checking for invalidity:

        - premise_behavior: Evaluates whether a premise is true at the main world and time
        - conclusion_behavior: Evaluates whether a conclusion is false at the main world and time

        These behaviors are used to find counterexamples that demonstrate invalidity of arguments
        by showing a case where all premises are true but the conclusion is false.
        """
        # Create main_point dictionary with world and time
        main_point = {"world": self.main_world, "time": self.main_time}
        premise_behavior = lambda premise: self.true_at(premise, main_point)
        conclusion_behavior = lambda conclusion: self.false_at(conclusion, main_point)
        return premise_behavior, conclusion_behavior
        
    def verify_model(self, z3_model, premises, conclusions):
        """Verify that premises are true and conclusions are false in the found model.
        
        This method checks whether the model generated by Z3 correctly satisfies the 
        constraints for invalidating an argument - i.e., that all premises are true and
        all conclusions are false at the main evaluation point.
        
        Args:
            z3_model: The Z3 model to verify
            premises: List of premise formulas
            conclusions: List of conclusion formulas
            
        Returns:
            dict: Verification results dictionary with information about whether
                  premises are true and conclusions are false in the model
        """
        verification_results = {
            "premises_verified": True,
            "conclusions_verified": True,
            "errors": []
        }
        
        # Check that all premises are true at the main point
        for premise in premises:
            try:
                main_point = {"world": self.main_world, "time": self.main_time}
                premise_expr = self.true_at(premise, main_point)
                result = z3_model.eval(premise_expr)
                if not is_true(result):
                    verification_results["premises_verified"] = False
                    verification_results["errors"].append(f"Premise {premise} is not true at main evaluation point")
            except z3.Z3Exception as e:
                verification_results["errors"].append(f"Error evaluating premise {premise}: {e}")
        
        # Check that all conclusions are false at the main point
        for conclusion in conclusions:
            try:
                main_point = {"world": self.main_world, "time": self.main_time}
                conclusion_expr = self.false_at(conclusion, main_point)
                result = z3_model.eval(conclusion_expr)
                if not is_true(result):
                    verification_results["conclusions_verified"] = False
                    verification_results["errors"].append(f"Conclusion {conclusion} is not false at main evaluation point")
            except z3.Z3Exception as e:
                verification_results["errors"].append(f"Error evaluating conclusion {conclusion}: {e}")
        
        return verification_results

    def true_at(self, sentence, eval_point):
        """Returns a Z3 formula that is satisfied when the sentence is true at the given evaluation point.

        ProofChecker Alignment: Atoms are FALSE outside the world's domain. This matches
        the ProofChecker theorem `atom_false_of_not_domain` which ensures atoms evaluate
        to false at times not in the world history's domain.

        Args:
            sentence: The sentence to evaluate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID (integer) at which to evaluate the sentence
                - "time": The time point at which to evaluate the sentence

        Returns:
            Z3 formula that is satisfied when sentence is true at eval_point
        """
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        # Get the world array from the world ID
        world_array = self.world_function(eval_world)

        sentence_letter = sentence.sentence_letter  # store sentence letter

        # base case
        if sentence_letter is not None:
            # ProofChecker alignment: Atoms are FALSE outside the world's domain
            # (atom_false_of_not_domain theorem in Truth.lean)
            in_domain = self.is_valid_time_for_world(eval_world, eval_time)
            eval_world_state = z3.Select(world_array, eval_time)
            return z3.And(
                in_domain,
                self.truth_condition(eval_world_state, sentence_letter)
            )

        # recursive case
        operator = sentence.operator  # store operator
        arguments = sentence.arguments or () # store arguments
        return operator.true_at(*arguments, eval_point) # apply semantics

    def false_at(self, sentence, eval_point):
        """Returns a Z3 formula that is satisfied when the sentence is false at the given evaluation point.

        Args:
            sentence: The sentence to evaluate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID at which to evaluate the sentence
                - "time": The time point at which to evaluate the sentence
            
        Returns:
            Z3 formula that is satisfied when sentence is false at eval_point
        """
        return z3.Not(self.true_at(sentence, eval_point))
    
    def inject_z3_model_values(self, z3_model, original_semantics, model_constraints):
        """Inject concrete Z3 values from iteration into model constraints.
        
        This method extracts values from a Z3 model and adds them as constraints
        for the next iteration. It handles Bimodal-specific concepts: world IDs,
        truth conditions, and temporal task relations.
        
        Args:
            z3_model: Z3 model containing concrete values from solver
            original_semantics: Original semantics instance that created the Z3 functions
            model_constraints: ModelConstraints instance to update with injected values
        """
        # Get number of states from model_constraints settings
        num_states = 2 ** model_constraints.settings['N']
        
        # Inject world constraints (bimodal uses world IDs)
        # We need to check valid world IDs instead of states
        max_world_ids = 10  # Reasonable limit for iteration
        for world_id in range(max_world_ids):
            # Evaluate using original is_world function
            is_world_val = z3_model.eval(original_semantics.is_world(world_id), model_completion=True)
            # Add constraint using new is_world function
            if is_true(is_world_val):
                model_constraints.all_constraints.append(self.is_world(world_id))
            else:
                model_constraints.all_constraints.append(z3.Not(self.is_world(world_id)))
        
        # Inject truth_condition constraints for each state and sentence letter
        for sentence_obj in model_constraints.syntax.sentence_letters:
            atom = sentence_obj.sentence_letter
            
            for state in range(num_states):
                # Evaluate using original truth_condition function
                truth_val = z3_model.eval(original_semantics.truth_condition(state, atom), model_completion=True)
                # Add constraint using new truth_condition function
                if is_true(truth_val):
                    model_constraints.all_constraints.append(self.truth_condition(state, atom))
                else:
                    model_constraints.all_constraints.append(z3.Not(self.truth_condition(state, atom)))
        
        # Inject task_rel constraints (transitions between world states with duration)
        # Duration range based on time domain: for M time points, durations range from -(M-1) to (M-1)
        M = model_constraints.settings.get('M', self.M)
        duration_range = range(-M + 1, M)

        for state1 in range(num_states):
            for duration in duration_range:
                for state2 in range(num_states):
                    # Evaluate using original task_rel function with duration
                    task_val = z3_model.eval(
                        original_semantics.task_rel(state1, duration, state2),
                        model_completion=True
                    )
                    # Add constraint using new task_rel function
                    if is_true(task_val):
                        model_constraints.all_constraints.append(
                            self.task_rel(state1, duration, state2)
                        )
                    else:
                        model_constraints.all_constraints.append(
                            z3.Not(self.task_rel(state1, duration, state2))
                        )
        
        # Note: World arrays, intervals, and other temporal structures are
        # handled by the theory's own construction process

    def generate_time_intervals(self, M):
        """Generate all valid time intervals of length M that include time 0.
        
        Args:
            M (int): The length of each interval
            
        Returns:
            list: List of (start_time, end_time) tuples representing intervals
        """
        intervals = []
        for start in range(-M+1, 1):  # Start points from M+1 to 0
            end = start + M - 1       # Each interval has exactly M time points
            intervals.append((start, end))
        return intervals
        
    def is_time_shifted(self, source_world_id, shift_amount, target_world_id):
        """Determines if target_world_id is a time-shifted version of source_world_id by shift_amount.
        
        Args:
            source_world_id: The ID of the source world
            shift_amount: The amount to shift by
            target_world_id: The ID of the target world
            
        Returns:
            Z3 formula that is true if target is a time-shifted version of source
        """
        return self.is_shifted_by(source_world_id, shift_amount, target_world_id)

    def extract_model_elements(self, z3_model):
        """Extract all model elements from a found model with improved organization.
        
        This method extracts world IDs, their arrays, time intervals, and time-shift relations
        from a satisfiable Z3 model.
        
        Args:
            z3_model: The Z3 model to extract elements from
            
        Returns:
            Tuple containing:
            1. Dictionary mapping world_ids to their time-state mappings
               {world_id (int): {time: bitvector_state}}
            2. Dictionary containing main world mapping {time: bitvector_state}
            3. Dictionary mapping world_ids to their world arrays
               {world_id (int): world_array}
            4. Dictionary mapping world_ids to their time-shift relations
               {source_id: {shift: target_id}}
        """
        # First identify all valid world IDs
        all_worlds = self._extract_valid_world_ids(z3_model)
        
        # Extract world arrays for each valid world ID
        world_arrays = self._extract_world_arrays(z3_model, all_worlds)
        
        # Extract time intervals for each world
        world_time_intervals = self._extract_time_intervals(z3_model, all_worlds)
        
        # Extract time-state mappings for each world ID
        world_histories = self._extract_world_histories(z3_model, all_worlds, world_arrays, world_time_intervals)
        
        # Check if we have any valid world histories
        if not world_histories:
            # Create empty dictionaries for a consistent interface
            world_histories = {}
            world_arrays = {}
            time_shift_relations = {}
            # Return empty structures
            return world_histories, {}, world_arrays, {}
        
        # Extract time shift relations between worlds
        time_shift_relations = self._extract_time_shift_relations(z3_model, all_worlds, world_histories)
        
        # Identify main world history
        main_world_history = world_histories.get(self.main_world, {})
        
        return world_histories, main_world_history, world_arrays, time_shift_relations
        
    def _extract_valid_world_ids(self, z3_model):
        """Identifies all valid world IDs in the model.
        
        Args:
            z3_model: The Z3 model to extract from
            
        Returns:
            list: List of valid world IDs
        """
        all_worlds = []
        # Check each potential world_id to see if it corresponds to a valid world history
        for i in range(self.max_world_id):
            try:
                # Get is_world expression
                is_world_expr = self.is_world(i)
                
                # Check if this world_id maps to a valid world history
                is_valid_expr = z3_model.eval(is_world_expr)
                is_valid = is_true(is_valid_expr)
                
                if is_valid:
                    all_worlds.append(i)
            except z3.Z3Exception:
                continue
        
        # Ensure main world (ID 0) is included
        if 0 not in all_worlds:
            all_worlds.append(0)
            
        return all_worlds
    
    def _extract_world_arrays(self, z3_model, all_worlds):
        """Gets arrays for each world ID.
        
        Extracts the array representation for each valid world in the model,
        handling both ArrayRef and QuantifierRef (Lambda) representations.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            
        Returns:
            dict: Mapping from world_id to world array
        """
        world_arrays = {}
        
        for world_id in all_worlds:
            try:
                # Extract this valid world history array
                world_array_expr = self.world_function(world_id)
                
                # Evaluate the expression in the model
                world_array = z3_model.eval(world_array_expr)
                
                # Store the array regardless of its representation type
                world_arrays[world_id] = world_array

            # TODO: add print to test
            except z3.Z3Exception:
                # Skip worlds that can't be extracted
                pass
                
        return world_arrays
    
    def _extract_time_intervals(self, z3_model, all_worlds):
        """Extracts valid time intervals for each world.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            
        Returns:
            dict: Mapping from world_id to (start_time, end_time) tuple
        """
        # Reset time intervals dictionary
        self.world_time_intervals = {}
        
        for world_id in all_worlds:
            try:
                start_time = z3_model.eval(self.world_interval_start(world_id)).as_long()
                end_time = z3_model.eval(self.world_interval_end(world_id)).as_long()
                self.world_time_intervals[world_id] = (start_time, end_time)
            except z3.Z3Exception:
                # Use default interval if extraction fails
                start_time = -self.M + 1
                end_time = self.M - 1
                self.world_time_intervals[world_id] = (start_time, end_time)
        
        return self.world_time_intervals
    
    # TODO: refactor to make fail-fast
    def safe_select(self, z3_model, world_array, time):
        """Safely select from a world array, handling both ArrayRef and QuantifierRef.
        
        This function allows array access regardless of Z3's internal representation choice
        between concrete arrays (ArrayRef) and Lambda functions (QuantifierRef).
        
        Args:
            z3_model: The Z3 model
            world_array: Either an ArrayRef or QuantifierRef (Lambda)
            time: The time point to select (int or Z3 ArithRef)
            
        Returns:
            The value at the specified time point
            
        Raises:
            TypeError: If world_array is not a valid array type or time is not a valid Z3 integer
            z3.Z3Exception: If evaluation fails
        """
        # Handle time parameter to ensure it's a Z3 integer
        if isinstance(time, int):
            # Simple Python int
            time_val = z3.IntVal(time)
        elif isinstance(time, z3.ArithRef) and time.sort() == z3.IntSort():
            # Already a Z3 Int, use directly
            time_val = time
        elif hasattr(time, 'as_long'):
            # Z3 value with numerical representation, convert to Z3 Int
            # TODO: linter error
            time_val = z3.IntVal(time.as_long())  # type: ignore
        else:
            # Cannot use this time value
            raise TypeError(f"Time parameter must be an integer or Z3 Int, got {type(time)}: {time}")
            
        # Handle different array types
        if isinstance(world_array, z3.ArrayRef):
            # Standard array select
            select_expr = z3.Select(world_array, time_val)
            return z3_model.eval(select_expr)
        elif isinstance(world_array, z3.QuantifierRef):
            # Handle Lambda expression
            if world_array.num_vars() != 1:
                raise TypeError(f"Expected Lambda with 1 variable, got {world_array.num_vars()}")
                
            # Create proper Z3 substitution
            select_expr = z3.substitute(world_array.body(), 
                                      (z3.Var(0, self.TimeSort), time_val))
            return z3_model.eval(select_expr)
        else:
            raise TypeError(f"Cannot select from world array of type {type(world_array)}")

    def _extract_world_histories(self, z3_model, worlds, world_arrays, world_time_intervals):
        """Creates histories (time-state mappings) for each world.
        
        Extracts the state of each world at each time point within its valid interval
        using the safe_select function to handle different array representations.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            world_arrays: Dictionary of world arrays
            world_time_intervals: Dictionary of time intervals
            
        Returns:
            dict: Mapping from world_id to time-state mapping
        """
        world_histories = {}
        
        for world_id in worlds:
            # Skip worlds with missing data
            if world_id not in world_arrays or world_id not in world_time_intervals:
                continue
                
            # Get the world array and time interval
            world_array = world_arrays[world_id]
            start_time, end_time = world_time_intervals[world_id]
            
            # Extract states for each time point
            time_states = {}
            
            for time in range(start_time, end_time + 1):
                try:
                    # Create Z3 IntVal for time to ensure proper typing
                    time_val = z3.IntVal(time)
                    state = self.safe_select(z3_model, world_array, time_val)
                    
                    # Convert to state representation using the new alphabetic labeling
                    if hasattr(state, 'sort') and str(state.sort()).startswith('BitVec'):
                        # Use bitvec_to_worldstate instead of bitvec_to_substates
                        state_val = bitvec_to_worldstate(state)
                        time_states[time] = state_val
                    else:
                        # Non-BitVec result
                        time_states[time] = f"<{state}>"
                except (TypeError, z3.Z3Exception) as e:
                    # Try direct Z3 evaluation as a last resort
                    try:
                        if isinstance(world_array, z3.ArrayRef):
                            time_val = z3.IntVal(time)
                            select_expr = z3.Select(world_array, time_val)
                            state = z3_model.eval(select_expr)
                            # Use bitvec_to_worldstate instead of bitvec_to_substates
                            state_val = bitvec_to_worldstate(state)
                            time_states[time] = state_val
                        else:
                            # No recovery possible
                            time_states[time] = f"<error:{str(e)}>"
                    except Exception:
                        # Final fallback - store error
                        time_states[time] = f"<error:{str(e)}>"
            
            # Add history to output
            world_histories[world_id] = time_states
        
        return world_histories
    
    def _extract_time_shift_relations(self, z3_model, worlds, world_histories):
        """Builds shift relations between worlds.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            world_histories: Dictionary of time-state mappings
            
        Returns:
            dict: Nested dictionary mapping source_id to {shift: target_id}
        """
        time_shift_relations = {}
        
        for source_id in worlds:
            time_shift_relations[source_id] = {}
            
            # Add self-shift (shift by 0)
            time_shift_relations[source_id][0] = source_id
            
            # Skip if world isn't in histories
            if source_id not in world_histories:
                continue
                
            # Check essential shifts (+1, -1)
            for shift in [1, -1]:
                for target_id in worlds:
                    if source_id != target_id and target_id in world_histories:  # Skip self and invalid targets
                        try:
                            # First check interval compatibility
                            source_start, source_end = self.world_time_intervals[source_id]
                            target_start, target_end = self.world_time_intervals[target_id]
                            
                            # For positive shift, target interval should be shifted up by 1
                            if shift == 1 and target_start == source_start + 1 and target_end == source_end + 1:
                                # Check if states match when shifted
                                is_shifted = True
                                for time in range(source_start, source_end + 1):
                                    if time + shift <= target_end:
                                        source_state = world_histories[source_id].get(time)
                                        target_state = world_histories[target_id].get(time + shift)
                                        if source_state is not None and target_state is not None and source_state != target_state:
                                            is_shifted = False
                                            break
                                
                                if is_shifted:
                                    time_shift_relations[source_id][shift] = target_id
                                    break
                            
                            # For negative shift, target interval should be shifted down by 1
                            elif shift == -1 and target_start == source_start - 1 and target_end == source_end - 1:
                                # Check if states match when shifted
                                is_shifted = True
                                for time in range(source_start, source_end + 1):
                                    if time + shift >= target_start:
                                        source_state = world_histories[source_id].get(time)
                                        target_state = world_histories[target_id].get(time + shift)
                                        if source_state is not None and target_state is not None and source_state != target_state:
                                            is_shifted = False
                                            break
                                
                                if is_shifted:
                                    time_shift_relations[source_id][shift] = target_id
                                    break
                        except Exception as e:
                            pass
        
        if not world_histories:
            pass
            
        return time_shift_relations

