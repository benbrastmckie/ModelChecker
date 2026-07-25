"""
Core semantics implementation for the logos theory.

This module contains LogosSemantics, the shared semantic framework for all logos
subtheories, providing the foundation for hyperintensional truthmaker semantics
with support for modular operator loading and subtheory coordination.
"""

from typing import Any, List, Optional, Set, TYPE_CHECKING, cast

from model_checker import z3_shim as z3

from model_checker.solver import is_true
from model_checker.syntactic.atoms import get_atom_sort
from model_checker.models.semantic import SemanticDefaults
from model_checker.utils import ForAll, Exists

# Import protocols for type checking
if TYPE_CHECKING:
    from ..protocols import (
        RegistryProtocol,
        EvaluationPoint,
        StateType,
        Z3Constraint,
        SettingsDict,
    )
    from model_checker.syntactic import Sentence
    from model_checker.models.model_constraints import ModelConstraints


class LogosSemantics(SemanticDefaults):
    """
    Shared semantic framework for all logos subtheories.

    This class provides the foundation for hyperintensional truthmaker semantics
    with support for modular operator loading and subtheory coordination.
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'M': None,  # Time steps for temporal models (used by constitutive subtheory)
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10,
        'iterate': False,
        'expectation': None,
        'solver': 'z3',  # Solver backend: 'z3' or 'cvc5'
    }

    def __init__(self, combined_settings: Optional['SettingsDict'] = None,
                 operator_registry: Optional['RegistryProtocol'] = None, **kwargs: Any) -> None:
        # Ensure we have default settings
        if combined_settings is None:
            combined_settings = self.DEFAULT_EXAMPLE_SETTINGS.copy()
            combined_settings.update(kwargs)

        super().__init__(combined_settings)
        self.operator_registry = operator_registry

        # Define the Z3 primitives
        self.verify = z3.Function(
            "verify",                   # Names the function 'verify'
            z3.BitVecSort(self.N),      # which maps a bitvector
            get_atom_sort(),            # and a sentence letter
            z3.BoolSort()               # to a truth-value
        )
        self.falsify = z3.Function(
            "falsify",                  # Names the function 'falsify'
            z3.BitVecSort(self.N),      # which maps a bitvector
            get_atom_sort(),            # and a sentence letter
            z3.BoolSort()               # to a truth-value
        )
        self.possible = z3.Function(
            "possible",                 # Names the function 'possible'
            z3.BitVecSort(self.N),      # which maps a bitvector
            z3.BoolSort()               # to a truth-value
        )

        # Define point of evaluation for the premises and conclusions
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world": self.main_world
        }

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        possibility_downward_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )

        # Set frame constraints
        self.frame_constraints = [
            possibility_downward_closure,
            self.is_world(self.main_world),
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

    def load_subtheories(self, subtheories: Optional[List[str]] = None) -> List[Any]:
        """Load specified subtheories."""
        if subtheories is None:
            subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual']
        if self.operator_registry:
            return self.operator_registry.load_subtheories(subtheories)
        return []

    def compatible(self, state_x: 'StateType', state_y: 'StateType') -> 'Z3Constraint':
        """Determines if the fusion of two states is possible."""
        return self.possible(self.fusion(state_x, state_y))

    def maximal(self, state_w: 'StateType') -> 'Z3Constraint':
        """Determines if a state is maximal with respect to compatibility."""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, state_w),
                self.is_part_of(x, state_w),
            ),
        )

    def is_world(self, state_w: 'StateType') -> 'Z3Constraint':
        """Determines if a state represents a possible world in the model."""
        return cast(z3.BoolRef, z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        ))

    def true_at(self, sentence: 'Sentence', eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a sentence is true at a given evaluation point.

        For atomic sentences (sentence_letters), it checks if there exists some state x
        that is part of the evaluation world such that x verifies the sentence letter.

        For complex sentences, it delegates to the operator's true_at method with the
        sentence's arguments and evaluation point.

        Args:
            sentence (Sentence): The sentence to evaluate
            eval_point (dict): The evaluation point containing a "world" key

        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is true at eval_point

        Raises:
            TypeError: If the sentence has neither a sentence letter nor an operator
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]

        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, cast(z3.BoolRef, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter))))

        operator = sentence.operator
        if operator is None:
            raise TypeError(
                f"Cannot evaluate truth of '{sentence.name}': "
                f"sentence has no operator or sentence letter."
            )
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_point)

    def false_at(self, sentence: 'Sentence', eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a sentence is false at a given evaluation point.

        For atomic sentences (sentence_letters), it checks if there exists some state x
        that is part of the evaluation world such that x falsifies the sentence letter.

        For complex sentences, it delegates to the operator's false_at method with the
        sentence's arguments and evaluation point.

        Args:
            sentence (Sentence): The sentence to evaluate
            eval_point (dict): The evaluation point containing a "world" key

        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is false at eval_point

        Raises:
            TypeError: If the sentence has neither a sentence letter nor an operator
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]

        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, cast(z3.BoolRef, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter))))

        operator = sentence.operator
        if operator is None:
            raise TypeError(
                f"Cannot evaluate falsity of '{sentence.name}': "
                f"sentence has no operator or sentence letter."
            )
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_point)

    def extended_verify(self, state: 'StateType', sentence: 'Sentence',
                       eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a state verifies a sentence at an evaluation point.

        This method extends the hyperintensional verification relation to all
        sentences of the language in order to determine whether a specific state
        is a verifier for a given sentence at a particular evaluation point.

        For atomic sentences (those with a sentence_letter), it directly uses the verify
        relation to determine if the state verifies the atomic sentence.

        For complex sentences (those with an operator), it delegates to the operator's
        extended_verify method which handles the verification conditions specific to
        that operator.

        Args:
            state (BitVecRef): The state being tested as a verifier
            sentence (Sentence): The sentence to check
            eval_point (dict): The evaluation point context

        Returns:
            BoolRef: Z3 constraint expressing the verification condition

        Raises:
            TypeError: If the sentence has neither a sentence letter nor an operator
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        if operator is None:
            raise TypeError(
                f"Cannot verify '{sentence.name}': "
                f"sentence has no operator or sentence letter."
            )
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_point)

    def extended_falsify(self, state: 'StateType', sentence: 'Sentence',
                        eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a state falsifies a sentence at an evaluation point.

        This method extends the hyperintensional falsification relation to all
        sentences of the language in order to determine whether a specific state
        is a falsifier for a given sentence at a particular evaluation point.

        For atomic sentences (those with a sentence_letter), it directly uses the falsify
        relation to determine if the state falsifies the atomic sentence.

        For complex sentences (those with an operator), it delegates to the operator's
        extended_falsify method which handles the falsification conditions specific to
        that operator.

        Args:
            state (BitVecRef): The state being tested as a falsifier
            sentence (Sentence): The sentence to check
            eval_point (dict): The evaluation point context

        Returns:
            BoolRef: Z3 constraint expressing the falsification condition

        Raises:
            TypeError: If the sentence has neither a sentence letter nor an operator
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        if operator is None:
            raise TypeError(
                f"Cannot falsify '{sentence.name}': "
                f"sentence has no operator or sentence letter."
            )
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_point)

    def max_compatible_part(self, state_x, state_w, state_y):
        """Determines if state_x is the maximal part of state_w compatible with state_y.

        This method checks whether state_x is a largest substate of state_w that maintains
        compatibility with state_y (there may be more than one). This is used to
        determine the alternative worlds used in the counterfactual semantics.

        Args:
            state_x (BitVecRef): The state being tested as maximal compatible part
            state_w (BitVecRef): The state containing state_x
            state_y (BitVecRef): The state that state_x must be compatible with

        Returns:
            BoolRef: Z3 constraint expressing whether state_x is a maximal part
                    of state_w that is compatible with state_y
        """
        z = z3.BitVec("max_part", self.N)
        return z3.And(
            self.is_part_of(state_x, state_w),
            self.compatible(state_x, state_y),
            ForAll(
                z,
                z3.Implies(
                    z3.And(
                        self.is_part_of(z, state_w),
                        self.compatible(z, state_y),
                        self.is_part_of(state_x, z),
                    ),
                    state_x == z,
                ),
            ),
        )

    def is_alternative(self, state_u, state_y, state_w):
        """Determines if a state represents an alternative world resulting from
        imposing one state on another.

        This method checks whether state_u is a possible world that results from imposing state_y
        on world state_w. The alternative world must contain state_y as a part and must also
        contain a maximal part of state_w that is compatible with state_y.

        Args:
            state_u (BitVecRef): The state being tested as an alternative world
            state_y (BitVecRef): The state being imposed
            state_w (BitVecRef): The world state being modified

        Returns:
            BoolRef: Z3 constraint expressing whether state_u is an alternative world
                    resulting from imposing state_y on state_w
        """
        z = z3.BitVec("alt_z", self.N)
        return z3.And(
            self.is_world(state_u),
            self.is_part_of(state_y, state_u),
            Exists(
                [z],
                cast(z3.BoolRef, z3.And(
                    self.is_part_of(z, state_u),
                    self.max_compatible_part(z, state_w, state_y)
                ))
            )
        )

    def calculate_alternative_worlds(self, verifiers, eval_point, model_structure):
        """Calculates alternative worlds where a given state is imposed.

        This method identifies all alternative worlds generated by the verifiers
        and evaluation world. These alternative worlds are used in the semantics
        for counterfactual conditionals.

        Args:
            verifiers (set): Set of states verifying the antecedent
            eval_point (dict): The evaluation point containing the reference world
            model_structure (ModelStructure): The model being evaluated

        Returns:
            set: Set of alternative worlds where the antecedent is true
        """
        is_alt = model_structure.semantics.is_alternative
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(is_alt(pw, ver, eval_world))
        }

    def product(self, set_A: Set['StateType'], set_B: Set['StateType']) -> Set['StateType']:
        """Compute the set of all pairwise fusions between elements of two sets.

        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors

        Returns:
            set: A set containing the fusion of each element from set_A with each element from set_B

        Note:
            Uses bitwise OR as the fusion operation between elements
        """
        product_set = set()
        for bit_a in set_A:
            for bit_b in set_B:
                bit_ab = z3.simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A: Set['StateType'], set_B: Set['StateType']) -> Set['StateType']:
        """Compute the union of two sets closed under pairwise fusion.

        Takes two sets and returns their union plus all possible fusions between
        their elements. The result is a set containing:
        1. All elements from both input sets
        2. All pairwise fusions between elements from the two sets

        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors

        Returns:
            set: The union of set_A and set_B closed under pairwise fusion
        """
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))

    def closer_world(self, world_u, world_v, eval_point):
        """Determines if world_u is closer than world_v to the evaluation world.

        This is a placeholder implementation for counterfactual semantics.
        A full implementation would define a similarity metric between worlds.

        Args:
            world_u (BitVecRef): First world to compare
            world_v (BitVecRef): Second world to compare
            eval_point (dict): The evaluation point containing reference world

        Returns:
            BoolRef: Z3 constraint expressing whether world_u is closer than world_v
        """
        # Placeholder: for now, just return False (no ordering)
        # A real implementation would define closeness based on similarity metrics
        return z3.BoolVal(False)

    def inject_z3_model_values(self, z3_model: z3.ModelRef,
                              original_semantics: 'LogosSemantics',
                              model_constraints: 'ModelConstraints') -> None:
        """Inject concrete Z3 values from iteration into model constraints.

        This method extracts values from a Z3 model and adds them as constraints
        for the next iteration. It handles Logos-specific concepts: worlds,
        possible states, verify, and falsify relations.

        Args:
            z3_model: Z3 model containing concrete values from solver
            original_semantics: Original semantics instance that created the Z3 functions
            model_constraints: ModelConstraints instance to update with injected values
        """
        # Get number of states from model_constraints settings
        num_states = 2 ** model_constraints.settings['N']

        # Inject world constraints
        for state in range(num_states):
            # Evaluate using original is_world function
            is_world_val = z3_model.eval(original_semantics.is_world(state), model_completion=True)
            # Add constraint using new is_world function
            if is_true(is_world_val):
                model_constraints.all_constraints.append(self.is_world(state))
            else:
                model_constraints.all_constraints.append(z3.Not(self.is_world(state)))

        # Inject possible state constraints
        for state in range(num_states):
            # Evaluate using original possible function
            is_possible_val = z3_model.eval(original_semantics.possible(state), model_completion=True)
            # Add constraint using new possible function
            if is_true(is_possible_val):
                model_constraints.all_constraints.append(self.possible(state))
            else:
                model_constraints.all_constraints.append(z3.Not(self.possible(state)))

        # Inject verify/falsify constraints for each sentence letter
        for sentence_obj in model_constraints.syntax.sentence_letters:
            atom = sentence_obj.sentence_letter

            # Inject verify constraints
            for state in range(num_states):
                # Evaluate using original verify function
                verify_val = z3_model.eval(original_semantics.verify(state, atom), model_completion=True)
                # Add constraint using new verify function
                if is_true(verify_val):
                    model_constraints.all_constraints.append(self.verify(state, atom))
                else:
                    model_constraints.all_constraints.append(z3.Not(self.verify(state, atom)))

            # Inject falsify constraints
            for state in range(num_states):
                # Evaluate using original falsify function
                falsify_val = z3_model.eval(original_semantics.falsify(state, atom), model_completion=True)
                # Add constraint using new falsify function
                if is_true(falsify_val):
                    model_constraints.all_constraints.append(self.falsify(state, atom))
                else:
                    model_constraints.all_constraints.append(z3.Not(self.falsify(state, atom)))

    def with_world(
        self,
        eval_point: 'EvaluationPoint',
        world: 'StateType'
    ) -> 'EvaluationPoint':
        """Create a new evaluation point with the given world.

        Creates a copy of the evaluation point with the world field set
        to the provided value, preserving all other keys (including assignment).
        Used by intensional operators to thread variable bindings through
        world-shifting evaluation.

        Args:
            eval_point: The base evaluation point to extend
            world: The world to evaluate in

        Returns:
            A new evaluation point dictionary with the world
        """
        return {**eval_point, "world": world}
