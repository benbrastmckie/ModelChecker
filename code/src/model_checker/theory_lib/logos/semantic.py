"""
Shared semantic framework for the logos theory.

This module implements the core semantic foundation for all logos subtheories,
providing unified classes for semantics, propositions, and model structures.
"""

import itertools
import sys
import time
from typing import Dict, Any, Optional, Set, Tuple, Union, List, TYPE_CHECKING

from z3 import simplify
import z3

from model_checker import syntactic
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.structure import ModelDefaults
from model_checker.syntactic.assignments import VariableAssignment
from model_checker.syntactic.terms import Term, Variable, Constant, FunctionApplication
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
    int_to_binary,
)

# Import protocols for type checking
if TYPE_CHECKING:
    from .protocols import (
        SemanticsProtocol,
        RegistryProtocol,
        EvaluationPoint,
        StateType,
        Z3Constraint,
        SettingsDict
    )
    from model_checker.syntactic import Sentence
    from model_checker.models.model_constraints import ModelConstraints


def term_denotation(
    term: Term,
    assignment: VariableAssignment,
    semantics: 'LogosSemantics'
) -> z3.BitVecRef:
    """Compute [[t]]^sigma_M - the denotation of term t.

    This function recursively evaluates a term to produce a Z3 bit vector
    representing a domain element (state/haecceity). The denotation depends
    on the current variable assignment and the model's interpretation of
    constants and functions.

    Args:
        term: The term to evaluate
        assignment: Current variable assignment sigma
        semantics: Model semantics providing interpretation functions

    Returns:
        Z3 bit vector representing the denoted state/haecceity

    Raises:
        KeyError: If a variable is not bound in the assignment, or
                 if a constant/function is not registered in semantics
        TypeError: If term is of unknown type

    Examples:
        >>> v_x = Variable("v_x")
        >>> sigma = assignment.variant(v_x, BitVecVal(3, N))
        >>> term_denotation(v_x, sigma, sem)  # Returns 3

        >>> semantics.register_constant('zero', BitVecVal(0, N))
        >>> term_denotation(Constant('zero'), sigma, sem)  # Returns 0
    """
    if isinstance(term, Variable):
        # [[v]]^sigma = sigma(v)
        # If variable is bound, return its value
        # If unbound (free variable), return a fresh Z3 variable
        # This handles open formulas by treating free variables as arbitrary domain elements
        try:
            return assignment[term]
        except KeyError:
            # Free variable - create a fresh Z3 variable for it
            # This is semantically correct: an open formula is satisfied iff
            # for all assignments to free variables, the formula holds
            return z3.BitVec(f"free_{term.name}", semantics.N)

    if isinstance(term, Constant):
        # [[c]]^sigma = |c| (interpretation of constant)
        # The semantics must have this constant registered
        return semantics.constant_interpretation(term.name)

    if isinstance(term, FunctionApplication):
        # [[f(t1, ..., tn)]]^sigma = |f|([[t1]]^sigma, ..., [[tn]]^sigma)
        # First evaluate all arguments recursively
        arg_denotations = tuple(
            term_denotation(arg, assignment, semantics)
            for arg in term.arguments
        )
        # Then apply the function interpretation
        return semantics.function_interpretation(term.name, arg_denotations)

    raise TypeError(f"Unknown term type: {type(term).__name__}")


class LogosSemantics(SemanticDefaults):
    """
    Shared semantic framework for all logos subtheories.
    
    This class provides the foundation for hyperintensional truthmaker semantics
    with support for modular operator loading and subtheory coordination.
    """
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10,
        'iterate': False,
        'expectation': None,
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
            syntactic.AtomSort,         # and a sentence letter
            z3.BoolSort()               # to a truth-value
        )
        self.falsify = z3.Function(
            "falsify",                  # Names the function 'falsify'
            z3.BitVecSort(self.N),      # which maps a bitvector
            syntactic.AtomSort,         # and a sentence letter
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

        # First-order infrastructure
        self._predicate_verifiers: Dict[str, z3.FuncDeclRef] = {}
        self._predicate_falsifiers: Dict[str, z3.FuncDeclRef] = {}
        self._constant_interpretations: Dict[str, z3.BitVecRef] = {}
        self._function_interpretations: Dict[str, z3.FuncDeclRef] = {}
    
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
        return z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        )

    def true_at(self, sentence: 'Sentence', eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a sentence is true at a given evaluation point.

        For atomic sentences (sentence_letters), it checks if there exists some state x
        that is part of the evaluation world such that x verifies the sentence letter.

        For complex sentences, it delegates to the operator's true_at method with the
        sentence's arguments and evaluation point.

        Task 14: Constants (bare identifiers or explicit <>) are domain elements,
        not propositions, and cannot be evaluated for truth. This raises TypeError.

        Args:
            sentence (Sentence): The sentence to evaluate
            eval_point (dict): The evaluation point containing a "world" key

        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is true at eval_point

        Raises:
            TypeError: If sentence is a constant (domain element, not proposition)
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]

        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))

        operator = sentence.operator
        if operator is None:
            # Check if this is a predicate application: [pred_name, term1, term2, ...]
            from model_checker.syntactic.terms import Term
            prefix = sentence.prefix_sentence
            if (isinstance(prefix, list) and len(prefix) >= 2 and
                isinstance(prefix[0], str) and
                all(isinstance(arg, Term) for arg in prefix[1:])):
                # Predicate application: evaluate using predicate_verify
                pred_name = prefix[0]
                term_args = prefix[1:]
                return self._predicate_true_at(pred_name, term_args, eval_point)

            # Task 14: No operator and no sentence_letter means this is a constant
            # Constants are domain elements, not propositions
            raise TypeError(
                f"Cannot evaluate truth of '{sentence.name}': "
                f"constants are domain elements, not propositions. "
                f"Use predicate syntax P[] for sentence letters."
            )
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_point)

    def false_at(self, sentence: 'Sentence', eval_point: 'EvaluationPoint') -> 'Z3Constraint':
        """Determines if a sentence is false at a given evaluation point.

        For atomic sentences (sentence_letters), it checks if there exists some state x
        that is part of the evaluation world such that x falsifies the sentence letter.

        For complex sentences, it delegates to the operator's false_at method with the
        sentence's arguments and evaluation point.

        Task 14: Constants (bare identifiers or explicit <>) are domain elements,
        not propositions, and cannot be evaluated for falsity. This raises TypeError.

        Args:
            sentence (Sentence): The sentence to evaluate
            eval_point (dict): The evaluation point containing a "world" key

        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is false at eval_point

        Raises:
            TypeError: If sentence is a constant (domain element, not proposition)
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]

        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))

        operator = sentence.operator
        if operator is None:
            # Check if this is a predicate application: [pred_name, term1, term2, ...]
            from model_checker.syntactic.terms import Term
            prefix = sentence.prefix_sentence
            if (isinstance(prefix, list) and len(prefix) >= 2 and
                isinstance(prefix[0], str) and
                all(isinstance(arg, Term) for arg in prefix[1:])):
                # Predicate application: evaluate using predicate_falsify
                pred_name = prefix[0]
                term_args = prefix[1:]
                return self._predicate_false_at(pred_name, term_args, eval_point)

            # Task 14: No operator and no sentence_letter means this is a constant
            # Constants are domain elements, not propositions
            raise TypeError(
                f"Cannot evaluate falsity of '{sentence.name}': "
                f"constants are domain elements, not propositions. "
                f"Use predicate syntax P[] for sentence letters."
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

        Task 14: Constants cannot be verified - they are domain elements, not propositions.

        Args:
            state (BitVecRef): The state being tested as a verifier
            sentence (Sentence): The sentence to check
            eval_point (dict): The evaluation point context

        Returns:
            BoolRef: Z3 constraint expressing the verification condition

        Raises:
            TypeError: If sentence is a constant (domain element, not proposition)
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        if operator is None:
            # Check if this is a predicate application: [pred_name, term1, term2, ...]
            from model_checker.syntactic.terms import Term
            prefix = sentence.prefix_sentence
            if (isinstance(prefix, list) and len(prefix) >= 2 and
                isinstance(prefix[0], str) and
                all(isinstance(arg, Term) for arg in prefix[1:])):
                # Predicate application: evaluate using predicate extended verify
                pred_name = prefix[0]
                term_args = prefix[1:]
                return self._predicate_extended_verify(state, pred_name, term_args, eval_point)

            raise TypeError(
                f"Cannot verify '{sentence.name}': "
                f"constants are domain elements, not propositions. "
                f"Use predicate syntax P[] for sentence letters."
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

        Task 14: Constants cannot be falsified - they are domain elements, not propositions.

        Args:
            state (BitVecRef): The state being tested as a falsifier
            sentence (Sentence): The sentence to check
            eval_point (dict): The evaluation point context

        Returns:
            BoolRef: Z3 constraint expressing the falsification condition

        Raises:
            TypeError: If sentence is a constant (domain element, not proposition)
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        if operator is None:
            # Check if this is a predicate application: [pred_name, term1, term2, ...]
            from model_checker.syntactic.terms import Term
            prefix = sentence.prefix_sentence
            if (isinstance(prefix, list) and len(prefix) >= 2 and
                isinstance(prefix[0], str) and
                all(isinstance(arg, Term) for arg in prefix[1:])):
                # Predicate application: evaluate using predicate extended falsify
                pred_name = prefix[0]
                term_args = prefix[1:]
                return self._predicate_extended_falsify(state, pred_name, term_args, eval_point)

            raise TypeError(
                f"Cannot falsify '{sentence.name}': "
                f"constants are domain elements, not propositions. "
                f"Use predicate syntax P[] for sentence letters."
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
                z3.And(
                    self.is_part_of(z, state_u),
                    self.max_compatible_part(z, state_w, state_y)
                )
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
                bit_ab = simplify(bit_a | bit_b)
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
            if z3.is_true(is_world_val):
                model_constraints.all_constraints.append(self.is_world(state))
            else:
                model_constraints.all_constraints.append(z3.Not(self.is_world(state)))
        
        # Inject possible state constraints
        for state in range(num_states):
            # Evaluate using original possible function
            is_possible_val = z3_model.eval(original_semantics.possible(state), model_completion=True)
            # Add constraint using new possible function
            if z3.is_true(is_possible_val):
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
                if z3.is_true(verify_val):
                    model_constraints.all_constraints.append(self.verify(state, atom))
                else:
                    model_constraints.all_constraints.append(z3.Not(self.verify(state, atom)))
            
            # Inject falsify constraints
            for state in range(num_states):
                # Evaluate using original falsify function
                falsify_val = z3_model.eval(original_semantics.falsify(state, atom), model_completion=True)
                # Add constraint using new falsify function
                if z3.is_true(falsify_val):
                    model_constraints.all_constraints.append(self.falsify(state, atom))
                else:
                    model_constraints.all_constraints.append(z3.Not(self.falsify(state, atom)))

    # =========================================================================
    # First-Order Semantics Infrastructure
    # =========================================================================

    def get_assignment(self, eval_point: 'EvaluationPoint') -> VariableAssignment:
        """Extract variable assignment from evaluation point.

        If no assignment is present in the evaluation point, returns an empty
        assignment. This allows operators to access variable bindings during
        first-order evaluation.

        Args:
            eval_point: The evaluation point dictionary

        Returns:
            VariableAssignment: The current variable assignment, or empty if none
        """
        return eval_point.get("assignment", VariableAssignment.empty())

    def with_assignment(
        self,
        eval_point: 'EvaluationPoint',
        assignment: VariableAssignment
    ) -> 'EvaluationPoint':
        """Create a new evaluation point with the given assignment.

        Creates a copy of the evaluation point with the assignment field set
        to the provided value. Used by first-order operators to thread
        variable bindings through recursive evaluation.

        Args:
            eval_point: The base evaluation point to extend
            assignment: The variable assignment to include

        Returns:
            A new evaluation point dictionary with the assignment
        """
        return {**eval_point, "assignment": assignment}

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

    def register_constant(self, name: str, value: z3.BitVecRef) -> None:
        """Register a constant with its interpretation.

        Associates a constant name with a specific domain element (bit vector).
        This interpretation is used when computing term denotations.

        Args:
            name: The constant name (e.g., 'a', 'zero')
            value: The domain element this constant denotes
        """
        self._constant_interpretations[name] = value

    def constant_interpretation(self, name: str) -> z3.BitVecRef:
        """Get the interpretation of a constant.

        Auto-registers unknown constants with a fresh Z3 BitVec variable.
        This allows constants to be used without explicit registration,
        supporting first-order examples that reference constants like 'a<>'.

        Args:
            name: The constant name

        Returns:
            The domain element denoted by this constant
        """
        if name not in self._constant_interpretations:
            # Auto-register with a fresh Z3 BitVec variable
            # Use const_{name} naming convention for consistency
            fresh_const = z3.BitVec(f"const_{name}", self.N)
            self._constant_interpretations[name] = fresh_const
        return self._constant_interpretations[name]

    def register_function(self, name: str, arity: int) -> None:
        """Register a function symbol with its interpretation.

        Creates a Z3 function declaration for the function symbol.
        The function maps n domain elements to a domain element.

        Args:
            name: The function symbol name (e.g., 'succ', 'plus')
            arity: The number of arguments the function takes
        """
        # Function maps arity bit vectors to a bit vector
        arg_sorts = [z3.BitVecSort(self.N)] * arity
        self._function_interpretations[name] = z3.Function(
            f"func_{name}",
            *arg_sorts,
            z3.BitVecSort(self.N)
        )

    def function_interpretation(
        self,
        name: str,
        args: tuple[z3.BitVecRef, ...]
    ) -> z3.BitVecRef:
        """Apply a function interpretation to arguments.

        Args:
            name: The function symbol name
            args: The argument values (already evaluated)

        Returns:
            The result of applying the function to the arguments

        Raises:
            KeyError: If the function has not been registered
        """
        if name not in self._function_interpretations:
            raise KeyError(f"Function '{name}' not registered. "
                          f"Call register_function('{name}', arity) first.")
        return self._function_interpretations[name](*args)

    def register_predicate(self, name: str, arity: int) -> None:
        """Register a predicate with verifier/falsifier functions.

        Creates Z3 functions for |F|+ and |F|- interpretation.
        These functions map n domain elements plus a state to a boolean,
        representing whether the state is in the verifier/falsifier set
        for the predicate applied to those arguments.

        Args:
            name: The predicate name (e.g., 'P', 'Loves')
            arity: The number of arguments the predicate takes
        """
        # Verifier function: maps n args + verifier state to bool
        # Represents: s in |F|+(d1, ..., dn)
        verifier_args = [z3.BitVecSort(self.N)] * arity + [z3.BitVecSort(self.N)]
        self._predicate_verifiers[name] = z3.Function(
            f"pred_verify_{name}",
            *verifier_args,
            z3.BoolSort()
        )

        # Falsifier function: maps n args + falsifier state to bool
        # Represents: s in |F|-(d1, ..., dn)
        self._predicate_falsifiers[name] = z3.Function(
            f"pred_falsify_{name}",
            *verifier_args,
            z3.BoolSort()
        )

        # Add no_glut constraint for predicates: verifiers incompatible with falsifiers
        # This mirrors the no_glut constraint for sentence letters:
        # ForAll args, x, y. (verify(args, x) AND falsify(args, y)) => Not(compatible(x, y))
        arg_vars = [z3.BitVec(f"pred_ng_{name}_arg{i}", self.N) for i in range(arity)]
        x = z3.BitVec(f"pred_ng_{name}_x", self.N)
        y = z3.BitVec(f"pred_ng_{name}_y", self.N)
        all_vars = arg_vars + [x, y]

        verify_func = self._predicate_verifiers[name]
        falsify_func = self._predicate_falsifiers[name]

        no_glut_constraint = ForAll(
            all_vars,
            z3.Implies(
                z3.And(
                    verify_func(*arg_vars, x),
                    falsify_func(*arg_vars, y)
                ),
                z3.Not(self.compatible(x, y))
            )
        )
        self.frame_constraints.append(no_glut_constraint)

    def predicate_verify(
        self,
        name: str,
        args: tuple[z3.BitVecRef, ...],
        state: z3.BitVecRef
    ) -> z3.BoolRef:
        """Check if state verifies predicate F(args).

        Args:
            name: The predicate name
            args: The argument values (domain elements)
            state: The state being tested as a verifier

        Returns:
            Z3 constraint expressing whether state is in |F|+(args)

        Raises:
            KeyError: If the predicate has not been registered
        """
        if name not in self._predicate_verifiers:
            raise KeyError(f"Predicate '{name}' not registered. "
                          f"Call register_predicate('{name}', arity) first.")
        return self._predicate_verifiers[name](*args, state)

    def predicate_falsify(
        self,
        name: str,
        args: tuple[z3.BitVecRef, ...],
        state: z3.BitVecRef
    ) -> z3.BoolRef:
        """Check if state falsifies predicate F(args).

        Args:
            name: The predicate name
            args: The argument values (domain elements)
            state: The state being tested as a falsifier

        Returns:
            Z3 constraint expressing whether state is in |F|-(args)

        Raises:
            KeyError: If the predicate has not been registered
        """
        if name not in self._predicate_falsifiers:
            raise KeyError(f"Predicate '{name}' not registered. "
                          f"Call register_predicate('{name}', arity) first.")
        return self._predicate_falsifiers[name](*args, state)

    def _predicate_true_at(self, pred_name, term_args, eval_point):
        """Evaluate truth of a predicate application at an evaluation point.

        P(t1, ..., tn) is true at w iff there exists a state x that is part of w
        and x verifies P(d1, ..., dn) where di = [[ti]].

        Args:
            pred_name: Name of the predicate
            term_args: List of Term objects as arguments
            eval_point: Evaluation point with world and assignment

        Returns:
            Z3 constraint for predicate truth
        """
        eval_world = eval_point["world"]
        assignment = self.get_assignment(eval_point)

        # Compute denotations of all term arguments
        arg_denotations = tuple(
            term_denotation(arg, assignment, self)
            for arg in term_args
        )

        # Register predicate if not already registered
        arity = len(term_args)
        if pred_name not in self._predicate_verifiers:
            self.register_predicate(pred_name, arity)

        # P(args) is true iff exists x. x <= w and x verifies P(args)
        x = z3.BitVec(f"pred_t_{pred_name}_x", self.N)
        return Exists(
            x,
            z3.And(
                self.is_part_of(x, eval_world),
                self.predicate_verify(pred_name, arg_denotations, x)
            )
        )

    def _predicate_false_at(self, pred_name, term_args, eval_point):
        """Evaluate falsity of a predicate application at an evaluation point.

        P(t1, ..., tn) is false at w iff there exists a state x that is part of w
        and x falsifies P(d1, ..., dn) where di = [[ti]].

        Args:
            pred_name: Name of the predicate
            term_args: List of Term objects as arguments
            eval_point: Evaluation point with world and assignment

        Returns:
            Z3 constraint for predicate falsity
        """
        eval_world = eval_point["world"]
        assignment = self.get_assignment(eval_point)

        # Compute denotations of all term arguments
        arg_denotations = tuple(
            term_denotation(arg, assignment, self)
            for arg in term_args
        )

        # Register predicate if not already registered
        arity = len(term_args)
        if pred_name not in self._predicate_falsifiers:
            self.register_predicate(pred_name, arity)

        # P(args) is false iff exists x. x <= w and x falsifies P(args)
        x = z3.BitVec(f"pred_f_{pred_name}_x", self.N)
        return Exists(
            x,
            z3.And(
                self.is_part_of(x, eval_world),
                self.predicate_falsify(pred_name, arg_denotations, x)
            )
        )

    def _predicate_extended_verify(self, state, pred_name, term_args, eval_point):
        """Determine if a state verifies a predicate application.

        A state x verifies P(t1, ..., tn) iff x is a verifier for P(d1, ..., dn)
        where di = [[ti]] (term denotation).

        Args:
            state: The state being tested as verifier
            pred_name: Name of the predicate
            term_args: List of Term objects as arguments
            eval_point: Evaluation point with world and assignment

        Returns:
            Z3 constraint for predicate verification
        """
        assignment = self.get_assignment(eval_point)

        # Compute denotations of all term arguments
        arg_denotations = tuple(
            term_denotation(arg, assignment, self)
            for arg in term_args
        )

        # Register predicate if not already registered
        arity = len(term_args)
        if pred_name not in self._predicate_verifiers:
            self.register_predicate(pred_name, arity)

        # State verifies P(args) iff it's in the predicate's verifier function
        return self.predicate_verify(pred_name, arg_denotations, state)

    def _predicate_extended_falsify(self, state, pred_name, term_args, eval_point):
        """Determine if a state falsifies a predicate application.

        A state x falsifies P(t1, ..., tn) iff x is a falsifier for P(d1, ..., dn)
        where di = [[ti]] (term denotation).

        Args:
            state: The state being tested as falsifier
            pred_name: Name of the predicate
            term_args: List of Term objects as arguments
            eval_point: Evaluation point with world and assignment

        Returns:
            Z3 constraint for predicate falsification
        """
        assignment = self.get_assignment(eval_point)

        # Compute denotations of all term arguments
        arg_denotations = tuple(
            term_denotation(arg, assignment, self)
            for arg in term_args
        )

        # Register predicate if not already registered
        arity = len(term_args)
        if pred_name not in self._predicate_falsifiers:
            self.register_predicate(pred_name, arity)

        # State falsifies P(args) iff it's in the predicate's falsifier function
        return self.predicate_falsify(pred_name, arg_denotations, state)


class LogosProposition(PropositionDefaults):
    """
    Proposition class with modular operator support.
    
    Represents propositional content in the logos semantic framework
    with support for all subtheory operators.
    """
    
    def __init__(self, sentence: 'Sentence', model_structure: Any,
                 eval_world: Union[str, 'StateType'] = 'main') -> None:
        """Initialize a LogosProposition instance.

        Args:
            sentence (Sentence): The sentence whose proposition is being represented
            model_structure (ModelStructure): The model structure containing semantic definitions
            eval_world (str|BitVecRef, optional): The world at which to evaluate the proposition.
                If 'main', uses the model's main world. Defaults to 'main'.
        """
        super().__init__(sentence, model_structure)
        self.eval_world = model_structure.main_point["world"] if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
    
    def proposition_constraints(self, sentence_letter: Any) -> List['Z3Constraint']:
        """Generates Z3 constraints for a sentence letter based on semantic settings.

        This method generates constraints that govern the behavior of atomic propositions
        in the model following the default theory pattern.
        
        Args:
            sentence_letter: The atomic sentence letter to generate constraints for
            
        Returns:
            list: List of Z3 constraints for the sentence letter
        """
        semantics = self.semantics
        
        def get_classical_constraints():
            """Generate constraints that enforce classical behavior by ruling out
            truth value gaps and gluts.
            
            These constraints ensure:
            1. If two states verify a proposition, their fusion also verifies it
            2. If two states falsify a proposition, their fusion also falsifies it  
            3. No verifier is compatible with any falsifier (no gluts)
            4. Every possible state must be compatible with either a verifier or falsifier (no gaps)
            """
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", semantics.N)
            
            verifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.verify(y, sentence_letter)
                    ),
                    semantics.verify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            falsifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.falsify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    ),
                    semantics.falsify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            no_glut = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    ),
                    z3.Not(semantics.compatible(x, y)),
                ),
            )
            no_gap = ForAll(
                x,
                z3.Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        z3.And(
                            semantics.compatible(x, y),
                            z3.Or(
                                semantics.verify(y, sentence_letter),
                                semantics.falsify(y, sentence_letter)
                            ),
                        ),
                    ),
                ),
            )
            return [
                verifier_fusion_closure,
                falsifier_fusion_closure,
                no_glut,
                no_gap
            ]

        def get_contingent_constraints():
            """The contingent constraints ensure that each atomic proposition has
            at least one possible verifier and one possible falsifier, which implicitly
            guarantees that no null states are verifiers or falsifiers."""
            x, y = z3.BitVecs("ct_cont_x ct_cont_y", semantics.N)
            possible_verifier = Exists(
                x,
                z3.And(semantics.possible(x), semantics.verify(x, sentence_letter))
            )
            possible_falsifier = Exists(
                y,
                z3.And(semantics.possible(y), semantics.falsify(y, sentence_letter))
            )
            return [
                possible_verifier,
                possible_falsifier,
            ]

        def get_non_null_constraints():
            """The non_null constraints prevent null states (empty states) from being verifiers
            or falsifiers. These constraints are important to prevent trivial satisfaction of
            the disjoint constraints, though they are already entailed by the contingent constraints
            when those are enabled."""
            return [
                z3.Not(semantics.verify(0, sentence_letter)),
                z3.Not(semantics.falsify(0, sentence_letter)),
            ]

        def get_disjoint_constraints():
            """Generate disjoint constraints."""
            x = z3.BitVec("dt_disj_x", semantics.N)
            return [
                ForAll(
                    [x],
                    z3.Not(z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(x, sentence_letter)
                    )),
                )
            ]

        def get_non_empty_constraints():
            """The non_empty constraints ensure that each atomic proposition has at least one
            verifier and one falsifier. While these constraints are implied by the contingent
            constraints, they are included separately to prevent trivial satisfaction of the
            disjoint constraints when contingent constraints are not enabled."""
            x, y = z3.BitVecs("ct_empty_x ct_empty_y", semantics.N)
            return [
                z3.Exists(
                    [x, y],
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    )
                )
            ]

        # Generate constraints following default theory pattern
        constraints = get_classical_constraints()
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraints())
        if self.settings['non_empty'] and not self.settings['contingent']:
            constraints.extend(get_non_empty_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
            constraints.extend(get_non_null_constraints())
        if self.settings['non_null'] and not self.settings['disjoint']:
            constraints.extend(get_non_null_constraints())
        return constraints

    def find_proposition(
        self,
        assignment: Optional['VariableAssignment'] = None
    ) -> Tuple[Set['StateType'], Set['StateType']]:
        """Computes the verifier and falsifier sets for this proposition.

        This method determines the sets of states that verify and falsify
        the proposition in the model. For atomic propositions, it uses the
        verify and falsify relations; for complex propositions, it delegates
        to the appropriate operator's implementation.

        Task 21: Added optional assignment parameter for first-order logic.
        When evaluating open formulas (those with free variables bound by an
        outer quantifier), the assignment parameter provides the variable
        bindings needed to compute the correct verifiers and falsifiers.

        Args:
            assignment: Optional variable assignment for first-order evaluation.
                When provided, the assignment is included in the eval_point
                passed to operators. Defaults to None (empty assignment).

        Returns:
            tuple: A pair (verifiers, falsifiers) containing the sets of
                 states that verify and falsify the proposition respectively
        """
        model = self.model_structure.z3_model
        if model is None:
            # If no model is available, return empty sets
            # This can happen during iteration when models are being created
            return set(), set()

        # Clean proposition computation without debug output

        semantics = self.semantics
        eval_world = self.eval_world
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            V = {
                state for state in self.model_structure.all_states
                if self._evaluate_z3_boolean(model, semantics.verify(state, sentence_letter))
            }
            F = {
                state for state in self.model_structure.all_states
                if self._evaluate_z3_boolean(model, semantics.falsify(state, sentence_letter))
            }
            return V, F
        if operator is not None:
            # Task 21: Build eval_point with assignment if provided
            eval_point = {"world": eval_world}
            if assignment is not None:
                eval_point = semantics.with_assignment(eval_point, assignment)
            return operator.find_verifiers_and_falsifiers(*arguments, eval_point)

        # Check if this is a predicate application: [pred_name, term1, term2, ...]
        from model_checker.syntactic.terms import Term
        prefix = self.sentence.prefix_sentence
        if (isinstance(prefix, list) and len(prefix) >= 2 and
            isinstance(prefix[0], str) and
            all(isinstance(arg, Term) for arg in prefix[1:])):
            # Predicate application: find verifiers/falsifiers
            pred_name = prefix[0]
            term_args = prefix[1:]
            # Task 21: Pass assignment to predicate finder
            return self._predicate_find_proposition(pred_name, term_args, eval_world, assignment)

        raise ValueError(f"There is no proposition for {self}.")

    def _predicate_find_proposition(self, pred_name, term_args, eval_world, assignment=None):
        """Find verifiers and falsifiers for a predicate application.

        Args:
            pred_name: Name of the predicate
            term_args: List of Term objects as arguments
            eval_world: The evaluation world
            assignment: Optional variable assignment for first-order evaluation

        Returns:
            tuple: A pair (verifiers, falsifiers) containing the sets of states
        """
        model = self.model_structure.z3_model
        semantics = self.semantics
        eval_point = {"world": eval_world}

        # Task 21: Use provided assignment or get from empty eval_point
        if assignment is None:
            assignment = semantics.get_assignment(eval_point)
        else:
            eval_point = semantics.with_assignment(eval_point, assignment)

        # Compute denotations of all term arguments
        arg_denotations = tuple(
            term_denotation(arg, assignment, semantics)
            for arg in term_args
        )

        # Register predicate if not already registered
        arity = len(term_args)
        if pred_name not in semantics._predicate_verifiers:
            semantics.register_predicate(pred_name, arity)

        # Find all states that verify/falsify the predicate
        V = {
            state for state in self.model_structure.all_states
            if self._evaluate_z3_boolean(model, semantics.predicate_verify(pred_name, arg_denotations, state))
        }
        F = {
            state for state in self.model_structure.all_states
            if self._evaluate_z3_boolean(model, semantics.predicate_falsify(pred_name, arg_denotations, state))
        }
        return V, F

    def _evaluate_z3_boolean(self, z3_model: z3.ModelRef, expression: z3.BoolRef) -> bool:
        """Safely evaluate a Z3 boolean expression to a Python boolean.
        
        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values.
        
        Args:
            z3_model: The Z3 model to use for evaluation
            expression: The Z3 boolean expression to evaluate
            
        Returns:
            bool: True if the expression evaluates to true, False otherwise
        """
        
        try:
            # Evaluate the expression with model completion
            result = z3_model.evaluate(expression, model_completion=True)
            
            # Check if result is a boolean constant
            if z3.is_true(result):
                return True
            elif z3.is_false(result):
                return False
            
            # Try to simplify
            simplified = z3.simplify(result)
            if z3.is_true(simplified):
                return True
            elif z3.is_false(simplified):
                return False
                
            # Check string representation as last resort
            if str(simplified) == "True":
                return True
            elif str(simplified) == "False":
                return False
                
            # Conservative default
            return False
            
        except Exception:
            return False

    def truth_value_at(self, eval_world: 'StateType') -> bool:
        """Determines the truth value of the proposition at a given world.
        
        Checks if the world contains a verifier for the proposition (making it true)
        or a falsifier (making it false). Also checks for potential inconsistencies
        where a world contains both a verifier and falsifier, which should not occur
        in a well-formed model.
        
        Args:
            eval_world (BitVecRef): The world at which to evaluate the proposition
            
        Returns:
            bool: True if the world contains a verifier, False if it contains a falsifier
            
        Note:
            Prints a warning if an inconsistency is detected where a world contains
            both a verifier and falsifier for the same proposition.
        """
        semantics = self.model_structure.model_constraints.semantics
        z3_model = self.model_structure.z3_model
        ver_witness = None
        fal_witness = None
        exists_verifier = False
        exists_falsifier = False
        for verifier in self.verifiers:
            if z3_model.eval(semantics.is_part_of(verifier, eval_world), model_completion=True):
                ver_witness = verifier
                exists_verifier = True
                break
        for falsifier in self.falsifiers:
            if z3_model.eval(semantics.is_part_of(falsifier, eval_world), model_completion=True):
                fal_witness = falsifier
                exists_falsifier = True
                break
        if exists_verifier == exists_falsifier:
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {bitvec_to_substates(eval_world, self.N)} contains both:\n "
                f"  The verifier {bitvec_to_substates(ver_witness, self.N)}; and"
                f"  The falsifier {bitvec_to_substates(fal_witness, self.N)}."
            )
        return exists_verifier

    def print_proposition(self, eval_point: 'EvaluationPoint',
                         indent_num: int, use_colors: bool) -> None:
        """Print the proposition with its truth value at the given evaluation point.

        Prints the proposition name, its verifiers and falsifiers, and its truth value
        at the specified evaluation world. The output is formatted with optional
        indentation and color coding.

        Args:
            eval_point (dict): Dictionary containing evaluation context, including the 'world' key
            indent_num (int): Number of indentation levels to use
            use_colors (bool): Whether to use ANSI color codes in the output

        Returns:
            None
        """
        N = self.model_structure.model_constraints.semantics.N
        eval_world = eval_point["world"]
        truth_value = self.truth_value_at(eval_world)
        world_state = bitvec_to_substates(eval_world, N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )

    def __repr__(self) -> str:
        """Return a string representation of the proposition.

        Returns a string showing the verifiers and falsifiers of the proposition
        in set notation. Only includes possible states unless print_impossible
        setting is enabled.

        Returns:
            str: A string of the form "< {verifiers}, {falsifiers} >" where each
                set contains the binary representations of the states
        """
        # Guard against missing verifiers/falsifiers attribute (e.g., during error handling)
        if not hasattr(self, 'verifiers') or not hasattr(self, 'falsifiers'):
            sentence_name = getattr(self, 'sentence', None)
            if sentence_name is not None:
                sentence_name = getattr(sentence_name, 'name', str(sentence_name))
            return f"<LogosProposition: {sentence_name} (uninitialized)>"

        N = self.model_structure.model_constraints.semantics.N
        possible = self.model_structure.model_constraints.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
            if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        }
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        }
        return f"< {pretty_set_print(ver_states)}, {pretty_set_print(fal_states)} >"


class LogosModelStructure(ModelDefaults):
    """
    Model structure with modular operator support.
    
    Manages the overall semantic model structure for the logos theory
    with support for all subtheories and modular operator loading.
    """
    
    def __init__(self, model_constraints: 'ModelConstraints', settings: Dict[str, Any]) -> None:
        super().__init__(model_constraints, settings)
        self.loaded_subtheories = []
        
        # Get main point
        self.main_world = self.main_point["world"]
        
        # Initialize Z3 model values
        self.z3_main_world = None
        self.z3_possible_states = None
        self.z3_world_states = None 
        
        # Initialize attributes for difference tracking
        self.model_differences = None  # Will store differences with previous model
        self.previous_model = None     # Reference to previous model for comparison

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self.z3_main_world = self.z3_model[self.main_world]
            self.main_point["world"] = self.z3_main_world
            self.z3_possible_states = [
                bit
                for bit in self.all_states
                if bool(self.z3_model.evaluate(self.semantics.possible(bit)))
            ]
            self.z3_world_states = [
                bit
                for bit in self.z3_possible_states
                if bool(self.z3_model.evaluate(self.semantics.is_world(bit)))
            ]
    
    def load_subtheories(self, subtheories: List[str]) -> None:
        """Load specified subtheories into the model."""
        self.loaded_subtheories.extend(subtheories)
        if hasattr(self.semantics, 'load_subtheories'):
            self.semantics.load_subtheories(subtheories)
    
    def get_available_operators(self) -> Dict[str, Any]:
        """Get all operators from loaded subtheories."""
        if hasattr(self.semantics, 'operator_registry'):
            return self.semantics.operator_registry.get_operators()
        return {}
    
    def print_model_info(self) -> None:
        """Print information about the loaded model."""
        print(f"Logos Theory Model")
        print(f"Loaded subtheories: {', '.join(self.loaded_subtheories)}")
        
        operators = self.get_available_operators()
        if operators:
            print(f"Available operators: {len(operators)}")
            for name, op in operators.items():
                print(f"  - {name}: {op.__class__.__name__}")
        else:
            print("No operators loaded")

    def _evaluate_z3_boolean_for_model(self, expression: z3.BoolRef) -> bool:
        """Safely evaluate a Z3 boolean expression using the model.

        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values.

        Args:
            expression: The Z3 boolean expression to evaluate

        Returns:
            bool: True if the expression evaluates to true, False otherwise
        """
        try:
            result = self.z3_model.evaluate(expression, model_completion=True)
            if z3.is_true(result):
                return True
            elif z3.is_false(result):
                return False

            # Try to simplify
            simplified = z3.simplify(result)
            if z3.is_true(simplified):
                return True
            elif z3.is_false(simplified):
                return False

            # Conservative default
            return False
        except Exception:
            return False

    def _get_predicate_extension(
        self,
        pred_name: str,
        arg_tuple: Tuple[z3.BitVecRef, ...]
    ) -> Tuple[Set[str], Set[str]]:
        """Get the verifier and falsifier states for a predicate application.

        Evaluates the predicate at the given argument tuple and returns the
        sets of states that verify and falsify the predicate application.

        Args:
            pred_name: The name of the predicate (e.g., 'F', 'R')
            arg_tuple: Tuple of Z3 bitvector values for the arguments

        Returns:
            Tuple of (verifier_states, falsifier_states) where each is a set
            of state strings formatted via bitvec_to_substates.
        """
        verifier_states: Set[str] = set()
        falsifier_states: Set[str] = set()

        for state in self.all_states:
            # Check if state is possible (unless print_impossible is True)
            is_possible = self._evaluate_z3_boolean_for_model(
                self.semantics.possible(state)
            )
            if not is_possible and not self.settings.get('print_impossible', False):
                continue

            # Check if state verifies the predicate application
            verify_expr = self.semantics.predicate_verify(pred_name, arg_tuple, state)
            if self._evaluate_z3_boolean_for_model(verify_expr):
                verifier_states.add(bitvec_to_substates(state, self.N))

            # Check if state falsifies the predicate application
            falsify_expr = self.semantics.predicate_falsify(pred_name, arg_tuple, state)
            if self._evaluate_z3_boolean_for_model(falsify_expr):
                falsifier_states.add(bitvec_to_substates(state, self.N))

        return verifier_states, falsifier_states

    def print_predicate_extensions(self, output=sys.__stdout__) -> None:
        """Print predicate extensions showing what each predicate maps to for each domain element.

        For each registered predicate, displays the verifier and falsifier states
        for every combination of domain element arguments. This helps users
        understand how predicates are interpreted in the countermodel.

        The output format is:
            PREDICATE EXTENSIONS:

            F (arity 1):
              F() = < {verifiers}, {falsifiers} >
              F(a) = < {verifiers}, {falsifiers} >
              ...

            R (arity 2):
              R(, ) = < {verifiers}, {falsifiers} >
              R(, a) = < {verifiers}, {falsifiers} >
              ...

        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        # Skip if no predicates are registered
        if not self.semantics._predicate_verifiers:
            return

        # Set up colors
        BLUE = ""
        RESET = ""
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"

        print(f"\n{BLUE}PREDICATE EXTENSIONS:{RESET}\n", file=output)

        # Iterate over predicates in sorted order for consistent output
        for pred_name in sorted(self.semantics._predicate_verifiers.keys()):
            verify_func = self.semantics._predicate_verifiers[pred_name]
            # Arity is function arity minus 1 (the state argument)
            arity = verify_func.arity() - 1

            print(f"{pred_name} (arity {arity}):", file=output)

            # Enumerate all domain element combinations
            # Domain elements are 0 to 2^N - 1
            domain_range = range(2 ** self.N)

            for args in itertools.product(domain_range, repeat=arity):
                # Convert integer args to Z3 bitvector values
                arg_bitvecs = tuple(z3.BitVecVal(a, self.N) for a in args)

                # Get verifier and falsifier states
                ver_states, fal_states = self._get_predicate_extension(pred_name, arg_bitvecs)

                # Format domain element arguments for display
                arg_strs = [bitvec_to_substates(z3.BitVecVal(a, self.N), self.N) for a in args]
                args_display = ", ".join(arg_strs)

                # Format output like propositions: < verifiers, falsifiers >
                print(
                    f"  {pred_name}({args_display}) = < {pretty_set_print(ver_states)}, {pretty_set_print(fal_states)} >",
                    file=output
                )

            print(file=output)

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print a complete overview of the model structure and evaluation results.
        
        This method provides a comprehensive display of the model, including:
        - Model states and their properties
        - Evaluation results at the designated world
        - Truth values of atomic sentence letters
        - Recursive evaluation of complex sentences and their subformulas
        
        Args:
            default_settings (dict): Default configuration settings for the model
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            output (file, optional): Output stream to write to. Defaults to sys.stdout
        """
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_evaluation(output)
            self.print_predicate_extensions(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds", file=output)
            # Always print closing separator for countermodels  
            print(f"\n{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print the model details to the specified output stream.

        This method prints all elements of the model including states, evaluation results,
        and optionally constraints to the provided output stream.

        Args:
            default_settings (dict): Default configuration settings for the model
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            print_constraints (bool, optional): Whether to print model constraints.
                Defaults to the value in self.settings.
            output (TextIO, optional): Output stream to write to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
        # Check if we actually timed out (runtime >= max_time)
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime is not None and self.z3_model_runtime >= self.max_time
        
        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
        self.print_all(self.settings, example_name, theory_name, output)
        
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def print_model_differences(self, output=sys.stdout):
        """Print differences between this model and the previous one.
        
        Logos-specific implementation that understands hyperintensional semantics.
        
        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return
        
        diffs = self.model_differences
        
        # Use colors if outputting to terminal
        if output is sys.stdout:
            GREEN = "\033[32m"
            RED = "\033[31m"
            YELLOW = "\033[33m"
            BLUE = "\033[34m"
            RESET = "\033[0m"
        else:
            GREEN = RED = YELLOW = BLUE = RESET = ""
        
        print(f"\n{YELLOW}=== DIFFERENCES FROM PREVIOUS MODEL ==={RESET}\n", file=output)
        
        # Print world changes
        if diffs.get('world_changes', {}).get('added') or diffs.get('world_changes', {}).get('removed'):
            print(f"{BLUE}World Changes:{RESET}", file=output)
            for world in diffs.get('world_changes', {}).get('added', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {GREEN}+ {world_str} (now a world){RESET}", file=output)
            for world in diffs.get('world_changes', {}).get('removed', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {RED}- {world_str} (no longer a world){RESET}", file=output)
            print("", file=output)
        
        # Print possible state changes
        if diffs.get('possible_changes', {}).get('added') or diffs.get('possible_changes', {}).get('removed'):
            print(f"{BLUE}Possible State Changes:{RESET}", file=output)
            for state in diffs.get('possible_changes', {}).get('added', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {GREEN}+ {state_str} (now possible){RESET}", file=output)
            for state in diffs.get('possible_changes', {}).get('removed', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {RED}- {state_str} (now impossible){RESET}", file=output)
            print("", file=output)
        
        # Print atomic changes (verify/falsify)
        if diffs.get('atomic_changes'):
            atomic = diffs.get('atomic_changes', {})
            # Print verification changes
            if atomic.get('verify'):
                print(f"{BLUE}Verification Changes:{RESET}", file=output)
                for letter, state_changes in atomic['verify'].items():
                    print(f"  Letter {letter}:", file=output)
                    for state_str, change in state_changes.items():
                        if change['new']:
                            print(f"    {GREEN}+ {state_str} now verifies {letter}{RESET}", file=output)
                        else:
                            print(f"    {RED}- {state_str} no longer verifies {letter}{RESET}", file=output)
                print("", file=output)
            
            # Print falsification changes
            if atomic.get('falsify'):
                print(f"{BLUE}Falsification Changes:{RESET}", file=output)
                for letter, state_changes in atomic['falsify'].items():
                    print(f"  Letter {letter}:", file=output)
                    for state_str, change in state_changes.items():
                        if change['new']:
                            print(f"    {GREEN}+ {state_str} now falsifies {letter}{RESET}", file=output)
                        else:
                            print(f"    {RED}- {state_str} no longer falsifies {letter}{RESET}", file=output)
                print("", file=output)
        
        # Print parthood changes
        if diffs.get('parthood'):
            print(f"{BLUE}Part-of Relation Changes:{RESET}", file=output)
            for relation, change in diffs['parthood'].items():
                if change['new']:
                    print(f"  {GREEN}+ {relation}{RESET}", file=output)
                else:
                    print(f"  {RED}- {relation}{RESET}", file=output)
            print("", file=output)
    
    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and evaluate all sentence letters at that world."""
        BLUE = ""
        RESET = ""
        main_world = self.main_point["world"]
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N)}{RESET}\n",
            file=output,
        )

    def print_states(self, output=sys.__stdout__):
        """Print all states in the model with their binary representations and properties."""
        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )
        
        def format_state(bin_rep, state, color, label=""):
            label_str = f" ({label})" if label else ""
            use_colors = output is sys.__stdout__
            if use_colors:
                print(f"  {self.WHITE}{bin_rep} = {color}{state}{label_str}{self.RESET}", file=output)
            else:
                print(f"  {bin_rep} = {state}{label_str}", file=output)
        
        # Print formatted state space
        print("\nState Space:", file=output)
        for bit in self.all_states:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, self.COLORS["initial"])
            elif bit in self.z3_world_states:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.z3_possible_states:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")
    
    def extract_states(self) -> Dict[str, List[str]]:
        """Extract categorized states for output.
        
        Logos distinguishes between worlds, possible states, and impossible states.
        
        Returns:
            Dict with keys 'worlds', 'possible', 'impossible'
        """
        states = {"worlds": [], "possible": [], "impossible": []}
        
        if hasattr(self, 'z3_world_states') and self.z3_world_states:
            for state in self.z3_world_states:
                # Convert bit vector to state number
                if hasattr(state, 'as_long'):
                    states["worlds"].append(f"s{state.as_long()}")
                else:
                    states["worlds"].append(f"s{state}")
        
        if hasattr(self, 'z3_possible_states') and self.z3_possible_states:
            for state in self.z3_possible_states:
                # Only add if not already a world
                if state not in (self.z3_world_states if hasattr(self, 'z3_world_states') else []):
                    if hasattr(state, 'as_long'):
                        states["possible"].append(f"s{state.as_long()}")
                    else:
                        states["possible"].append(f"s{state}")
        
        # For impossible states, we need to check all states that aren't possible
        if hasattr(self, 'all_states') and self.all_states:
            # Convert possible states to integers for comparison
            possible_set = set()
            if hasattr(self, 'z3_possible_states') and self.z3_possible_states:
                for ps in self.z3_possible_states:
                    if hasattr(ps, 'as_long'):
                        possible_set.add(ps.as_long())
                    else:
                        possible_set.add(ps)
            
            for state in self.all_states:
                # Convert state to integer for comparison
                state_val = state.as_long() if hasattr(state, 'as_long') else state
                
                # Check if not possible and not null state
                if state_val not in possible_set and state_val != 0:
                    states["impossible"].append(f"s{state_val}")
        
        return states
    
    def extract_evaluation_world(self) -> Optional[str]:
        """Extract the main evaluation world.
        
        Returns:
            State name (e.g., 's3') or None if not set
        """
        if hasattr(self, 'z3_main_world') and self.z3_main_world is not None:
            if hasattr(self.z3_main_world, 'as_long'):
                return f"s{self.z3_main_world.as_long()}"
            else:
                return f"s{self.z3_main_world}"
        return None
    
    def extract_relations(self) -> Dict[str, Any]:
        """Extract relations between states.
        
        For Logos, this includes fusion/fission relations and compatibility.
        
        Returns:
            Dict containing various relations
        """
        relations = {}
        
        # Add any Logos-specific relations here
        # For now, return empty as relations are computed dynamically
        
        return relations
    
    def extract_propositions(self) -> Dict[str, Dict[str, bool]]:
        """Extract proposition truth values at worlds.
        
        Returns:
            Dict mapping propositions to their truth values at each world
        """
        propositions = {}
        
        if not hasattr(self, 'syntax') or not hasattr(self.syntax, 'propositions'):
            return propositions
        
        # Get world states
        worlds = []
        if hasattr(self, 'z3_world_states'):
            worlds = self.z3_world_states
        
        # Extract truth values for each proposition
        for prop_name, prop_obj in self.syntax.propositions.items():
            if hasattr(prop_obj, 'letter'):
                letter = prop_obj.letter
                propositions[letter] = {}
                
                for world in worlds:
                    # Get world number
                    if hasattr(world, 'as_long'):
                        world_num = world.as_long()
                    else:
                        world_num = world
                    
                    world_name = f"s{world_num}"
                    
                    if hasattr(prop_obj, 'truth_value_at'):
                        try:
                            # Logos propositions use truth_value_at
                            propositions[letter][world_name] = prop_obj.truth_value_at(world_num)
                        except:
                            # If evaluation fails, skip this world
                            pass
        
        return propositions
