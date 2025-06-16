"""
Shared semantic framework for the logos theory.

This module implements the core semantic foundation for all logos subtheories,
providing unified classes for semantics, propositions, and model structures.
"""

import z3
import sys
import time

from model_checker.model import (
    PropositionDefaults,
    SemanticDefaults,
    ModelDefaults,
    ModelConstraints,
)
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
    int_to_binary,
)
from model_checker import syntactic


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
        'max_time': 10000,
        'iterate': False,
        'iteration_timeout': 1.0,
        'iteration_attempts': 5,
        'expectation': None,
    }
    
    def __init__(self, combined_settings=None, operator_registry=None, **kwargs):
        # Ensure we have default settings
        if combined_settings is None:
            combined_settings = self.DEFAULT_EXAMPLE_SETTINGS.copy()
            combined_settings.update(kwargs)
        
        super().__init__(combined_settings)
        self.operator_registry = operator_registry
        
        # Define the Z3 primitives following default theory pattern
        self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(self.N), z3.BoolSort())
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
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point["world"])
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point["world"])
    
    def load_subtheories(self, subtheories=None):
        """Load specified subtheories."""
        if subtheories is None:
            subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual']
        if self.operator_registry:
            return self.operator_registry.load_subtheories(subtheories)
        return []

    def compatible(self, state_x, state_y):
        """Determines if the fusion of two states is possible."""
        return self.possible(self.fusion(state_x, state_y))

    def maximal(self, state_w):
        """Determines if a state is maximal with respect to compatibility."""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                z3.And(
                    self.possible(x),
                    self.compatible(state_w, x)
                ),
                self.is_part_of(x, state_w),
            ),
        )

    def is_world(self, state_w):
        """Determines if a state represents a possible world in the model."""
        return z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        )

    def true_at(self, sentence, eval_world):
        """Determines if a sentence is true at a given evaluation world.
        
        For atomic sentences (sentence_letters), it checks if there exists some state x 
        that is part of the evaluation world such that x verifies the sentence letter.
        
        For complex sentences, it delegates to the operator's true_at method with the 
        sentence's arguments and evaluation world.
        
        Args:
            sentence (Sentence): The sentence to evaluate
            eval_world (BitVecRef): The world at which to evaluate the sentence
            
        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is true at eval_world
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_world)

    def false_at(self, sentence, eval_world):
        """Determines if a sentence is false at a given evaluation world.
        
        For atomic sentences (sentence_letters), it checks if there exists some state x 
        that is part of the evaluation world such that x falsifies the sentence letter.
        
        For complex sentences, it delegates to the operator's false_at method with the 
        sentence's arguments and evaluation world.
        
        Args:
            sentence (Sentence): The sentence to evaluate
            eval_world (BitVecRef): The world at which to evaluate the sentence
            
        Returns:
            BoolRef: Z3 constraint expressing whether the sentence is false at eval_world
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_world)

    def extended_verify(self, state, sentence, eval_point):
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
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_point)
    
    def extended_falsify(self, state, sentence, eval_point):
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
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_point)

    def max_compatible_part(self, state_x, state_w, state_y):
        \"\"\"Determines if state_x is the maximal part of state_w compatible with state_y.
        
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
        \"\"\"
        z = z3.BitVec(\"max_part\", self.N)
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
        \"\"\"Determines if a state represents an alternative world resulting from
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
        \"\"\"
        z = z3.BitVec(\"alt_z\", self.N)
        return z3.And(
            self.is_world(state_u),
            self.is_part_of(state_y, state_u),
            Exists(z, z3.And(self.is_part_of(z, state_u), self.max_compatible_part(z, state_w, state_y))),
        )

    def calculate_alternative_worlds(self, verifiers, eval_point, model_structure):
        \"\"\"Calculates alternative worlds where a given state is imposed.
        
        This method identifies all alternative worlds generated by the verifiers
        and evaluation world. These alternative worlds are used in the semantics
        for counterfactual conditionals.
        
        Args:
            verifiers (set): Set of states verifying the antecedent
            eval_point (dict): The evaluation point containing the reference world
            model_structure (ModelStructure): The model being evaluated
            
        Returns:
            set: Set of alternative worlds where the antecedent is true
        \"\"\"
        is_alt = model_structure.semantics.is_alternative
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point[\"world\"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(is_alt(pw, ver, eval_world))
        }

    def product(self, set_A, set_B):
        \"\"\"Compute the set of all pairwise fusions between elements of two sets.
        
        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors
            
        Returns:
            set: A set containing the fusion of each element from set_A with each element from set_B
            
        Note:
            Uses bitwise OR as the fusion operation between elements
        \"\"\"
        product_set = set()
        for bit_a in set_A:
            for bit_b in set_B:
                from z3 import simplify
                bit_ab = simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
        \"\"\"Compute the union of two sets closed under pairwise fusion.
        
        Takes two sets and returns their union plus all possible fusions between
        their elements. The result is a set containing:
        1. All elements from both input sets
        2. All pairwise fusions between elements from the two sets
        
        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors
            
        Returns:
            set: The union of set_A and set_B closed under pairwise fusion
        \"\"\"
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))

    def closer_world(self, world_u, world_v, eval_point):
        \"\"\"Determines if world_u is closer than world_v to the evaluation world.
        
        This is a placeholder implementation for counterfactual semantics.
        A full implementation would define a similarity metric between worlds.
        
        Args:
            world_u (BitVecRef): First world to compare
            world_v (BitVecRef): Second world to compare  
            eval_point (dict): The evaluation point containing reference world
            
        Returns:
            BoolRef: Z3 constraint expressing whether world_u is closer than world_v
        \"\"\"
        # Placeholder: for now, just return False (no ordering)
        # A real implementation would define closeness based on similarity metrics
        return z3.BoolVal(False)


class LogosProposition(PropositionDefaults):
    """
    Proposition class with modular operator support.
    
    Represents propositional content in the logos semantic framework
    with support for all subtheory operators.
    """
    
    def __init__(self, sentence, model_structure, eval_world='main'):
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
    
    def proposition_constraints(self, sentence_letter):
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
            """Generate classical constraints following default theory pattern."""
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
                [x],
                z3.Not(z3.And(
                    semantics.verify(x, sentence_letter),
                    semantics.falsify(x, sentence_letter)
                )),
            )
            no_gap = ForAll(
                [x],
                z3.Implies(
                    semantics.possible(x),
                    z3.Or(
                        Exists(
                            [y],
                            z3.And(
                                semantics.verify(y, sentence_letter),
                                semantics.compatible(x, y)
                            ),
                        ),
                        Exists(
                            [y],
                            z3.And(
                                semantics.falsify(y, sentence_letter),
                                semantics.compatible(x, y)
                            ),
                        ),
                    ),
                ),
            )
            return [verifier_fusion_closure, falsifier_fusion_closure, no_glut, no_gap]

        def get_contingent_constraints():
            """Generate contingency constraints."""
            x, y = z3.BitVecs("ct_cont_x ct_cont_y", semantics.N)
            return [
                z3.Exists(
                    [x, y],
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    )
                )
            ]

        def get_non_null_constraints():
            """Generate non-null constraints."""
            return [
                z3.Not(semantics.verify(semantics.null_state, sentence_letter)),
                z3.Not(semantics.falsify(semantics.null_state, sentence_letter))
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
            """Generate non-empty constraints."""
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


class LogosModelStructure(ModelDefaults):
    """
    Model structure with modular operator support.
    
    Manages the overall semantic model structure for the logos theory
    with support for all subtheories and modular operator loading.
    """
    
    def __init__(self, semantics, proposition_class=None):
        super().__init__(semantics, proposition_class or LogosProposition)
        self.loaded_subtheories = []
    
    def load_subtheories(self, subtheories):
        """Load specified subtheories into the model."""
        self.loaded_subtheories.extend(subtheories)
        if hasattr(self.semantics, 'load_subtheories'):
            self.semantics.load_subtheories(subtheories)
    
    def get_available_operators(self):
        """Get all operators from loaded subtheories."""
        if hasattr(self.semantics, 'operator_registry'):
            return self.semantics.operator_registry.get_operators()
        return {}
    
    def print_model_info(self):
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