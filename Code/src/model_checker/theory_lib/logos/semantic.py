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
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)
    
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
                self.compatible(x, state_w),
                self.is_part_of(x, state_w),
            ),
        )

    def is_world(self, state_w):
        """Determines if a state represents a possible world in the model."""
        return z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        )

    def true_at(self, sentence, eval_point):
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
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]
        
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_point)

    def false_at(self, sentence, eval_point):
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
        """
        # Extract world from evaluation point
        eval_world = eval_point["world"]
        
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_point)

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
            Exists(z, z3.And(self.is_part_of(z, state_u), self.max_compatible_part(z, state_w, state_y))),
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

    def product(self, set_A, set_B):
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
                from z3 import simplify
                bit_ab = simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
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

    def find_proposition(self):
        """Computes the verifier and falsifier sets for this proposition.
        
        This method determines the sets of states that verify and falsify
        the proposition in the model. For atomic propositions, it uses the
        verify and falsify relations; for complex propositions, it delegates
        to the appropriate operator"s implementation.
        
        Returns:
            tuple: A pair (verifiers, falsifiers) containing the sets of
                 states that verify and falsify the proposition respectively
        """
        model = self.model_structure.z3_model
        semantics = self.semantics
        eval_world = self.eval_world
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            V = {
                state for state in self.model_structure.all_states
                if model.evaluate(semantics.verify(state, sentence_letter))
            }
            F = {
                state for state in self.model_structure.all_states
                if model.evaluate(semantics.falsify(state, sentence_letter))
            }
            return V, F
        if operator is not None:
            eval_point = {"world": eval_world}
            return operator.find_verifiers_and_falsifiers(*arguments, eval_point)
        raise ValueError(f"Their is no proposition for {self}.")

    def truth_value_at(self, eval_world):
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
            if z3_model.evaluate(semantics.is_part_of(verifier, eval_world)):
                ver_witness = verifier
                exists_verifier = True
                break
        for falsifier in self.falsifiers:
            if z3_model.evaluate(semantics.is_part_of(falsifier, eval_world)):
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

    def print_proposition(self, eval_point, indent_num, use_colors):
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

    def __repr__(self):
        """Return a string representation of the proposition.
        
        Returns a string showing the verifiers and falsifiers of the proposition
        in set notation. Only includes possible states unless print_impossible
        setting is enabled.
        
        Returns:
            str: A string of the form "< {verifiers}, {falsifiers} >" where each
                set contains the binary representations of the states
        """
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
    
    def __init__(self, model_constraints, settings):
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
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
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
        if diffs.get('worlds', {}).get('added') or diffs.get('worlds', {}).get('removed'):
            print(f"{BLUE}World Changes:{RESET}", file=output)
            for world in diffs['worlds'].get('added', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {GREEN}+ {world_str} (now a world){RESET}", file=output)
            for world in diffs['worlds'].get('removed', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {RED}- {world_str} (no longer a world){RESET}", file=output)
            print("", file=output)
        
        # Print possible state changes
        if diffs.get('possible_states', {}).get('added') or diffs.get('possible_states', {}).get('removed'):
            print(f"{BLUE}Possible State Changes:{RESET}", file=output)
            for state in diffs['possible_states'].get('added', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {GREEN}+ {state_str} (now possible){RESET}", file=output)
            for state in diffs['possible_states'].get('removed', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {RED}- {state_str} (now impossible){RESET}", file=output)
            print("", file=output)
        
        # Print verification changes
        if diffs.get('verify'):
            print(f"{BLUE}Verification Changes:{RESET}", file=output)
            for letter, state_changes in diffs['verify'].items():
                print(f"  Letter {letter}:", file=output)
                for state_str, change in state_changes.items():
                    if change['new']:
                        print(f"    {GREEN}+ {state_str} now verifies {letter}{RESET}", file=output)
                    else:
                        print(f"    {RED}- {state_str} no longer verifies {letter}{RESET}", file=output)
            print("", file=output)
        
        # Print falsification changes
        if diffs.get('falsify'):
            print(f"{BLUE}Falsification Changes:{RESET}", file=output)
            for letter, state_changes in diffs['falsify'].items():
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
        print("State Space:", file=output)
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