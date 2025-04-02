"""This module implements the core semantic framework for generating Z3 constraints
to be added to a Z3 solver, finding Z3 models, and using those models to construct
semantic models over which the sentences of the language may be evaluated and printed.
This module does not include semantic clauses for the operators included in the
language since this is covered by a dedicated module.

The module provides three main classes that together form the semantic foundation:

1. Semantics: Implements the semantic framework for modal logic, including:
   - State-based verification and falsification conditions
   - Compatibility and fusion relations between states
   - Truth conditions for complex formulas
   - Alternative world calculations for counterfactuals
   - Extended verification/falsification relations

2. Proposition: Represents propositional content in the exact truthmaker semantics, featuring:
   - Verifier and falsifier sets for atomic and complex propositions
   - Classical semantic constraints (no gaps/gluts)
   - Optional semantic constraints (contingency, disjointness, etc.)
   - Truth value evaluation at possible worlds
   - Pretty printing of propositions with truth values

3. ModelStructure: Manages the overall semantic model structure, providing:
   - Z3 solver integration for constraint satisfaction
   - State space construction and management
   - Model evaluation and verification
   - Visualization and printing utilities
   - Model persistence and serialization

The semantic framework uses a bit-vector representation for states, where:
- States are represented as bit vectors
- Possible worlds are maximal consistent states
- Verification and falsification are primitive relations on states
- Complex formulas are evaluated through recursive decomposition

Key Features:
- Exact truthmaker semantics with verifiers and falsifiers
- Support for classical and non-classical logics
- Flexible constraint system for semantic properties
- Efficient state space representation using bit vectors
- Comprehensive model checking and evaluation
- Rich visualization and debugging capabilities

Dependencies:
- z3-solver: For constraint solving and model construction
- sys: For system integration and I/O
- time: For performance monitoring

The module is designed to be used as part of a larger model checking framework,
providing the semantic foundation for modal logic analysis and verification.
"""

import z3
import sys
import time

# Try local imports first (for development)
try:
    from src.model_checker.model import (
        PropositionDefaults,
        SemanticDefaults,
        ModelDefaults,
        ModelConstraints,
    )
    from src.model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
        pretty_set_print,
        int_to_binary,
    )
    from src.model_checker import syntactic
except ImportError:
    # Fall back to installed package imports
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



##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class Semantics(SemanticDefaults):
    """Default semantics implementation for the modal logic system.
    
    This class provides a concrete implementation of the semantic framework
    for modal logic, including the definition of possible worlds, compatibility
    relations, truth and falsity conditions, and frame constraints.
    
    The semantics uses a bit-vector representation of states where worlds are
    represented as maximal possible states, and the verification and falsification
    of atomic propositions is defined in terms of state-based verifiers and falsifiers.
    
    Attributes:
        DEFAULT_EXAMPLE_SETTINGS (dict): Default settings for examples using this semantics
        verify (Function): Z3 function mapping states and atoms to truth values
        falsify (Function): Z3 function mapping states and atoms to falsity values
        possible (Function): Z3 function determining if a state is possible
        main_world (BitVec): The designated world for evaluation
        frame_constraints (list): Z3 constraints defining the logical frame
        premise_behavior (function): Function defining premise behavior for validity
        conclusion_behavior (function): Function defining conclusion behavior for validity
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'max_time' : 1,
        'iterate' : 1,
        'expectation' : None,
    }

    def __init__(self, settings):

        # Initialize the superclass to set defaults
        super().__init__(settings)

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(self.N), z3.BoolSort())
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world" : self.main_world
        }

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )
        is_main_world = self.is_world(self.main_world)

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point["world"])
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point["world"])

    def compatible(self, state_x, state_y):
        """Determines if the fusion of two states is possible.
        
        Args:
            state_x (BitVecRef): First state to check
            state_y (BitVecRef): Second state to check
            
        Returns:
            BoolRef: Z3 constraint expressing whether the fusion of state_x and
                    state_y is possible.
        """
        return self.possible(self.fusion(state_x, state_y))

    def maximal(self, state_w):
        """Determines if a state is maximal with respect to compatibility.
        
        A state is maximal if it includes all states that are compatible with it
        as parts. This is used to identify possible worlds in the model.
        
        Args:
            state_w (BitVecRef): The state to check for maximality
            
        Returns:
            BoolRef: Z3 constraint expressing whether state_w is maximal
        """
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, state_w),
                self.is_part_of(x, state_w),
            ),
        )

    def is_world(self, state_w):
        """Determines if a state represents a possible world in the model.
        
        A state is a possible world if it is both possible (according to the model's
        possibility function) and maximal (cannot be properly extended while maintaining
        compatibility).
        
        Args:
            state_w (BitVecRef): The state to check
            
        Returns:
            BoolRef: Z3 constraint expressing whether state_w is a possible world
        """
        return z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        )

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

    def calculate_outcome_worlds(self, verifiers, eval_point, model_structure):
        """Calculates outcome worlds that result from an imposition.
        
        This method identifies all worlds that result from imposing a state on
        the evaluation world using the primitive imposition relation rather than
        the alternative world relation where the later is defined. These worlds
        are used in the semantics of the imposition operator.
        
        Args:
            verifiers (set): Set of states being imposed
            eval_point (dict): The evaluation point containing the reference world
            model_structure (ModelStructure): The model being evaluated
            
        Returns:
            set: Set of outcome worlds resulting from the imposition
        """
        imposition = model_structure.semantics.imposition
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.world_states
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(imposition(ver, eval_world, pw))
        }


class Proposition(PropositionDefaults):
    """Concrete implementation of propositions for the default semantic theory.
    
    This class represents the propositional content of sentences in the model,
    defining how they are verified and falsified by states. It implements the
    exact-truthmaker semantics approach where each proposition is identified
    with a pair of sets: verifiers (states that make it true) and falsifiers
    (states that make it false).
    
    The class handles constraint generation for atomic propositions and
    provides methods for testing truth values at evaluation points.
    
    Attributes:
        verifiers (set): States that verify the proposition
        falsifiers (set): States that falsify the proposition
        eval_world: The world at which the proposition is being evaluated
    """

    def __init__(self, sentence, model_structure, eval_world='main'):
        """Initialize a Proposition instance.

        Args:
            sentence (Sentence): The sentence whose proposition is being represented
            model_structure (ModelStructure): The model structure containing semantic definitions
            eval_world (str|BitVecRef, optional): The world at which to evaluate the proposition.
                If 'main', uses the model's main world. Defaults to 'main'.
        """

        super().__init__(sentence, model_structure)

        self.eval_world = model_structure.main_point["world"] if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
        
    def __eq__(self, other):
        """Compare two propositions for equality.
        
        Two propositions are considered equal if they have the same verifiers,
        falsifiers, and name.
        
        Args:
            other (Proposition): The proposition to compare with
            
        Returns:
            bool: True if the propositions are equal, False otherwise
        """
        return (
            self.verifiers == other.verifiers
            and self.falsifiers == other.falsifiers
            and self.name == other.name
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

    def proposition_constraints(self, sentence_letter):
        """Generates Z3 constraints for a sentence letter based on semantic settings.

        This method generates constraints that govern the behavior of atomic propositions
        in the model. It includes:
        - Classical constraints (preventing truth value gaps and gluts)
        - Optional constraints based on settings:
            - non-null: Prevents null states from verifying/falsifying
            - contingent: Ensures propositions have both possible verifiers and falsifiers
            - disjoint: Ensures atomic propositions have disjoint verifiers/falsifiers

        Returns:
            list: A list of Z3 constraints for the sentence letter
        """
        semantics = self.semantics

        def get_classical_constraints():
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", semantics.N)
            """Generate constraints that enforce classical behavior by ruling out
            truth value gaps and gluts.
            
            These constraints ensure:
            1. If two states verify a proposition, their fusion also verifies it
            2. If two states falsify a proposition, their fusion also falsifies it  
            3. No state can both verify and falsify a proposition (no gluts)
            4. Every possible state must be compatible with either a verifier or falsifier (no gaps)
            """
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

        def get_non_null_constraints():
            """The non_null constraints prevent null states (empty states) from being verifiers
            or falsifiers. These constraints are important to prevent trivial satisfaction of
            the disjoint constraints, though they are already entailed by the contingent constraints
            when those are enabled."""
            return [
                z3.Not(semantics.verify(0, sentence_letter)),
                z3.Not(semantics.falsify(0, sentence_letter)),
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

        def get_disjoint_constraints():
            """The disjoint constraints ensure that atomic propositions have
            non-overlapping verifiers and falsifiers. This includes non-null
            constraints to prevent empty states from being verifiers or falsifiers."""
            x, y, z = z3.BitVecs("dj_prop_x dj_prop_y dj_prop_z", semantics.N)
            disjoint_constraints = []
            for other_letter in self.sentence_letters:
                if other_letter is not sentence_letter:
                    other_disjoint_atom = ForAll(
                        [x, y],
                        z3.Implies(
                            z3.And(
                                semantics.non_null_part_of(x, y),
                                z3.Or(
                                    semantics.verify(y, sentence_letter),
                                    semantics.falsify(y, sentence_letter),
                                ),
                            ),
                            ForAll(
                                z,
                                z3.Implies(
                                    z3.Or(
                                        semantics.verify(z, other_letter),
                                        semantics.falsify(z, other_letter)
                                    ),
                                    z3.Not(semantics.is_part_of(x, z)),
                                )
                            )
                        )
                    )
                    disjoint_constraints.append(other_disjoint_atom)
            return disjoint_constraints

        # Collect constraints
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
        to the appropriate operator's implementation.
        
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
            return operator.find_verifiers_and_falsifiers(*arguments, eval_world)
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


class ModelStructure(ModelDefaults):
    """Constructs a semantic model from a Z3 model over which to interpret the language.

    This class represents the core model structure used for semantic evaluation,
    including the state space, possible worlds, and evaluation functions. It manages
    the Z3 solver instance and provides methods for model construction, evaluation,
    and visualization.

    Attributes:
        main_world (BitVecRef): The designated world for evaluation
        z3_main_world (BitVecRef): Z3 model value for the main world
        z3_possible_states (list): List of all possible states in the Z3 model
        z3_world_states (list): List of all world states in the Z3 model
        main_point (dict): Dictionary containing evaluation context with the main world

    The class provides functionality for:
    - Initializing and managing the model structure
    - Evaluating formulas in the model
    - Printing model information and evaluation results
    - Saving model data to files
    - Handling model constraints and satisfiability checking
    """

    def __init__(self, model_constraints, settings):
        """Initialize ModelStructure with model constraints and optional max time.
        
        Args:
            model_constraints: ModelConstraints object containing all constraints
            max_time: Maximum time in seconds to allow for solving. Defaults to 1.
        """
        if not isinstance(model_constraints, ModelConstraints):
            raise TypeError(
                f"Expected model_constraints to be a ModelConstraints object, got {type(model_constraints)}. "
                "Make sure you're passing the correct model_constraints object."
            )

        super().__init__(model_constraints, settings)

        # Get main point
        self.main_world = self.main_point["world"]

        # Initialize Z3 model values
        self.z3_main_world = None
        self.z3_possible_states = None
        self.z3_world_states = None 

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

    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and evaluate all sentence letters at that world.
        
        Displays the binary representation of the evaluation world and indicates which
        atomic sentences (sentence letters) are true or false at that world in the model.
        
        Args:
            output (file object, optional): Output stream to write to. Defaults to sys.stdout.
        """
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
        """Print all states in the model with their binary representations and properties.
        
        Prints each state in the model along with its binary representation and additional
        properties like whether it's a world state, possible state, or impossible state.
        States are color-coded when printing to stdout:
        - World states are marked with "(world)"
        - Possible states are highlighted
        - Impossible states are shown only if print_impossible setting is True
        - The null state (0) is specially formatted
        
        Args:
            output (file object, optional): Output stream to write to. Defaults to sys.stdout.
        """

        def binary_bitvector(bit):
            """Convert a Z3 BitVec to its binary string representation.
            
            For BitVecs whose size is not divisible by 4, returns the raw sexpr.
            For BitVecs whose size is divisible by 4, converts the hexadecimal
            representation to binary format.
            
            Args:
                bit (BitVecRef): The Z3 BitVec to convert
                
            Returns:
                str: Binary string representation of the BitVec
            """
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )
        
        def format_state(bin_rep, state, color, label=""):
            """Format and print a state with optional label and color formatting.
            
            Args:
                bin_rep (str): Binary representation of the state
                state (str): State representation
                color (str): ANSI color code for formatting
                label (str, optional): Additional label to append to state. Defaults to empty string.
                
            Returns:
                None: Prints the formatted state to the specified output
            """
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
        self.print_info(model_status, default_settings, example_name, theory_name, output)
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
        if self.timeout:
            print(f"TIMEOUT: {self.timeout}")
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
            return
        self.print_all(default_settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(self, example_name, theory_name, include_constraints, output):
        """Save the model details to a file.
        
        Writes a complete representation of the model to the specified file, including
        evaluation results, state space, and optionally the model constraints.
        
        Args:
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            include_constraints (bool): Whether to include model constraints in output
            output (TextIO): File object to write the model details to
        """
        constraints = self.model_constraints.all_constraints
        self.print_all(example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
