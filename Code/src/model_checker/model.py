"""Core model checking functionality for modal logic systems.

This module provides the foundational classes and infrastructure for building and analyzing
modal logic models. It implements the core semantic operations, proposition handling,
constraint generation, and model checking capabilities used across different modal logics.

Key Components:
    SemanticDefaults: Base class for semantic operations in modal logics
        - Implements core operations like fusion, part-of relations
        - Provides set-theoretic operations for modal semantics
        - Handles bit vector representations of states

    PropositionDefaults: Base class for proposition representation
        - Links sentences to their semantic interpretation
        - Manages truth value calculation and evaluation
        - Handles atomic and complex propositions

    ModelConstraints: Links syntax to semantic constraints
        - Generates Z3 constraints from logical content
        - Manages operator instantiation with semantics
        - Bridges between syntax and model structure

    ModelDefaults: Core model structure and solving capabilities
        - Handles Z3 solver interaction and constraint solving
        - Manages model interpretation and result analysis
        - Provides visualization and output formatting

The module uses Z3 for constraint solving and implements a bit-vector based
approach to state representation. It supports various modal logics through
extensible base classes that can be customized for specific theories.

Example Usage:
    # Create model constraints from premises and conclusions
    constraints = ModelConstraints(settings, syntax, semantics, proposition_class)

    # Build and solve the model
    model = ModelDefaults(constraints, settings)

    # Analyze and display results
    model.print_info(model_status, default_settings, example_name, theory_name, output)

Dependencies:
    - z3-solver: For constraint solving and model generation
    - model_checker.utils: Utility functions and shared resources

Note:
    This module serves as the foundation for implementing specific modal logic
    theories. Each theory should extend these base classes to implement its
    particular semantic interpretation and constraints.
"""


import sys
from contextlib import redirect_stdout
import time
from functools import reduce
from string import Template
from z3 import (
    And,
    ArrayRef,
    BitVecSort,
    BitVecVal,
    EmptySet,
    ExprRef,
    IntVal,
    IsMember,
    Not,
    SetAdd,
    Solver,
    sat,
    simplify,
)

# Try local imports first (for development)
try:
    from src.model_checker.utils import (
        not_implemented_string,
    )
except ImportError:
    # Fall back to installed package imports
    from model_checker.utils import (
        not_implemented_string,
    )

inputs_template = Template(
'''Z3 run time: ${z3_model_runtime} seconds
"""

################
### SETTINGS ###
################

settings = ${settings}


###############
### EXAMPLE ###
###############

# input sentences
premises = ${premises}
conclusions = ${conclusions}


#########################################
### GENERATE Z3 CONSTRAINTS AND PRINT ###
#########################################

### NOTE: run below for individual tests

model_structure = make_model_for(
    settings,
    premises,
    conclusions,
    Semantics,
    Proposition,
    operators,
)
model_structure.print_all()
'''
)

class SemanticDefaults:
    """Base class providing fundamental semantic operations for a modal logic system.
    
    This class defines the core semantic functionality used across all theories in the
    model checker. It provides methods for working with bit vectors representing states,
    set operations, and foundational semantic relations like part-of and fusion.
    
    Each theory should extend this class to implement its specific semantics for modal
    operators and provide concrete implementations of the truth/falsity conditions.
    
    Attributes:
        name (str): Name of the semantics implementation class
        N (int): Bit-width for state representation (if provided in settings)
        full_bit (BitVecVal): Maximum possible state (if N is provided)
        null_bit (BitVecVal): Empty state (if N is provided)
        all_states (list): All possible bit vectors of width N (if N is provided)
        M (int): Number of times for temporal semantics (if provided in settings)
        all_times (list): All possible time points (if M is provided)
        main_point (dict): The primary evaluation point for the model
        frame_constraints (list): Z3 constraints defining the logical frame
        premise_behavior (str): How premises should be handled for validity
        conclusion_behavior (str): How conclusions should be handled for validity
    """

    def __init__(self, combined_settings):

        # Store the name
        self.name = self.__class__.__name__

        # Define all states and top and bottom if N is specified
        if 'N' in combined_settings.keys():
            self.N = combined_settings['N']
            max_value = (1 << self.N) - 1 # NOTE: faster than 2**self.N - 1
            self.full_state = BitVecVal(max_value, self.N)
            self.null_state = BitVecVal(0, self.N)
            self.all_states = [BitVecVal(i, self.N) for i in range(1 << self.N)]

        # Define all times between 0 and M inclusive
        if 'M' in combined_settings.keys():
            self.M = combined_settings['M']
            self.all_times = [IntVal(i) for i in range(self.M)]

        # Define main_point
        self.main_point = None

        # Define the frame constraints
        self.frame_constraints = None

        # Define invalidity conditions
        self.premise_behavior = None
        self.conclusion_behavior = None

    def fusion(self, bit_s, bit_t):
        """Performs the fusion operation on two bit vectors.
        
        In most modal logics, fusion corresponds to combining or merging states.
        This implementation uses bitwise OR as the default fusion operation,
        but specific theories might override with different implementations.
        
        Args:
            bit_s (BitVecRef): The first bit vector
            bit_t (BitVecRef): The second bit vector
            
        Returns:
            BitVecRef: The result of fusing the two input bit vectors
        """
        return bit_s | bit_t

    def z3_set(self, python_set, N):
        """Convert a Python set to a Z3 set representation with specified bit-width.
        
        Args:
            python_set (set): The Python set to convert
            N (int): The bit-width for the resulting Z3 set
            
        Returns:
            z3.SetRef: A Z3 set containing the elements from the input Python set
            
        Note:
            The resulting Z3 set will have elements of bit-width N
        """
        z3_set = EmptySet(BitVecSort(N))
        for elem in python_set:
            z3_set = SetAdd(z3_set, elem)
        return z3_set

    def z3_set_to_python_set(self, z3_set, domain):
        """Convert a Z3 set to a Python set by checking membership of domain elements.
        
        Args:
            z3_set (z3.SetRef): The Z3 set to convert
            domain (list): Collection of elements to check for membership
            
        Returns:
            set: A Python set containing elements from domain that are members of z3_set
            
        Note:
            Uses Z3's IsMember and simplify functions to determine set membership
        """
        python_set = set()
        for elem in domain:
            if bool(simplify(IsMember(elem, z3_set))):
                python_set.add(elem)
        return python_set

    def total_fusion(self, set_P):
        """Compute the fusion of all elements in a set of bit vectors.
        
        Takes a set of bit vectors and returns their total fusion by applying
        the fusion operation (bitwise OR) to all elements in the set.
        
        Args:
            set_P: A set or Z3 array of bit vectors to be fused
            
        Returns:
            BitVecRef: The result of fusing all elements in the input set
            
        Note:
            If set_P is empty, returns the null bit vector (all zeros)
        """
        if isinstance(set_P, ArrayRef):
            set_P = self.z3_set_to_python_set(set_P, self.all_states)
        return reduce(self.fusion, list(set_P))

    def is_part_of(self, bit_s, bit_t):
        """Checks if one bit vector is part of another where one bit vector is
        a part of another if their fusion is identical to the second bit vector.
        
        Args:
            bit_s (BitVecRef): The potential part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is part of bit_t
        """
        return self.fusion(bit_s, bit_t) == bit_t

    def is_proper_part_of(self, bit_s, bit_t):
        """Checks if one bit vector is a proper part of another.
        
        A bit vector is a proper part of another if it is a part of it but not equal to it.
        
        Args:
            bit_s (BitVecRef): The potential proper part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is a proper part of bit_t
        """
        return And(self.is_part_of(bit_s, bit_t), bit_s != bit_t)

    def non_null_part_of(self, bit_s, bit_t):
        """Checks if a bit vector is a non-null part of another bit vector.
        
        Args:
            bit_s (BitVecRef): The potential non-null part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is both:
                    1. Not the null state (not zero)
                    2. A part of bit_t
        """
        return And(Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

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
                bit_ab = simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
        """Compute the union of two sets closed under pairwise fusion.
        
        Takes two sets and returns their union plus all possible fusions between
        their elements. The result is a set containing:
        1. All elements from both input sets
        2. All pairwise fusions between elements of the input sets
        
        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors
            
        Returns:
            set: The union of set_A and set_B closed under pairwise fusion
        """
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))


class PropositionDefaults:
    """Base class for representing propositions in a logical system.
    
    This abstract class provides the foundation for representing propositional content
    in a model. Subclasses must implement the actual semantic behavior specific to each
    logical theory.
    
    Propositions link sentences to their semantic interpretation in a model. They
    contain the necessary methods for calculating truth values and managing verification
    and falsification conditions.
    
    Attributes:
        sentence (Sentence): The sentence object this proposition represents
        model_structure (ModelStructure): The model in which this proposition is interpreted
        N (int): Bit-width for state representation
        main_point (dict): The primary evaluation point for the model
        name (str): The string representation of the sentence
        operator (Operator): The main logical operator of the sentence (None for atoms)
        arguments (list): Sentence objects for the operator's arguments (None for atoms)
        sentence_letter (ExprRef): For atomic sentences, their Z3 representation (None for complex sentences)
        model_constraints (ModelConstraints): Constraints governing the model
        semantics (Semantics): The semantics object used for evaluation
        sentence_letters (list): All atomic sentence letters in the argument
        settings (dict): Model settings
    """

    def __init__(self, sentence, model_structure):

        # Raise error if instantiated directly instead of as a bare class
        if self.__class__ == PropositionDefaults:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))

        # Validate model_structure
        if not hasattr(model_structure, 'semantics'):
            raise TypeError(
                f"Expected model_structure to be a ModelStructure object, got {type(model_structure)}. "
                "Make sure you're passing the correct model_structure object when creating propositions."
            )

        # Store inputs
        self.sentence = sentence
        self.model_structure = model_structure

        # Store values from model_structure
        self.N = self.model_structure.semantics.N
        self.main_point = self.model_structure.main_point

        # Store values from sentence
        self.name = self.sentence.name
        self.operator = self.sentence.operator
        self.arguments = self.sentence.arguments
        self.sentence_letter = self.sentence.sentence_letter

        # Store values from model_constraints
        self.model_constraints = self.model_structure.model_constraints
        self.semantics = self.model_constraints.semantics
        self.sentence_letters = self.model_constraints.sentence_letters
        self.settings = self.model_constraints.settings

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, PropositionDefaults):
            return self.name == other.name
        return False

    def set_colors(self, name, indent_num, truth_value, world_state, use_colors):
        if not use_colors:
            VOID = ""
            return VOID, VOID, VOID
        RED, GREEN, RESET = "\033[31m", "\033[32m", "\033[0m" 
        FULL, PART = "\033[37m", "\033[33m"
        if indent_num == 1:
            FULL, PART = (GREEN, GREEN) if truth_value else (RED, RED)
            if truth_value is None:
                print(
                    f"\n{RED}WARNING:{RESET}"
                    f"{name} is neither true nor false at {world_state}.\n"
                )
        return RESET, FULL, PART


class ModelConstraints:
    """Links syntactic structures to semantic constraints for model generation.
    
    This class connects the syntactic representation of an argument (premises and conclusions)
    with a specific semantics implementation to generate constraints for model finding.
    It serves as the bridge between syntax and semantics in the model checking process.
    
    The class is responsible for instantiating operators with the appropriate semantics,
    generating Z3 constraints that represent the logical content of sentences, and
    managing the settings that govern the model generation process.
    
    Attributes:
        settings (dict): Configuration settings for model generation
        syntax (Syntax): The syntactic representation of the argument
        semantics (Semantics): The semantic theory being used
        proposition_class (class): The class used to create propositions
        sentences (dict): All sentences in the argument
        sentence_letters (list): All atomic sentence letters in the argument
        operators (dict): Instantiated operator objects with the selected semantics
        premises (list): Sentence objects for premises
        conclusions (list): Sentence objects for conclusions

    Takes semantics and proposition_class as arguments to build generate
    and storing all Z3 constraints. This class is passed to ModelStructure."""

    def __init__(
        self,
        settings,
        syntax,
        semantics,
        proposition_class,
    ):

        # Store inputs
        self.syntax = syntax
        self.semantics = semantics
        self.proposition_class = proposition_class
        self.settings = settings
        # self.old_z3_models = None

        # Store syntax values
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions

        self.sentence_letters = self._load_sentence_letters()

        # Store operator dictionary
        self.operators = self.copy_dictionary(self.syntax.operator_collection)

        # use semantics to recursively update all derived_objects
        self.instantiate(self.premises + self.conclusions)

        # Use semantics to generate and store Z3 constraints
        self.frame_constraints = self.semantics.frame_constraints
        self.model_constraints = [
            constraint
            for sentence_letter in self.sentence_letters
            for constraint in self.proposition_class.proposition_constraints(
                self,
                sentence_letter,
            )
        ]
        self.premise_constraints = [
            self.semantics.premise_behavior(premise)
            for premise in self.premises
        ]
        self.conclusion_constraints = [
            self.semantics.conclusion_behavior(conclusion)
            for conclusion in self.conclusions
        ]
        self.all_constraints = (
            self.frame_constraints
            + self.model_constraints
            + self.premise_constraints
            + self.conclusion_constraints
        )

    def __str__(self):
        """Returns a string representation of the ModelConstraints object.
        
        This method is useful when using the model-checker programmatically in Python scripts.
        It provides a concise description of the ModelConstraints object by showing its
        premises and conclusions.
        
        Returns:
            str: A string in the format "ModelConstraints for premises [p1, p2, ...] and conclusions [c1, c2, ...]"
        """
        premises = list(self.syntax.premises)
        conclusions = list(self.syntax.conclusions)
        return f"ModelConstraints for premises {premises} and conclusions {conclusions}"

    # def _store_z3_model(self, old_z3_model):
    #     if self.old_z3_models is None:
    #         self.old_z3_models = [old_z3_model]
    #     else:
    #         self.old_z3_models.append(old_z3_model)

    def _load_sentence_letters(self):
        """Extracts and validates atomic sentence letters from the syntax object.
        
        Unpacks each sentence letter from the syntax object and verifies it is a valid
        Z3 expression (ExprRef type). Returns a list of all atomic sentence letters
        used in the argument.
        
        Returns:
            list: A list of Z3 ExprRef objects representing atomic sentence letters
            
        Raises:
            TypeError: If any sentence letter is not a valid Z3 ExprRef object
        """
        sentence_letters = []
        for packed_letter in self.syntax.sentence_letters:
            unpacked_letter = packed_letter.sentence_letter
            if not isinstance(unpacked_letter, ExprRef):
                raise TypeError("The sentence letter {letter} is not of type z3.ExprRef")
            sentence_letters.append(unpacked_letter) 
        return sentence_letters

    def copy_dictionary(self, operator_collection):
        """Creates a new dictionary by copying operators from the operator collection.
        
        Takes an operator collection and creates a new dictionary where each operator
        is instantiated with the current semantics. This ensures each operator has
        its own instance with the appropriate semantic interpretation.
        
        Args:
            operator_collection (dict): Dictionary mapping operator names to operator classes
            
        Returns:
            dict: New dictionary with instantiated operator objects using current semantics
        """
        return {
            op_name : op_class(self.semantics)
            for (op_name, op_class) in operator_collection.items()
        }

    def instantiate(self, sentences):
        """Recursively updates each sentence in the given list with its proposition.
        
        This method traverses through the sentence tree and updates each sentence object
        with its corresponding proposition based on the current model constraints and
        semantics. This process links the syntactic structure with its semantic
        interpretation.
        
        Args:
            sentences (list): A list of Sentence objects to be updated
            
        Returns:
            list: The input sentences, now updated with their propositions
            
        Note:
            This method should only be called after a valid Z3 model has been found.
        """
        for sent_obj in sentences:
            if sent_obj.arguments:
                self.instantiate(sent_obj.arguments)
            sent_obj.update_objects(self)

    def print_enumerate(self, output=sys.__stdout__):
        """Prints the premises and conclusions with enumerated numbering.
        
        Formats and displays the premises and conclusions with sequential numbering.
        Premises are numbered starting from 1, and conclusions continue the numbering
        sequence after premises.
        
        Args:
            output (file): Output stream to write to (defaults to sys.stdout)
            
        Example output:
            Premises:
            1. A
            2. B
            
            Conclusion:
            3. C
        """
        premises = self.syntax.premises
        conclusions = self.syntax.conclusions
        start_con_num = len(premises) + 1
        if conclusions:
            if len(premises) < 2:
                print("Premise:", file=output)
            else:
                print("Premises:", file=output)
            for index, sent in enumerate(premises, start=1):
                print(f"{index}. {sent}", file=output)
        if conclusions:
            if len(conclusions) < 2:
                print("\nConclusion:", file=output)
            else:
                print("\nConclusions:", file=output)
            for index, sent in enumerate(conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)


# TODO: expose elements that need to change to accommodate bimodal logic
class ModelDefaults:
    """Base class for model structures that handle Z3 solving and result interpretation.
    
    This class provides the core functionality for constraint solving and model generation.
    It interfaces with the Z3 solver to find models that satisfy the logical constraints
    derived from premises and conclusions, and provides methods for interpreting and
    displaying the results.
    
    Specific theories extend this class to implement theory-specific model structures
    with additional functionality and visualization capabilities.
    
    Attributes:
        model_constraints (ModelConstraints): The constraints to satisfy in the model
        settings (dict): Configuration settings for model generation
        semantics (Semantics): The semantic theory in use
        result (tuple): Contains solver results after solving
        solved (bool): Whether the model has been successfully solved
        timeout (bool): Whether solving timed out
        satisfiable (bool): Whether the constraints are satisfiable
        z3_model (Z3 model): The Z3 model object (if satisfiable)
        solver (Z3 Solver): The Z3 solver instance
        main_point (dict): The primary evaluation point for the model
    """

    def __init__(self, model_constraints, settings):
        # Define ANSI color codes
        self.COLORS = {
            "default": "\033[37m",  # WHITE
            "world": "\033[34m",    # BLUE
            "possible": "\033[36m", # CYAN
            "impossible": "\033[35m", # MAGENTA
            "initial": "\033[33m",  # YELLOW
        }
        self.RESET = "\033[0m"
        self.WHITE = self.COLORS["default"]

        # TODO: is this still needed?
        self.constraint_dict = {} # hopefully temporary, for unsat_core

        # Store arguments
        self.model_constraints = model_constraints
        self.settings = settings
        self.max_time = self.settings["max_time"]
        self.expectation = self.settings["expectation"]

        # Store from model_constraints.semantics
        self.semantics = self.model_constraints.semantics
        self.main_point = self.semantics.main_point
        self.all_states = self.semantics.all_states
        self.N = self.semantics.N

        # Store from model_constraint.syntax
        self.syntax = self.model_constraints.syntax
        self.start_time = self.syntax.start_time
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions
        self.sentence_letters = self.syntax.sentence_letters

        # Store from model_constraint
        self.proposition_class = self.model_constraints.proposition_class
        self.settings = self.model_constraints.settings

        # Initialize Z3 attributes
        self.solver = None # TODO: still needed?
        self.timeout = None
        self.z3_model = None
        self.unsat_core = None
        self.z3_model_status = None
        self.z3_model_runtime = None

        # Solve Z3 constraints and store results
        solver_results = self.solve(self.model_constraints, self.max_time)
        self._process_solver_results(solver_results)

        # Exit early if no valid model was found
        if self.timeout or self.z3_model is None:
            return

        # NOTE: this was moved to BuildExample to 
        # Recursively update propositions
        # for sent in self.premises + self.conclusions:
        #     print(f"SENTENCE {sent}; TYPE {type(sent)}")
        # self.interpret(self.premises + self.conclusions)

    def _process_solver_results(self, solver_results):
        """Process and store the results from the Z3 solver.
        
        Takes the raw solver results and updates the model's state attributes including
        timeout status, model/unsat core, model status, and runtime.
        
        Args:
            solver_results (tuple): Contains:
                - timeout (bool): Whether solver timed out
                - z3_model (Z3Model/list): Either a satisfying model or unsat core
                - z3_model_status (bool): Whether constraints were satisfiable
                - z3_model_runtime (float): Time taken by solver in seconds
        """
        timeout, z3_model, z3_model_status, z3_model_runtime = solver_results
        
        self.timeout = timeout
        self.z3_model_status = z3_model_status
        self.z3_model_runtime = z3_model_runtime
        
        # Store either the model or unsat core based on status
        if z3_model_status:
            self.z3_model = z3_model
        else:
            self.unsat_core = z3_model

    def _setup_solver(self, model_constraints):
        """Initialize Z3 solver and add all model constraints with tracking labels.
        
        Sets up a new Z3 solver instance and adds all constraints from the model_constraints
        object, organizing them into labeled groups (frame, model, premises, conclusions).
        Each constraint is tracked with a unique identifier for unsat core extraction.
        
        Args:
            model_constraints (ModelConstraints): Object containing all logical constraints
                                                to be added to the solver
                                                
        Returns:
            z3.Solver: Initialized solver with all constraints added and tracked
            
        Note:
            Constraints are added using assert_and_track() to enable unsat core generation
            when constraints are unsatisfiable.
        """
        solver = Solver()
        constraint_groups = [
            (model_constraints.frame_constraints, "frame"),
            (model_constraints.model_constraints, "model"), 
            (model_constraints.premise_constraints, "premises"),
            (model_constraints.conclusion_constraints, "conclusions")
        ]
        
        for constraints, group_name in constraint_groups:
            for ix, constraint in enumerate(constraints):
                c_id = f"{group_name}{ix+1}"
                solver.assert_and_track(constraint, c_id)
                self.constraint_dict[c_id] = constraint
                
        return solver

    def _create_result(self, is_timeout, model_or_core, is_satisfiable, start_time):
        """Creates a standardized tuple containing solver results with runtime.
        
        Args:
            is_timeout (bool): Whether the solver timed out
            model_or_core (Z3Model/list): Either a satisfying model or unsat core
            is_satisfiable (bool): Whether the constraints were satisfiable
            start_time (float): When solving started (used to calculate runtime)
            
        Returns:
            tuple: Contains (is_timeout, model_or_core, is_satisfiable, runtime)
            where runtime is rounded to 4 decimal places
        """
        runtime = round(time.time() - start_time, 4)
        return is_timeout, model_or_core, is_satisfiable, runtime

    def solve(self, model_constraints, max_time):
        """Uses the Z3 solver to find a model satisfying the given constraints.
        
        This method sets up the Z3 solver with all the constraints derived from
        the premises, conclusions, and frame conditions, then attempts to find
        a satisfying assignment that represents a valid model.
        
        Args:
            model_constraints (ModelConstraints): The logical constraints to solve
            max_time (int): Maximum solving time in milliseconds (0 for unlimited)
            
        Returns:
            tuple: Contains result information (timeout flag, model/core, satisfiability)
            
        Notes:
            - If the constraints are unsatisfiable, returns the unsatisfiable core
            - If solving times out, sets the timeout flag but still returns partial results
        """

        try:
            self.solver = self._setup_solver(model_constraints)

            # Set timeout and solve
            self.solver.set("timeout", int(max_time * 1000))
            start_time = time.time()
            result = self.solver.check()
            
            # Handle different solver outcomes
            if result == sat:
                return self._create_result(False, self.solver.model(), True, start_time)
            
            if self.solver.reason_unknown() == "timeout":
                return self._create_result(True, None, False, start_time)
            
            return self._create_result(False, self.solver.unsat_core(), False, start_time)
            
        except RuntimeError as e:
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, None, False, None
    
    def re_solve(self):
        """Re-solve the existing model constraints with the current solver state.
        
        Attempts to find a new solution using the existing solver instance and its
        constraints. This is useful when additional constraints have been added to
        the solver after initial solving.
        
        Returns:
            tuple: Contains (is_timeout, model_or_core, is_satisfiable, runtime) where:
                - is_timeout (bool): Whether solver timed out
                - model_or_core: Either a Z3 model (if satisfiable) or unsat core (if unsatisfiable)
                - is_satisfiable (bool): Whether constraints were satisfiable
                - runtime (float): Time taken by solver in seconds
                
        Raises:
            RuntimeError: If solver encounters an error during execution
            AssertionError: If solver instance doesn't exist
        """

        try:
            assert self.solver is not None
            # Re-apply timeout setting
            self.solver.set("timeout", int(self.max_time * 1000))
            
            start_time = time.time()
            result = self.solver.check()
            
            # Handle different solver outcomes
            if result == sat:
                return self._create_result(False, self.solver.model(), True, start_time)
            
            if self.solver.reason_unknown() == "timeout":
                return self._create_result(True, None, False, start_time)
            
            return self._create_result(False, self.solver.unsat_core(), False, start_time)
            
        except RuntimeError as e:
            print(f"An error occurred while running `re_solve()`: {e}")
            return True, None, False, None

    def check_result(self):
        """Checks if the model's result matches the expected outcome.
        
        Compares the actual model status (satisfiable/unsatisfiable) against the
        expected outcome specified in the settings. This is used to verify if
        the model checker produced the anticipated result.
        
        Returns:
            bool: True if the model status matches expectations, False otherwise
        """
        return self.z3_model_status == self.settings["expectation"]

    def interpret(self, sentences):
        """Recursively updates sentences with their semantic interpretations in the model.
        
        For each sentence in the input list, creates and attaches a proposition object
        that represents its semantic interpretation in the current model. This process
        recursively handles complex sentences by first interpreting their subformulas.
        
        Args:
            sentences (list): List of Sentence objects to be interpreted
            
        Returns:
            None
            
        Note:
            - This method should only be called after a valid Z3 model has been found
            - Modifies the sentence objects in-place by setting their proposition attribute
            - Skips sentences that already have an attached proposition
        """
        if not self.z3_model:
            return

        for sent_obj in sentences:
            if sent_obj.proposition is not None:
                continue
            if sent_obj.arguments:
                self.interpret(sent_obj.arguments)
            sent_obj.update_proposition(self)

    def print_grouped_constraints(self, output=sys.__stdout__):
        """Prints all model constraints organized by their logical category.
        
        Displays constraints grouped into four categories:
        1. Frame constraints (defining the logical frame)
        2. Model constraints (atomic propositions and relations)
        3. Premise constraints (from input premises)
        4. Conclusion constraints (from input conclusions)
        
        For each category, prints:
        - Total count of constraints
        - Numbered list of constraints with their Z3 representations
        
        If model is satisfiable, shows all constraints.
        If model is unsatisfiable, shows only the constraints in the unsat core.
        
        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        groups = {
            "FRAME": [],
            "MODEL": [],
            "PREMISES": [],
            "CONCLUSIONS": []
        }
        
        # Get the relevant constraints based on model status
        if self.z3_model:
            print("SATISFIABLE CONSTRAINTS:", file=output)
            constraints = self.model_constraints.all_constraints
        elif self.unsat_core is not None:
            print("UNSATISFIABLE CORE CONSTRAINTS:", file=output)
            constraints = [self.constraint_dict[str(c)] for c in self.unsat_core]
        else:
            print("NO CONSTRAINTS AVAILABLE", file=output)
            constraints = []
            
        # Print summary of constraint groups
        frame_count = sum(1 for c in constraints if c in self.model_constraints.frame_constraints)
        model_count = sum(1 for c in constraints if c in self.model_constraints.model_constraints) 
        premise_count = sum(1 for c in constraints if c in self.model_constraints.premise_constraints)
        conclusion_count = sum(1 for c in constraints if c in self.model_constraints.conclusion_constraints)
        
        print(f"- Frame constraints: {frame_count}", file=output)
        print(f"- Model constraints: {model_count}", file=output)
        print(f"- Premise constraints: {premise_count}", file=output)
        print(f"- Conclusion constraints: {conclusion_count}\n", file=output)
        
        # Organize constraints into groups
        for constraint in constraints:
            if constraint in self.model_constraints.frame_constraints:
                groups["FRAME"].append(constraint)
            elif constraint in self.model_constraints.model_constraints:
                groups["MODEL"].append(constraint)
            elif constraint in self.model_constraints.premise_constraints:
                groups["PREMISES"].append(constraint)
            elif constraint in self.model_constraints.conclusion_constraints:
                groups["CONCLUSIONS"].append(constraint)
        
        # Print each group
        for group_name, group_constraints in groups.items():
            if group_constraints:  # Only print groups that have constraints
                print(f"{group_name} CONSTRAINTS:", file=output)
                for index, con in enumerate(group_constraints, start=1):
                    print(f"{index}. {con}\n", file=output)

    def print_constraints(self, constraints, name, output=sys.__stdout__):
        """Prints a numbered list of constraints with appropriate header.
        
        Args:
            constraints (list): List of Z3 constraints to print
            name (str): Name/category of constraints for the header
            output (file, optional): Output stream to write to. Defaults to sys.stdout
            
        Example output:
            Satisfiable frame constraints:
            1. x ∧ y
            2. y → z
            
            or
            
            Unsatisfiable core constraints:
            1. x ∧ ¬x
        """
        if self.z3_model_status:
            print(f"Satisfiable {name} constraints:\n", file=output)
        else:
            print("Unsatisfiable core constraints:\n", file=output)
        for index, con in enumerate(constraints, start=1):
            print(f"{index}. {con}\n", file=output)

    def build_test_file(self, output):
        """Generates a test file from the current model configuration and results.
        
        Creates a Python test file containing the model settings, premises, conclusions,
        and runtime information. The generated file can be used to reproduce the model
        checking results or serve as a regression test.
        
        Args:
            output (file): File-like object to write the test content to
            
        Note:
            Uses the inputs_template to format the test file content with:
            - Model settings
            - Premise sentences
            - Conclusion sentences
            - Z3 solver runtime
        """

        inputs_data = {
            "settings": self.model_constraints.settings,
            "premises": self.premises,
            "conclusions": self.conclusions,
            "z3_model_runtime": self.z3_model_runtime,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)

    def recursive_print(self, sentence, eval_point, indent_num, use_colors):
        """Recursively prints a sentence and its subformulas with their truth values.

        This method handles both atomic and complex sentences, printing them with
        appropriate indentation and optional color coding. For atomic sentences,
        it directly prints the proposition. For complex sentences, it delegates to
        the operator's print method to handle the recursive printing of subformulas.

        Args:
            sentence (Sentence): The sentence object to print
            eval_point (dict): The evaluation point in the model
            indent_num (int): Current indentation level (1-based)
            use_colors (bool): Whether to use ANSI color codes in output

        Note:
            - Indentation is adjusted for second-level formulas for readability
            - Colors are used to indicate truth values when use_colors is True
            - Atomic sentences are printed directly via their proposition
            - Complex sentences delegate to their operator's print_method
        """
        if indent_num == 2:  # NOTE: otherwise second lines don't indent
            indent_num += 1
        if sentence.sentence_letter is not None:  # Print sentence letter
            sentence.proposition.print_proposition(eval_point, indent_num, use_colors)
            return
        operator = sentence.original_operator
        operator.print_method(sentence, eval_point, indent_num, use_colors)  # Print complex sentence

    def print_input_sentences(self, output):
        """Prints the premises and conclusions with their semantic interpretations.
        
        For each premise and conclusion, recursively prints the sentence along with
        its truth value at the main evaluation point. Complex sentences are broken
        down to show the truth values of their subformulas.
        
        Args:
            output (file): The output stream to write to (e.g., sys.stdout)
            
        Note:
            - Requires a valid Z3 model to interpret sentences
            - Uses color coding when printing to sys.stdout
            - Premises are numbered starting from 1
            - Conclusions continue the numbering after premises
        """
        
        def print_sentences(title_singular, title_plural, sentences, start_index, destination):
            """Helper function to print a list of sentences with a title."""
            if not sentences:
                return
                
            if not self.z3_model:
                print("No valid model available - cannot interpret sentences", file=output)
                return
                
            title = title_singular if len(sentences) < 2 else title_plural
            print(title, file=output)
            for index, sentence in enumerate(sentences, start=start_index):
                print(f"{index}.", end="", file=output)
                with redirect_stdout(destination):
                    use_colors = output is sys.__stdout__
                    self.recursive_print(sentence, self.main_point, 1, use_colors)
                    print(file=output)
        
        start_index = 1
        print_sentences(
            "INTERPRETED PREMISE:\n",
            "INTERPRETED PREMISES:\n",
            self.premises,
            start_index,
            output
        )
        continue_index = len(self.premises) + 1
        print_sentences(
            "INTERPRETED CONCLUSION:\n",
            "INTERPRETED CONCLUSIONS:\n",
            self.conclusions,
            continue_index,
            output
        )

    def print_model(self, output):
        """Prints the raw Z3 model or unsat core if print_z3 setting is enabled.
        
        This method prints either the complete Z3 model (if constraints are satisfiable)
        or the unsatisfiable core (if constraints are unsatisfiable), but only when
        the print_z3 setting is True in the model settings.
        
        Args:
            output (file): The output stream to write to (e.g., sys.stdout)
            
        Note:
            - Only prints if self.settings["print_z3"] is True
            - For satisfiable models, prints the complete Z3 model
            - For unsatisfiable models, prints the unsat core
        """
        if self.settings["print_z3"]:
            if self.z3_model_status:
                print(self.z3_model, file=output)
            else:
                print(self.unsat_core, file=output)
        if self.settings["print_z3"]:
            if self.z3_model_status:
                print(self.z3_model, file=output)
            else:
                print(self.unsat_core, file=output)

    def print_info(self, model_status, default_settings, example_name, theory_name, output):
        """Print comprehensive model information and analysis results.
        
        Displays a formatted output containing the model checking results, including
        example metadata, configuration settings, and performance metrics. The output
        is organized into sections showing:
        
        1. Example name and countermodel status
        2. Model configuration (atomic states, semantic theory)
        3. Non-default settings that were modified
        4. Premises and conclusions
        5. Z3 solver runtime statistics
        
        Args:
            model_status (bool): True if a countermodel was found, False otherwise
            default_settings (dict): Base configuration settings for comparison
            example_name (str): Identifier for the logical example being analyzed
            theory_name (str): Name of the semantic theory implementation used
            output (file): File-like object for writing the output
            
        Note:
            Output is formatted with section headers and separators for readability
        """
        
        # Determine result header
        header = "there is a countermodel." if model_status else "there is no countermodel."
        
        # Print example information
        self._print_section_header(example_name, header, output)
        self._print_model_details(theory_name, output)
        self._print_modified_settings(default_settings, output)
        
        # Print constraints and runtime
        self.model_constraints.print_enumerate(output)
        self._print_runtime_footer(output)

    def _print_section_header(self, example_name, header, output):
        """Print the section header with example name and result."""
        print(f"{'='*40}", file=output)
        print(f"\nEXAMPLE {example_name}: {header}\n", file=output)

    def _print_model_details(self, theory_name, output):
        """Print model details including atomic states and semantic theory."""
        print(f"Atomic States: {self.N}\n", file=output)
        print(f"Semantic Theory: {theory_name}\n", file=output)

    def _print_modified_settings(self, default_settings, output):
        """Print settings that have been modified from their default values.
        
        Compares the current settings against the default configuration and prints
        only those settings whose values have been changed. This helps identify
        which configuration parameters were customized for this model instance.
        
        Args:
            default_settings (dict): The baseline configuration settings
            output (file): File-like object to write the output to
            
        Note:
            Settings are printed in 'key = value' format with indentation
            Only modified settings are included in the output
        """
        modified_settings = {
            key: self.settings[key]
            for key, default_value in default_settings.items() 
            if default_value != self.settings[key]
        }
        
        if modified_settings:
            print("Non-Default Settings:", file=output)
            for key, value in modified_settings.items():
                print(f"  {key} = {value}", file=output)
            print()

    def _print_runtime_footer(self, output):
        """Print Z3 runtime and separator footer."""
        print(f"\nZ3 Run Time: {self.z3_model_runtime} seconds", file=output)
        print(f"\n{'='*40}\n", file=output)

