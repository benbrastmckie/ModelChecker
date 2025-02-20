'''
things in hidden_things right now:
    - PropositionDefaults
    - ModelConstraints
    - ModelStructure
'''

import sys
from contextlib import redirect_stdout
import time
from functools import reduce
from string import Template
from z3 import (
    And,
    ArrayRef,
    BitVecSort,
    EmptySet,
    ExprRef,
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
    """Includes default attributes and methods to be inherited by a semantics
    including frame constraints, truth and falsity, and logical consequence."""

    def __init__(self):

        # Store the name
        self.name = self.__class__.__name__

        # Define main_point
        self.main_point = None

        # Define the frame constraints
        self.frame_constraints = None

        # Define invalidity conditions
        self.premise_behavior = None
        self.conclusion_behavior = None

    def fusion(self, bit_s, bit_t):
        """Return bitwise OR of bit_s and bit_t (Z3 bit vectors)."""
        return bit_s | bit_t

    def z3_set(self, python_set, N):
        """Convert a Python set to a Z3 set of bit-width N."""
        z3_set = EmptySet(BitVecSort(N))
        for elem in python_set:
            z3_set = SetAdd(z3_set, elem)
        return z3_set

    def z3_set_to_python_set(self, z3_set, domain):
        """Convert a Z3 set to a Python set using domain for membership checks."""
        python_set = set()
        for elem in domain:
            if bool(simplify(IsMember(elem, z3_set))):
                python_set.add(elem)
        return python_set

    def total_fusion(self, set_P):
        """Return the fused result (bitwise OR) of all elements in set_P."""
        if isinstance(set_P, ArrayRef):
            set_P = self.z3_set_to_python_set(set_P, self.all_bits)
        return reduce(self.fusion, list(set_P))

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t

    def is_proper_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return And(self.is_part_of(bit_s, bit_t), bit_s != bit_t)

    def non_null_part_of(self, bit_s, bit_t):
        """bit_s verifies atom and is not the null state
        returns a Z3 constraint"""
        return And(Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def product(self, set_A, set_B):
        """set of pairwise fusions of elements in set_A and set_B"""
        product_set = set()
        for bit_a in set_A:
            for bit_b in set_B:
                bit_ab = simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
        """union closed under pairwise fusion"""
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))


class PropositionDefaults:
    """Defaults inherited by every proposition."""

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
        self.N = self.model_structure.semantics.N

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
    """Takes semantics and proposition_class as arguments to build generate
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
        """useful for using model-checker in a python file"""
        premises = list(self.syntax.premises)
        conclusions = list(self.syntax.conclusions)
        return f"ModelConstraints for premises {premises} and conclusions {conclusions}"

    def _load_sentence_letters(self):
        sentence_letters = []
        for packed_letter in self.syntax.sentence_letters:
            unpacked_letter = packed_letter.sentence_letter
            if not isinstance(unpacked_letter, ExprRef):
                raise TypeError("The sentence letter {letter} is not of type z3.ExprRef")
            sentence_letters.append(unpacked_letter) 
        return sentence_letters

    def copy_dictionary(self, operator_collection):
        """Copies the operator_dictionary from operator_collection."""
        return {
            op_name : op_class(self.semantics)
            for (op_name, op_class) in operator_collection.items()
        }

    # # NOTE: UPDATE OP STRATEGY
    # def apply_semantics(self, operator_collection):
    #     """Passes semantics into each operator in collection."""
    #     operator_collection.update_operators(self.semantics)
    #     return operator_collection

    def instantiate(self, sentences):
        """Updates each instance of Sentence in sentences by adding the
        prefix_sent to that instance, returning the input sentences."""
        for sent_obj in sentences:
            if sent_obj.arguments:
                self.instantiate(sent_obj.arguments)
            sent_obj.update_objects(self)

    def print_enumerate(self, output=sys.__stdout__):
        """prints the premises and conclusions with numbers"""
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
    """Solves and stores the Z3 model for an instance of ModelSetup."""

    def __init__(self, model_constraints, max_time=1):
        self.constraint_dict = {} # hopefully temporary, for unsat_core

        # Store arguments
        self.model_constraints = model_constraints
        self.max_time = max_time

        # Store from model_constraints.semantics
        self.semantics = self.model_constraints.semantics
        self.main_point = self.semantics.main_point
        self.all_bits = self.semantics.all_bits # TODO: move?
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

        # Solve Z3 constraints and store results
        solver_restults = self.solve(self.model_constraints, self.max_time)
        self._process_solver_results(solver_restults)

        # Exit early if no valid model was found
        if self.timeout or self.z3_model is None:
            return

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

        # Recursively update propositions
        self.interpret(self.premises + self.conclusions)

    def _process_solver_results(self, solver_results):
        """Process and store the results from the Z3 solver.
        
        Args:
            solver_results: Tuple containing (timeout, z3_model, z3_model_status, z3_model_runtime)
        """
        timeout, z3_model, z3_model_status, z3_model_runtime = solver_results
        
        self.timeout = timeout
        self.z3_model_status = z3_model_status
        self.z3_model_runtime = z3_model_runtime
        
        # Store either the model or unsat core based on status
        self.z3_model = z3_model if z3_model_status else None
        self.unsat_core = z3_model if not z3_model_status else None

    def solve(self, model_constraints, max_time):
        solver = Solver()
        # Track each constraint with a unique name
        fc, mc, pc, cc = (
            model_constraints.frame_constraints,
            model_constraints.model_constraints,
            model_constraints.premise_constraints,
            model_constraints.conclusion_constraints
        )
        for c_group, c_group_name in [
            (fc, "frame"),
            (mc, "model"),
            (pc, "premises"),
            (cc, "conclusions")
        ]:
            for ix, c in enumerate(c_group):
                c_id = f"{c_group_name}{ix+1}"
                solver.assert_and_track(c, c_id)
                self.constraint_dict[c_id] = c

        solver.set("timeout", int(max_time * 1000))  # time in seconds
        try:
            def measure_runtime():
                """Calculate the runtime of the solver check."""
                end_time = time.time()
                return round(end_time - start_time, 4)

            def create_result(is_timeout, model_or_core, is_satisfiable):
                """Create a standardized result tuple."""
                return is_timeout, model_or_core, is_satisfiable, measure_runtime()

            start_time = time.time()
            result = solver.check()
            
            if result == sat:
                return create_result(
                    is_timeout=False,
                    model_or_core=solver.model(),
                    is_satisfiable=True
                )
            
            if solver.reason_unknown() == "timeout":
                return create_result(
                    is_timeout=True,
                    model_or_core=None,
                    is_satisfiable=False
                )
            
            return create_result(
                is_timeout=False,
                model_or_core=solver.unsat_core(),
                is_satisfiable=False
            )
        except RuntimeError as e:  # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, None, False, None

    def interpret(self, sentences):
        """Updates each instance of Sentence in sentences by adding the
        prefix_sent to that instance, returning the input sentences."""

        for sent_obj in sentences:
            if sent_obj.proposition is not None:
                continue
            if sent_obj.arguments:
                self.interpret(sent_obj.arguments)
            sent_obj.update_proposition(self)

    def print_grouped_constraints(self, output=sys.__stdout__):
        """Prints constraints organized by their groups (frame, model, premises, conclusions)"""
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
        """prints constraints in an numbered list"""
        if self.z3_model_status:
            print(f"Satisfiable {name} constraints:\n", file=output)
        else:
            print("Unsatisfiable core constraints:\n", file=output)
        for index, con in enumerate(constraints, start=1):
            print(f"{index}. {con}\n", file=output)

    def build_test_file(self, output):
        """generates a test file from input to be saved"""

        inputs_data = {
            "settings": self.model_constraints.settings,
            "premises": self.premises,
            "conclusions": self.conclusions,
            "z3_model_runtime": self.z3_model_runtime,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)

    def recursive_print(self, sentence, eval_point, indent_num, use_colors):
        if indent_num == 2:  # NOTE: otherwise second lines don't indent
            indent_num += 1
        if sentence.sentence_letter is not None:  # Print sentence letter
            sentence.proposition.print_proposition(eval_point, indent_num, use_colors)
            return
        operator = sentence.original_operator
        operator.print_method(sentence, eval_point, indent_num, use_colors)  # Print complex sentence

    def print_input_sentences(self, output):
        """Prints the interpreted premises and conclusions, leveraging recursive_print."""
        
        def print_sentences(title_singular, title_plural, sentences, start_index, destination):
            """Helper function to print a list of sentences with a title."""
            if sentences:
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
        if self.settings["print_z3"]:
            if self.z3_model_status:
                print(self.z3_model, file=output)
            else:
                print(self.unsat_core, file=output)

    def print_info(self, model_status, default_settings, example_name, theory_name, output):
        """Print model information including example details, settings, and runtime.
        
        Args:
            model_status (bool): Whether a countermodel was found
            default_settings (dict): Default settings to compare against
            example_name (str): Name of the example being checked
            theory_name (str): Name of the semantic theory being used
            output (file): Output stream to write to
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
        """Print any settings that differ from defaults."""
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

