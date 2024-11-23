'''
things in hidden_things right now:
    - PropositionDefaults
    - ModelConstraints
    - ModelStructure
'''

from z3 import (
    And,
    ArrayRef,
    BitVecSort,
    EmptySet,
    IsMember,
    Not,
    BitVecVal,
    SetAdd,
    Solver,
    sat,
    simplify,
)

import time

from functools import reduce

from hidden_helpers import (
    bitvec_to_substates,
    int_to_binary,
    not_implemented_string,
)

import sys

from syntactic import (
    Operator
)

class SemanticDefaults:
    """Includes default attributes and methods to be inherited by a semantics
    including frame constraints, truth and falsity, and logical consequence."""

    def __init__(self, N):

        # Store the number of states
        self.N = N

        # Define top and bottom states
        max_value = (1 << self.N) - 1 # NOTE: faster than 2**self.N - 1
        self.full_bit = BitVecVal(max_value, self.N)
        self.null_bit = BitVecVal(0, self.N)
        self.all_bits = [BitVecVal(i, self.N) for i in range(1 << self.N)]
        
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

        # Store values from sentence
        self.name = sentence.name
        # if sentence.derived_sentence: # accords with model constraints
        #     self.arguments = sentence.derived_sentence.arguments
        # else:
        self.operator = sentence.operator
        self.arguments = sentence.arguments
        self.sentence_letter = sentence.sentence_letter
        # self.derived_object = sentence.derived_object
        # self.prefix_sentence = sentence.prefix_sentence

        # Store values from model_structure argument
        self.model_structure = model_structure
        self.N = self.model_structure.N
        self.model_constraints = self.model_structure.model_constraints

        # Store values from model_constraints
        self.semantics = self.model_constraints.semantics
        self.sentence_letters = self.model_constraints.sentence_letters
        self.contingent = self.model_constraints.contingent
        self.non_null = self.model_constraints.non_null
        self.disjoint = self.model_constraints.disjoint
        self.print_impossible = self.model_constraints.print_impossible

        # Set defaults for verifiers and falsifiers
        self.verifiers, self.falsifiers = [], []

    # # DISCUSS: this is something we ultimately want to move into
    # # semantic.py since users will define there what a proposition is and so
    # # should be able to configure the representation to match
    # def __repr__(self):
    #     N = self.model_structure.model_constraints.semantics.N
    #     possible = self.model_structure.model_constraints.semantics.possible
    #     z3_model = self.model_structure.z3_model
    #     ver_states = {
    #         bitvec_to_substates(bit, N)
    #         for bit in self.verifiers
    #         if z3_model.evaluate(possible(bit)) or self.print_impossible
    #     }
    #     fal_states = {
    #         bitvec_to_substates(bit, N)
    #         for bit in self.falsifiers
    #         if z3_model.evaluate(possible(bit)) or self.print_impossible
    #     }
    #     ver_prints = pretty_set_print(ver_states)
    #     fal_prints = pretty_set_print(fal_states)
    #     return f"< {ver_prints}, {fal_prints} >"

    def __repr__(self):
        return self.name

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, PropositionDefaults):
            return self.name == other.name
        return False

class ModelConstraints:
    """Takes semantics and proposition_class as arguments to build generate
    and storing all Z3 constraints. This class is passed to ModelStructure."""

    def __init__(
        self,
        syntax,
        semantics,
        proposition_class,
        contingent=False,
        non_null=True,
        disjoint=False,
        print_impossible=False,
    ):

        # Store syntax and its values
        self.syntax = syntax
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions
        self.all_sentences = self.syntax.all_sentences
        self.operator_collection = self.syntax.operator_collection
        self.sentence_letters = self.syntax.sentence_letters

        # Store semantics and use to define operator dictionary
        self.semantics = semantics
        self.operators = { # applies semantics to each operator
            op_name: op_class(semantics)
            for (op_name, op_class) in self.operator_collection.items()
        }

        # Store proposition_class defined by the user
        self.proposition_class = proposition_class

        # Store user settings
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint
        self.print_impossible = print_impossible

        # use semantics to recursively update all derived_objects
        self.instantiate(self.all_sentences.values())

        # TODO: fix sentence_letter attribute to correctly store Z3 expression

        # Use semantics to generate and store Z3 constraints
        self.frame_constraints = self.semantics.frame_constraints
        self.model_constraints = []
        for sentence_letter in self.sentence_letters:
            self.model_constraints.extend(
                self.proposition_class.proposition_constraints(
                    self,
                    sentence_letter,
                )
            )
        self.premise_constraints = [
            self.semantics.premise_behavior(
                premise,
                self.semantics.main_world,
            )
            for premise in self.premises
        ]
        self.conclusion_constraints = [
            self.semantics.conclusion_behavior(
                conclusion,
                self.semantics.main_world,
            )
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

    def instantiate(self, sentences):
        """Updates each instance of Sentence in sentences by adding the
        prefix_sent to that instance, returning the input sentences."""
        for sent_obj in sentences:
            # # TODO: add a better check/continue here
            # if sent_obj.updated_objects:
            #     continue
            # # TODO: recursion seems not to be needed given that the whole 
            # # dictionary is instantiated
            # if sent_obj.original_arguments:
            #     self.instantiate(sent_obj.original_arguments)
            # if sent_obj.arguments:
            #     self.instantiate(sent_obj.arguments)
            sent_obj.update_objects(self)
        # for sent_obj in sentences:
        #     print(f"AFTER: sentence_letter {sent_obj.sentence_letter} is type {type(sent_obj.sentence_letter)} for {sent_obj}")

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


class ModelStructure:
    """Solves and stores the Z3 model for an instance of ModelSetup."""

    def __init__(self, model_constraints, max_time=1):
        self.constraint_dict = {} # hopefully temporary, for unsat_core

        # Store arguments
        self.model_constraints = model_constraints
        self.max_time = max_time

        # Store from model_constraint.syntax
        self.syntax = self.model_constraints.syntax
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions
        self.all_sentences = self.syntax.all_sentences
        self.sentence_letters = self.syntax.sentence_letters

        # Store from model_constraint.semantics
        self.semantics = self.model_constraints.semantics
        self.main_world = self.semantics.main_world
        self.all_bits = self.semantics.all_bits
        self.N = self.semantics.N

        # Store from model_constraint
        self.proposition_class = self.model_constraints.proposition_class
        self.print_impossible = self.model_constraints.print_impossible

        # Solve Z3 constraints and store values
        timeout, z3_model, z3_model_status, z3_model_runtime = self.solve(
            self.model_constraints,
            self.max_time,
        )
        self.timeout = timeout
        self.z3_model = z3_model if z3_model_status else None
        self.unsat_core = z3_model if not z3_model_status else None
        self.z3_model_status = z3_model_status
        self.z3_model_runtime = z3_model_runtime

        # Store possible_bits, world_bits, and main_world from the Z3 model
        if not self.z3_model_status:
            self.poss_bits, self.world_bits, self.main_world = None, None, None
            return
        self.poss_bits = [
            bit
            for bit in self.all_bits
            if bool(self.z3_model.evaluate(self.semantics.possible(bit)))
            # LINTER: cannot access attribute "evaluate" for class "AstVector"
        ]
        self.world_bits = [
            bit
            for bit in self.poss_bits
            if bool(self.z3_model.evaluate(self.semantics.is_world(bit)))
            # LINTER: cannot access attribute "evaluate" for class "AstVector"
        ]
        if not self.z3_model is None:
            self.main_world = self.z3_model[self.main_world]

        # Recursively update every derived_object to store a propositions
        self.interpret(self.all_sentences.values())

    def solve(self, model_constraints, max_time):
        solver = Solver()
        # fc, mc, pc, cc = model_constraints.frame_constraints, model_constraints.model_constraints, model_constraints.premise_constraints, model_constraints.conclusion_constraints
        # for c_group, c_group_name in [(fc, "frame"), (mc, "model"), (pc, "premises"), (cc, "conclusions")]:
        #     assert isinstance(c_group, list)
        #     for ix, c in enumerate(c_group):
        #         c_id = f"{c_group_name}{ix+1}"
        #         solver.assert_and_track(c, c_id)
        #         self.constraint_dict[c_id] = c
        solver.set("timeout", int(max_time * 1000))  # time in seconds
        try:
            model_start = time.time()  # start benchmark timer
            # result = solver.check()
            result = solver.check(model_constraints.all_constraints)
            model_end = time.time()  # end benchmark timer
            model_runtime = round(model_end - model_start, 4)
            if result == sat:
                return False, solver.model(), True, model_runtime
            if solver.reason_unknown() == "timeout":
                return True, None, False, model_runtime
            return False, solver.unsat_core(), False, model_runtime
        except RuntimeError as e:  # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, None, False, None

    def interpret(self, sentences):
        """Updates each instance of Sentence in sentences by adding the
        prefix_sent to that instance, returning the input sentences."""

        for sent_obj in sentences:
            # TODO: add appropriate check
            # if sent_obj.derived_object is None:
            #     raise ValueError(f"{sent_obj} has 'None' for derived_object.")
            if sent_obj.proposition:
                continue
            if sent_obj.original_arguments:
                self.interpret(sent_obj.original_arguments)
            if sent_obj.arguments:
                self.interpret(sent_obj.arguments)
            sent_obj.update_proposition(self)

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        BLUE = "\033[34m"
        RESET = "\033[0m"
        # sentence_letters = self.sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N)}{RESET}\n",
            file=output,
        )
        # true_in_eval = set()
        # for sent in sentence_letters:
        #     for bit in self.all_bits:
        #         ver_bool = self.model_constraintsferify(bit, self.z3_model[sent])
        #         part_bool = bit_part(bit, main_world)
        #         if bool(self.z3_model.evaluate(ver_bool) and part_bool):
        #             true_in_eval.add(sent)
        #             break  # exits the first for loop
        # false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
        # GREEN = '\033[32m'
        # RED = '\033[31m'
        # # YELLOW = '\033[33m'
        # RESET = '\033[0m'
        # world_state = bitvec_to_substates(main_world, N)
        # if true_in_eval:
        #     true_eval_list = sorted([str(sent) for sent in true_in_eval])
        #     true_eval_string = ", ".join(true_eval_list)
        #     print(
        #         f"  {GREEN}{true_eval_string}  (True in {world_state}){RESET}",
        #         file=output,
        #     )
        # if false_in_eval:
        #     false_eval_list = sorted([str(sent) for sent in false_in_eval])
        #     false_eval_string = ", ".join(false_eval_list)
        #     print(
        #         f"  {RED}{false_eval_string}  (False in {world_state}){RESET}",
        #         file=output,
        #     )
        # print(file=output)

    # def print_to(self, print_constraints_bool, print_impossible, output=sys.__stdout__):
    #     """append all elements of the model to the file provided"""
    #     self.print_all(print_impossible, output)
    #     structure = self.model_constraints
    #     setup = self.model_constraints
    #     if print_constraints_bool:
    #         structure.print_constraints(setup.frame_constraints, 'FRAME', output)
    #         structure.print_constraints(setup.prop_constraints, 'PROPOSITION', output)
    #         structure.print_constraints(setup.premise_constraints, 'PREMISE', output)
    #         structure.print_constraints(setup.conclusion_constraints, 'CONCLUSION', output)
    #     print(f"Run time: {self.model_runtime} seconds\n", file=output)

    # def save_to(self, cons_include, print_impossible, output):
    #     """append all elements of the model to the file provided"""
    #     constraints = self.model_constraints.constraints
    #     self.print_all(print_impossible, output)
    #     self.model_constraints.build_test_file(output)
    #     if cons_include:
    #         print("# Satisfiable constraints", file=output)
    #         # TODO: print constraint objects, not constraint strings
    #         print(f"all_constraints = {constraints}", file=output)

    def print_states(self, output=sys.__stdout__):
        """Print all fusions of atomic states in the model."""

        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )
        
        def format_state(bin_rep, state, color, label=""):
            """Helper function to format and print a state."""
            label_str = f" ({label})" if label else ""
            print(f"  {WHITE}{bin_rep} = {color}{state}{label_str}{RESET}", file=output)
        
        # Extract semantics and state information
        # TODO: move to class attribute
        print("\nState Space:", file=output)

        # Define ANSI color codes
        COLORS = {
            "default": "\033[37m",  # WHITE
            "world": "\033[34m",    # BLUE
            "possible": "\033[36m", # CYAN
            "impossible": "\033[35m", # MAGENTA
            "initial": "\033[33m",  # YELLOW
        }
        RESET = "\033[0m"
        WHITE = COLORS["default"]

        # Print state details
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, COLORS["initial"])
            elif bit in self.world_bits:
                format_state(bin_rep, state, COLORS["world"], "world")
            elif bit in self.poss_bits:
                format_state(bin_rep, state, COLORS["possible"])
            elif self.print_impossible:
                format_state(bin_rep, state, COLORS["impossible"], "impossible")

    # def rec_print(self, sentence, eval_world, indent):
    #     # all_sentences = self.all_sentences
    #
    #     # B: should print_proposition be moved to the Sentence class?
    #     # that way it could call itself instead of storing sent_obj in props.
    #     # either way, I'm thinking print_proposition should dispatch to a method
    #     # in Proposition class to print sentence letters, and otherwise dispatch
    #     # to operators to look up the appropriate print method so that all
    #     # printing is defined alongside the semantics in each operator or in
    #     # Proposition which is also defined by the user.
    #
    #     sentence.proposition.print_proposition(eval_world, indent)
    #     if (len(sentence.derived_object) == 1):  # prefix has operator instances and AtomSorts
    #         return
    #
    #     # B: I think eventually all operators should have a print method
    #     if not hasattr(sentence.operator, 'print_operator'):
    #         for sentence_arg in sentence.arguments:
    #             self.rec_print(sentence_arg, eval_world, indent + 1)
    #
    #     # B: I think eventually all operators should have a print method
    #     if self.operator and hasattr(self.operator, 'print_operator'):
    #         self.operator.print_operator(self, eval_world, indent_num)


    # M: eventually, we need to add a condition on unilateral or bilateral semantics
    # so that one set vs two is printed (one for unilateral, two for bilateral)
    # B: I think it is OK to leave it to the user to change how things get
    # printed where this is defined here. There could in general be many changes
    # that users may want to make and so I don't think it is necessary to
    # anticipate all of them. But it will be good to experiment with Lukas'
    # semantics to see how making those changes go.

    def recursive_print(self, sentence, eval_world, indent_num):
        if indent_num == 2: # NOTE: otherwise second lines don't indent
            indent_num += 1
        if sentence.sentence_letter is not None:  # print sentence letter
            sentence.proposition.print_proposition(eval_world, indent_num)
            return
        operator = sentence.original_operator
        operator.print_method(sentence, eval_world, indent_num)  # print complex sentence

    def print_input_sentences(self, output):
        """Prints the interpreted premises and conclusions, leveraging recursive_print."""
        
        def print_sentences(title_singular, title_plural, sentences, start_index):
            """Helper function to print a list of sentences with a title."""
            if sentences:
                title = title_singular if len(sentences) < 2 else title_plural
                print(title, file=output)
                for index, sentence in enumerate(sentences, start=start_index):
                    print(f"{index}.", end="", file=output)
                    self.recursive_print(sentence, self.main_world, 1)
                    print(file=output)
        
        print_sentences(
            "INTERPRETED PREMISE:\n",
            "INTERPRETED PREMISES:\n",
            self.premises,
            start_index=1,
        )
        print_sentences(
            "INTERPRETED CONCLUSION:\n",
            "INTERPRETED CONCLUSIONS:\n",
            self.conclusions,
            start_index=len(self.premises) + 1,
        )

    def print_all(self, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        if self.z3_model_status:
            print(f"\nThere is a {self.N}-model of:\n", file=output)
            self.model_constraints.print_enumerate(output)
            self.print_states(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            # TODO: make method for runtime and progress bar
            print(f"Run time: {self.z3_model_runtime} seconds\n", file=output)
            return
        print(f"\nThere is no {self.N}-model of:\n")
        self.model_constraints.print_enumerate(output)
        # print([self.constraint_dict[str(c)] for c in self.unsat_core])
