'''
things in hidden_things right now:
    - PropositionDefaults
    - ModelConstraints
    - ModelStructure
'''

from z3 import (
    sat,
    Solver,
)

import time

from hidden_helpers import (
    bitvec_to_substates,
    int_to_binary,
    not_implemented_string,
)

import sys

class PropositionDefaults:
    """Defaults inherited by every proposition."""

    def __init__(self, sentence, model_structure):

        # Raise error if instantiated directly instead of as a bare class
        if self.__class__ == PropositionDefaults:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))

        # Store values from sentence argument
        self.sentence = sentence
        self.name = sentence.name
        self.arguments = sentence.arguments
        self.prefix_operator = sentence.prefix_operator
        self.prefix_object = sentence.prefix_object
        self.prefix_sentence = sentence.prefix_sentence

        # Store values from model_structure argument
        self.model_structure = model_structure
        self.N = self.model_structure.N
        self.model_constraints = self.model_structure.model_constraints
        self.semantics = self.model_constraints.semantics
        self.sentence_letters = self.model_constraints.sentence_letters
        self.contingent = self.model_constraints.contingent
        self.non_null = self.model_constraints.non_null
        self.disjoint = self.model_constraints.disjoint
        self.print_impossible = self.model_constraints.print_impossible

        # Set defaults for verifiers and falsifiers
        self.verifiers, self.falsifiers = [], [] # avoids linter errors in print_proposition

        # TODO: DISCUSS
        # # B: is this still needed? the code works without it and it seems that
        # # the hash is defined below. just trying to clean up loose ends...
        # try:
        #     hash(self)
        # except:
        #     type(self).__hash__ = lambda self: PropositionDefaults.__hash__(self)

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

        # use semantics to recursively update all prefix_objects
        self.instantiate(self.all_sentences.values())

        # Use semantics to generate and store Z3 constraints
        self.frame_constraints = self.semantics.frame_constraints
        self.model_constraints = []
        for sent_let in self.sentence_letters:
            self.model_constraints.extend(
                self.proposition_class.proposition_constraints(
                    self,
                    # TODO: fix definition so that [0] is not needed below?
                    # seems to occur elsewhere as well... is this needed?
                    sent_let.prefix_object[0],
                )
            )
        self.premise_constraints = [
            self.semantics.premise_behavior(
                prem.prefix_object,
                self.semantics.main_world,
            )
            for prem in self.premises
        ]
        self.conclusion_constraints = [
            self.semantics.conclusion_behavior(
                conc.prefix_object,
                self.semantics.main_world,
            )
            for conc in self.conclusions
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
            if sent_obj.prefix_object:
                continue
            if sent_obj.arguments:
                self.instantiate(sent_obj.arguments)
            sent_obj.update_prefix_object(self)

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

        # Store arguments
        self.model_constraints = model_constraints
        self.all_sentences = self.model_constraints.all_sentences
        self.max_time = max_time

        # Store from model_constraint.syntax
        self.syntax = self.model_constraints.syntax
        self.premises = self.syntax.premises # list of sentence objects for premises
        self.conclusions = self.syntax.conclusions # list of sentence objects for conclusions
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

        # Recursively update every prefix_object to store a proposition
        self.interpret(self.all_sentences.values())

    def solve(self, model_constraints, max_time):
        solver = Solver()
        solver.add(model_constraints.all_constraints)
        solver.set("timeout", int(max_time * 1000))  # time in seconds
        try:
            model_start = time.time()  # start benchmark timer
            result = solver.check()
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
            if sent_obj.prefix_object is None:
                raise ValueError(f"{sent_obj} has 'None' for prefix_object.")
            if sent_obj.proposition:
                continue
            if sent_obj.arguments: # if sent_obj.arguments and not sent_obj.propositions
                self.interpret(sent_obj.arguments)
            sent_obj.update_proposition(self)

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        N = self.model_constraints.semantics.N
        BLUE = "\033[34m"
        RESET = "\033[0m"
        sentence_letters = self.sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, N)}{RESET}\n",
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
        """print all fusions of atomic states in the model
        print_impossible is a boolean for whether to print impossible states or not
        first print function in print.py"""
        N = self.model_constraints.semantics.N
        print("\nState Space:", file=output)  # Print states
        YELLOW = "\033[33m"
        BLUE = "\033[34m"
        MAGENTA = "\033[35m"
        CYAN = "\033[36m"
        WHITE = "\033[37m"
        RESET = "\033[0m"
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, N)
            bin_rep = (
                bit.sexpr()
                if N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), N)
            )
            if bit == 0:
                print(f"  {WHITE}{bin_rep} = {YELLOW}{state}{RESET}", file=output)
                continue
            if bit in self.world_bits:
                print(f"  {WHITE}{bin_rep} = {BLUE}{state} (world){RESET}", file=output)
                continue
            if bit in self.poss_bits:
                print(f"  {WHITE}{bin_rep} = {CYAN}{state}{RESET}", file=output)
                continue
            if self.print_impossible:
                print(
                    f"  {WHITE}{bin_rep} = {MAGENTA}{state} (impossible){RESET}",
                    file=output,
                )

    def rec_print(self, sentence, eval_world, indent):
        all_sentences = self.all_sentences
        sentence.proposition.print_proposition(eval_world, indent)
        if (len(sentence.prefix_object) == 1):  # prefix has operator instances and AtomSorts
            return
        if not hasattr(sentence.prefix_operator, 'print_operator'):
            for sentence_arg in sentence.arguments:
                self.rec_print(sentence_arg, eval_world, indent + 1)

    def print_inputs_recursively(self, output):
        """does rec_print for every proposition in the input propositions
        returns None"""
        initial_eval_world = self.main_world
        # premises = self.model_constraints.syntax.premises
        # conclusions = self.model_constraints.syntax.conclusions
        start_conclusion_number = len(self.premises) + 1
        if self.premises:
            if len(self.premises) < 2:
                print("INTERPRETED PREMISE:\n", file=output)
            else:
                print("INTERPRETED PREMISES:\n", file=output)
            for index, sentence in enumerate(self.premises, start=1):
                print(f"{index}.", end="", file=output)
                self.rec_print(sentence, initial_eval_world, 1)
                # input_prop.print_proposition(initial_eval_world, 1)
                print(file=output)
        if self.conclusions:
            if len(self.conclusions) < 2:
                print("INTERPRETED CONCLUSION:\n", file=output)
            else:
                print("INTERPRETED CONCLUSIONS:\n", file=output)
            for index, sentence in enumerate(
                self.conclusions, start=start_conclusion_number
            ):
                print(f"{index}.", end="", file=output)
                self.rec_print(sentence, initial_eval_world, 1)
                print(file=output)

    def print_all(self, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        N = self.model_constraints.semantics.N
        if self.z3_model_status:
            print(f"\nThere is a {N}-model of:\n", file=output)
            self.model_constraints.print_enumerate(output)
            self.print_states(output)
            self.print_evaluation(output)
            self.print_inputs_recursively(output)
            return
        print(f"\nThere is no {N}-model of:\n")
        self.model_constraints.print_enumerate(output)
