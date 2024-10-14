from z3 import (
    sat,
    Solver,
)

import time

from hidden_helpers import (
    remove_repeats,
    bitvec_to_substates,
    int_to_binary,
    not_implemented_string,
    pretty_set_print,

)

import sys

class PropositionDefaults:
    """Defaults inherited by every proposition."""

    def __init__(self, prefix_sentence, model_structure):

        # Raise error
        if self.__class__ == PropositionDefaults:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))

        # Store arguments
        self.prefix_sentence = prefix_sentence
        self.model_structure = model_structure

        # Store values from model_structure
        self.N = self.model_structure.N
        self.name = self.model_structure.infix(prefix_sentence)
        self.model_constraints = self.model_structure.model_constraints

        # Store values from model_constraints
        self.semantics = self.model_constraints.semantics
        self.contingent = self.model_constraints.contingent
        self.non_null = self.model_constraints.non_null
        self.disjoint = self.model_constraints.disjoint
        self.print_impossible = self.model_constraints.print_impossible
        
        # Store proposition in model_structure.all_propositions dictionary
        self.model_structure.all_propositions[self.name] = self
        self.verifiers, self.falsifiers = None, None # avoids linter errors in print_proposition
        try:
            hash(self)
        except:
            type(self).__hash__ = lambda self: PropositionDefaults.__hash__(self)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, PropositionDefaults):
            return self.name == other.name
        return False
    
    # M: eventually, we need to add a condition on unilateral or bilateral semantics
    # B: not sure I follow? say more?
    # M: sorry meant unilateral and bilateral, not unary and binary (edited to reflect)
    # so that one set vs two is printed (one for unilateral, two for bilateral)
    def print_proposition(self, eval_world, indent_num=0):
        N = self.model_structure.model_constraints.semantics.N
        truth_value = self.truth_value_at(eval_world) 
        possible = self.model_structure.model_constraints.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
            if z3_model.evaluate(possible(bit))
            or self.print_impossible
        }
        ver_prints = pretty_set_print(ver_states) if ver_states else '∅'
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit))
            or self.print_impossible
        }
        # temporary fix on unary/binary issue below (the 'is None' bit)
        fal_prints = pretty_set_print(fal_states) if fal_states is not None else '∅'
        world_state = bitvec_to_substates(eval_world, N)
        RED = '\033[31m'
        GREEN = '\033[32m'
        RESET = '\033[0m'
        FULL = '\033[37m'
        PART = '\033[33m'
        if indent_num == 1:
            if truth_value:
                FULL = GREEN
                PART = GREEN
            if not truth_value:
                FULL = RED
                PART = RED
            if truth_value is None:
                world_state = bitvec_to_substates(eval_world, N)
                print(
                    f"\n{RED}WARNING:{RESET}"
                    f"{self} is neither true nor false at {world_state}.\n"
                )
        print(
            f"{'  ' * indent_num}{FULL}|{self}| = < {ver_prints}, {fal_prints} >{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )


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

        # Store inputs
        self.syntax = syntax
        self.proposition_class = proposition_class
        self.semantics = semantics
        self.operators = {
            op_name: op_class(semantics)
            for (op_name, op_class) in syntax.operators.items()
            # if op_name in ops # M: what did this do? 
        }
        # self.infix_premises = syntax.infix_premises
        # self.infix_conclusions = syntax.infix_conclusions

        # the prefix stuff needs to be activated
        self.prefix_premises = [self.activate_prefix_with_semantics(pfs) for pfs in syntax.prefix_premises]
        self.prefix_conclusions = [self.activate_prefix_with_semantics(pfs) for pfs in syntax.prefix_conclusions]

        self.all_subsentences = syntax.all_subsentences
        self.all_sentence_letters = syntax.all_sentence_letters
        # print(self.prefix_premises)
        # for pfx in self.prefix_premises:
        #     print([type(x) for x in pfx])

        # Store settings
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint
        self.print_impossible = print_impossible

        # Use semantics to generate and store Z3 constraints
        self.frame_constraints = self.semantics.frame_constraints
        self.model_constraints = []
        for sl in self.all_sentence_letters:
            self.model_constraints.extend(
                self.proposition_class.proposition_constraints(self, sl)
            )
        self.premise_constraints = [
            self.semantics.premise_behavior(prem, self.semantics.main_world)
            for prem in self.syntax.prefix_premises
        ]
        self.conclusion_constraints = [
            self.semantics.conclusion_behavior(conc, self.semantics.main_world)
            for conc in self.syntax.prefix_conclusions
        ]
        self.all_constraints = (
            self.frame_constraints
            + self.model_constraints
            + self.premise_constraints
            + self.conclusion_constraints
        )

    def activate_prefix_with_semantics(self, prefix_sentence):
        """
        prefix sentence has operator classes and AtomSorts
        """
        new_prefix_form = []
        for elem in prefix_sentence:
            if isinstance(elem, type):
                new_prefix_form.append(self.operators[elem.name])
            elif isinstance(elem, list):
                new_prefix_form.append(self.activate_prefix_with_semantics(elem))
            else:
                new_prefix_form.append(elem)
        return new_prefix_form


    def __str__(self):
        """useful for using model-checker in a python file"""
        premises = list(self.syntax.premises)
        conclusions = list(self.syntax.conclusions)
        return f"ModelConstraints for premises {premises} and conclusions {conclusions}"

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
        self.max_time = max_time

        # Store from model_constraint
        self.print_impossible = self.model_constraints.print_impossible
        self.semantics = self.model_constraints.semantics
        self.main_world = self.semantics.main_world
        self.N = self.semantics.N
        self.syntax = self.model_constraints.syntax

        # Store from syntax
        self.prefix_premises = self.syntax.prefix_premises
        self.prefix_conclusions = self.syntax.prefix_conclusions
        self.all_subsentences = self.syntax.all_subsentences
        self.all_sentence_letters = self.syntax.all_sentence_letters

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

        self.all_bits = self.find_all_bits(self.N)
        if not self.z3_model_status:
            self.poss_bits, self.world_bits, self.main_world = None, None, None
            self.all_propositions, self.premise_propositions = None, None
            self.conclusion_propositions = None
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
        self.main_world = self.z3_model[self.main_world]
        # LINTER: object of type "None" is not subscriptable
        # M: it's probably worth ignoring the linter in this case
        self.all_propositions = {}
        self.premise_propositions = [
            self.model_constraints.proposition_class(prefix_sent, self)
            # B: what if there are repeats in prefix_premises?
            for prefix_sent in self.prefix_premises
        ]
        self.conclusion_propositions = [
            self.model_constraints.proposition_class(prefix_sent, self)
            # B: what if there are repeats in prefix_premises?
            for prefix_sent in self.prefix_conclusions
        ]

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

    def summation(self, n, func, start = 0):
        '''summation of i ranging from start to n of func(i)
        used in find_all_bits'''
        if start == n:
            return func(start)
        return func(start) + self.summation(n,func,start+1)

    def find_all_bits(self, size):
        '''extract all bitvectors from the input model
        imported by model_structure'''
        all_bits = []
        max_bit_number = self.summation(size + 1, lambda x: 2**x)
        for val in range(max_bit_number):
            test_bit = BitVecVal(val, size)
            if test_bit in all_bits:
                continue
            all_bits.append(test_bit)
        return all_bits

    # M: might a better place for this be somewhere in the syntax?
    def infix(self, prefix_sent):
        """Takes a sentence in prefix notation and translates it to infix notation
        TODO: what is prefix notation here? Does it matter?
        """
        if len(prefix_sent) == 1:
            return str(prefix_sent[0])
        op = prefix_sent[0]
        if len(prefix_sent) == 2:
            return f"{op} {self.infix(prefix_sent[1])}"
        left_expr = prefix_sent[1]
        right_expr = prefix_sent[2]
        return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        N = self.model_constraints.semantics.N
        sentence_letters = self.all_sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {bitvec_to_substates(main_world, N)}",
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

    def rec_print(self, prop_obj, eval_world, indent):
        prop_obj.print_proposition(eval_world, indent)
        if len(prop_obj.prefix_sentence) == 1: # prefix has operator instances and AtomSorts
            return
        # B: can infix be avoided here by calling on the name of the proposition?
        sub_prefix_sents = prop_obj.prefix_sentence[1:]
        # M: in following two lines, infix_ can't really be removed
        sub_infix_sentences = (self.infix(sub_prefix) for sub_prefix in sub_prefix_sents)
        subprops = (self.all_propositions[infix] for infix in sub_infix_sentences)
        # LINTER: says for above: Object of type "None" is not subscriptable
        for subprop in subprops:
            self.rec_print(subprop, eval_world, indent + 1)

    def print_inputs_recursively(self, output):
        """does rec_print for every proposition in the input propositions
        returns None"""
        initial_eval_world = self.main_world
        premises = self.model_constraints.syntax.premises
        conclusions = self.model_constraints.syntax.conclusions
        # infix_premises = self.model_constraints.infix_premises
        # infix_conclusions = self.model_constraints.infix_conclusions
        start_con_num = len(premises) + 1
        if self.premise_propositions:
            if len(premises) < 2:
                print("INTERPRETED PREMISE:\n", file=output)
            else:
                print("INTERPRETED PREMISES:\n", file=output)
            for index, input_prop in enumerate(self.premise_propositions, start=1):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, 1)
                # input_prop.print_proposition(initial_eval_world, 1)
                print(file=output)
        if conclusions:
            if len(conclusions) < 2:
                print("INTERPRETED CONCLUSION:\n", file=output)
            else:
                print("INTERPRETED CONCLUSIONS:\n", file=output)
            for index, input_prop in enumerate(self.conclusion_propositions, start=start_con_num):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, 1)
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
