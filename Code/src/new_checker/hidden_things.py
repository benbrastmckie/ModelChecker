from z3 import (
    sat,
    Solver,
    simplify,
    z3,
)

import time

from hidden_helpers import (
    parse_expression,
    repeats_removed,
    sentence_letters_in_compound,
    subsentences_of,
)

from old_semantics_helpers import (
    all_sentence_letters,
    find_all_bits,
    bitvec_to_substates,
    int_to_binary,
)

import sys

not_implemented_string = lambda cl_name: (f"user should implement subclass(es) of {cl_name} " +
                                      f"for {cl_name.lower()}s. The {cl_name} " +
                                      "class should never be instantiated.")

class Proposition:
    """Defaults inherited by every proposition."""

    def __init__(self, prefix_sentence, model_structure):
        if self.__class__ == Proposition:
            raise NotImplementedError((not_implemented_string(self.__class__)))
        self.prefix_sentence = prefix_sentence
        self.name = model_structure.infix(self.prefix_sentence)
        self.model_structure = model_structure
        self.semantics = model_structure.model_setup.semantics
        self.non_null = model_structure.model_setup.non_null
        self.contingent = model_structure.model_setup.contingent
        self.model_structure.all_propositions[self.name] = self
        try:
            hash(self)
        except:
            type(self).__hash__ = lambda x: Proposition.__hash__(x)
            # B: linter says cannot assign to attribute "__hash__" for class "type[Proposition]*"
            # Type "(x: Self@Proposition) -> int" is not assignable to type "(self: Self@Proposition) -> int"
            # parameter mismatch: "self" vs "x"

    def __repr__(self):
        return self.name
        # return str(self.prefix_sentence)

    def __hash__(self):
        # B: I tried to define a hash function that is consistent with __eq__
        # so that instances with the same verifiers, falsifiers, and prefix_sentence
        # have the same hash but can't access verifiers and falsifiers from here
        return hash(self.name)
        # return hash((str(self.prefix_sentence), tuple(self.verifiers, self.falsifiers)))
        # return 0


class Operator:
    """Defaults inherited by every operator."""

    name = None
    arity = None

    def __init__(self, semantics):
        if self.__class__ == Operator:
            raise NotImplementedError((not_implemented_string(self.__class__)))
        if self.name == None or self.arity == None:
            op_class = type(self).__name__
            raise NameError(
                f"Your operator class {op_class} is missing a name or an arity. "
                + f"Please add them as class properties of {op_class}."
            )
        self.semantics = semantics

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return str(self.name)

    def __eq__(self, other):
        if isinstance(other, Operator):
            return self.name == other.name and self.arity == other.arity
        return False

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

class OperatorCollection:
    """Stores the operators that will be passed to ModelSetup."""

    def __init__(self, *input):
        self.operator_classes_dict = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_classes_dict

    def items(self):
        yield from self.operator_classes_dict.items()

    def add_operator(self, input):
        """Input is either an operator class (of type 'type') or a list of operator classes."""
        if (
            isinstance(input, list)
            or isinstance(input, tuple)
            or isinstance(input, set)
        ):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            self.operator_classes_dict[input.name] = input

    def __getitem__(self, value):
        return self.operator_classes_dict[value]


class ModelSetup:
    """Stores what is needed to find a Z3 model and passed to ModelStructure."""

    def __init__(
        self,
        semantics,
        operator_collection,
        infix_premises,
        infix_conclusions,
        proposition_class,
        max_time=1,
        contingent=False,
        non_null=True,
        disjoint=False,
    ):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.operators = {
            op_name: op_class(semantics)
            for (op_name, op_class) in operator_collection.items()
        }
        self.proposition_class = proposition_class
        self.max_time = max_time
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint

        self.prefix_premises = [self.prefix(prem) for prem in infix_premises]
        self.prefix_conclusions = [self.prefix(con) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = self.find_subsentences(prefix_sentences)
        self.all_sentence_letters = self.find_sentence_letters(prefix_sentences)

        self.frame_constraints = semantics.frame_constraints
        self.model_constraints = []
        for sl in self.all_sentence_letters:
            self.model_constraints.extend(
                proposition_class.proposition_constraints(self, sl)
            )
        self.premise_constraints = [
            semantics.premise_behavior(prem, semantics.main_world)
            for prem in self.prefix_premises
        ]
        self.conclusion_constraints = [
            semantics.conclusion_behavior(conc, semantics.main_world)
            for conc in self.prefix_conclusions
        ]
        self.all_constraints = (
            self.frame_constraints
            + self.model_constraints
            + self.premise_constraints
            + self.conclusion_constraints
        )

    def __str__(self):
        """useful for using model-checker in a python file"""
        return f"ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions}"

    def print_enumerate(self, output=sys.__stdout__):
        """prints the premises and conclusions with numbers"""
        infix_premises = self.infix_premises
        infix_conclusions = self.infix_conclusions
        start_con_num = len(infix_premises) + 1
        if self.infix_premises:
            if len(self.infix_premises) < 2:
                print("Premise:", file=output)
            else:
                print("Premises:", file=output)
            for index, sent in enumerate(self.infix_premises, start=1):
                print(f"{index}. {sent}", file=output)
        if infix_conclusions:
            if len(infix_conclusions) < 2:
                print("\nConclusion:", file=output)
            else:
                print("\nConclusions:", file=output)
            for index, sent in enumerate(infix_conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)

    def find_sentence_letters(self, prefix_sentences):
        """Finds all the sentence letters in a list of input sentences, in prefix form.
        Returns as a list of AtomSorts with no repeats (sorted for consistency).
        used in find_all_constraints (feeds into find_prop_constraints) and StateSpace __init__.
        """
        sentence_letters = set()
        for prefix_input in prefix_sentences:
            sentence_letters.update(sentence_letters_in_compound(prefix_input))
        return list(sentence_letters)
        # TODO: need to make a dictionary to sort the list returned above

    def find_subsentences(self, prefix_sentences):
        """take a set of prefix sentences and returns a set of all subsentences"""
        all_subsentences = []
        for prefix_sent in prefix_sentences:
            all_prefix_subs = subsentences_of(prefix_sent)
            all_subsentences.extend(all_prefix_subs)
        return repeats_removed(all_subsentences)

    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        return parse_expression(tokens, self)


class ModelStructure:
    """Solves and stores the Z3 model for an instance of ModelSetup."""

    def __init__(self, model_setup):
        timeout, z3_model_status, z3_model, z3_model_runtime = self.solve(model_setup)
        self.model_setup = model_setup
        self.timeout = timeout
        self.z3_model = z3_model
        self.model_status = z3_model_status
        self.model_runtime = z3_model_runtime

        self.N = model_setup.semantics.N
        self.all_subsentences = model_setup.all_subsentences
        prefix_sentences = model_setup.prefix_premises + model_setup.prefix_conclusions
        self.sentence_letters = all_sentence_letters(prefix_sentences)

        self.all_bits = find_all_bits(self.N)
        if isinstance(z3_model, z3.ModelRef):  # Check if z3_model is a ModelRef
            self.poss_bits = [
                bit
                for bit in self.all_bits
                if bool(z3_model.evaluate(model_setup.semantics.possible(bit)))
            ]
            self.world_bits = [
                bit
                for bit in self.poss_bits
                if bool(z3_model.evaluate(model_setup.semantics.is_world(bit)))
            ]
            self.main_world = z3_model[model_setup.semantics.main_world]
        else:
            # B: not sure whether to raise error to kill process or print
            # raise ValueError(f"Unexpected z3_model type: {type(z3_model)}")
            print(f"Unexpected z3_model type: {type(z3_model)}")
            self.poss_bits = []
            self.world_bits = []
            self.main_world = None
        self.all_propositions = {}
        self.premise_propositions = [
            model_setup.proposition_class(prefix_sent, self)
            # B: what if there are repeats in prefix_premises?
            for prefix_sent in model_setup.prefix_premises
        ]
        self.conclusion_propositions = [
            model_setup.proposition_class(prefix_sent, self)
            # B: what if there are repeats in prefix_premises?
            for prefix_sent in model_setup.prefix_conclusions
        ]

    def solve(self, model_setup):
        solver = Solver()
        solver.add(model_setup.all_constraints)
        solver.set("timeout", int(model_setup.max_time * 1000))  # time in seconds
        try:
            model_start = time.time()  # start benchmark timer
            result = solver.check()
            model_end = time.time()  # end benchmark timer
            model_runtime = round(model_end - model_start, 4)
            if result == sat:
                return False, True, solver.model(), model_runtime
            if solver.reason_unknown() == "timeout":
                return True, False, None, model_runtime
            return False, False, solver.unsat_core(), model_runtime
        except RuntimeError as e:  # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, False, None, None

    def infix(self, prefix_sent):
        """Takes a sentence in prefix notation and translates it to infix notation"""
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
        N = self.model_setup.semantics.N
        sentence_letters = self.sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {bitvec_to_substates(main_world, N)}",
            file=output,
        )
        # true_in_eval = set()
        # for sent in sentence_letters:
        #     for bit in self.all_bits:
        #         ver_bool = self.model_setup.verify(bit, self.z3_model[sent])
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
    #     structure = self.model_setup
    #     setup = self.model_setup
    #     if print_constraints_bool:
    #         structure.print_constraints(setup.frame_constraints, 'FRAME', output)
    #         structure.print_constraints(setup.prop_constraints, 'PROPOSITION', output)
    #         structure.print_constraints(setup.premise_constraints, 'PREMISE', output)
    #         structure.print_constraints(setup.conclusion_constraints, 'CONCLUSION', output)
    #     print(f"Run time: {self.model_runtime} seconds\n", file=output)

    # def save_to(self, cons_include, print_impossible, output):
    #     """append all elements of the model to the file provided"""
    #     constraints = self.model_setup.constraints
    #     self.print_all(print_impossible, output)
    #     self.model_setup.build_test_file(output)
    #     if cons_include:
    #         print("# Satisfiable constraints", file=output)
    #         # TODO: print constraint objects, not constraint strings
    #         print(f"all_constraints = {constraints}", file=output)

    def print_states(self, print_impossible=False, output=sys.__stdout__):
        """print all fusions of atomic states in the model
        print_impossible is a boolean for whether to print impossible states or not
        first print function in print.py"""
        N = self.model_setup.semantics.N
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
            if print_impossible:
                print(
                    f"  {WHITE}{bin_rep} = {MAGENTA}{state} (impossible){RESET}",
                    file=output,
                )

    def print_all(self, print_impossible=False, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        N = self.model_setup.semantics.N
        print(f"\nThere is a {N}-model of:\n", file=output)
        self.model_setup.print_enumerate(output)
        self.print_states(print_impossible, output)
        self.print_evaluation(output)
        # self.print_inputs_recursively(print_impossible, output) # missing

    # M: looking at find_complex_proposition, it looks like we can employ a similar strategy
    # to the operators bouncing back and forth with the semantics, except this time we
    # bounce back and forth with wherever the definition of a proposition is
    # B: yes, there will definitely also be some bouncing back and forth. whatever happens in
    # recursive_print will get divided between operators
