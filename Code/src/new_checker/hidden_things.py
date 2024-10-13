from z3 import (
    Const,
    DeclareSort,
    sat,
    Solver,
    simplify,
)

import time

import inspect

from hidden_helpers import (
    AtomSort,
    parse_expression,
    remove_repeats,
    sentence_letters_in_compound,
    subsentences_of,
    all_sentence_letters,
    find_all_bits,
    bitvec_to_substates,
    int_to_binary,
    not_implemented_string,
    pretty_set_print,
    flatten,

)

import sys

from syntactic import Sentence

# B: I'm assuming this will need to be included to activate sentence letters if this
# happens separately from finding sentence letters (if separating that is good)
AtomSort = DeclareSort("AtomSort")

class PropositionDefaults:
    """Defaults inherited by every proposition."""

    def __init__(self, prefix_sentence, model_structure):
        if self.__class__ == PropositionDefaults:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))
        self.prefix_sentence = prefix_sentence
        self.name = model_structure.infix(prefix_sentence)
        self.model_structure = model_structure
        self.N = model_structure.N
        self.semantics = model_structure.model_setup.semantics
        self.contingent = model_structure.model_setup.contingent
        self.non_null = model_structure.model_setup.non_null
        self.disjoint = model_structure.model_setup.disjoint
        self.print_impossible = model_structure.model_setup.print_impossible
        self.model_structure.all_propositions[self.name] = self
        self.verifiers, self.falsifiers = None, None # to avoid linter errors in print_proposition
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
        N = self.model_structure.model_setup.semantics.N
        # Linter: cannot access attribute "truth_value_at" for class "Proposition*"
        # M: the easiest solution would be to move verifiers to the init of this
        # or have a dummy set of verifiers here
        truth_value = self.truth_value_at(eval_world) 
        possible = self.model_structure.model_setup.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers # Linter: ditto for "verifiers"
            if z3_model.evaluate(possible(bit))
            or self.print_impossible
        }
        ver_prints = pretty_set_print(ver_states) if ver_states else '∅'
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers # Linter: ditto for "falsifiers"
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


class Operator:
    """Defaults inherited by every operator."""

    name = None
    arity = None
    primitive = True # a small piece of the avoid DefinedOperator recursion soln

    def __init__(self, semantics):
        if self.__class__ == Operator:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))
        if self.name is None or self.arity is None:
            op_class = self.__class__.__name__
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
    
class DefinedOperator(Operator):
    primitive = False

    def derived_definition(self):
        return []

    def __init__(self, semantics, loop_check=True):
        super().__init__(semantics)

        # check self is an arg of derived_definition
        op_subclass = self.__class__
        args_without_self = inspect.signature(self.derived_definition).parameters # parameters besides self in derived_definition
        args_with_self = inspect.signature(op_subclass.derived_definition).parameters # params above plus 'self'
        if 'self' not in args_with_self:
            raise ValueError(f"self should be an argument of {op_subclass.__name__}'s "
                             "derived_definition method (and it should go unused).")
        # from now on, can assume 'self' is an argument of derived_definition. 

        # check if derived_definition is implemented (ie is not default)
        elif len(args_with_self) == 1 and 'self' in args_with_self:
            raise NameError(
                f"Derived operator class {op_subclass.__name__} does not have an implemented "
                f"derived_definition method. ")
        
        # check for arity match between self.arity and derived_def num args (excluding self)
        derived_def_num_args = len(args_without_self)
        op_name = op_subclass.__name__
        mismatch_arity_msg = (
            f"the specified arity of value {self.arity} for the DerivedOperator class {op_name} "
            f"does not match the number of arguments (excluding 'self') for {op_name}'s derived_"
            f"definition property ({derived_def_num_args} non-self arguments currently.)")
        assert self.arity == derived_def_num_args, mismatch_arity_msg

        # check for DefinedOperators defined in terms of each other
        sample_derived_def = self.derived_definition(*(derived_def_num_args * ("a",)))
        ops_in_def = [elem for elem in flatten(sample_derived_def) if isinstance(elem, type)]
        self.defined_operators_in_definition = [op for op in ops_in_def if not op.primitive]
        if loop_check:
            for def_opcls in self.defined_operators_in_definition:
                if self.__class__ in def_opcls('dummy sem', False).defined_operators_in_definition:
                    ermsg = (f"{op_name} and {def_opcls.__name__} are defined in terms of each "
                            f"other. Please edit their derived_definition methods to avoid this.")
                    raise RecursionError(ermsg)

    def activate_prefix_definition(self, unactivated_prefix_def):
        '''Helper for get_derived_prefix_form. Takes a sentence in prefix notation
        returned by the derived_definition property of the DerivedOperator subclass
        and returns one with every Operator in that definition instantiated (since
        in the derived_definition operators are defined without an instantiation.)'''
        new_prefix_def = []
        for elem in unactivated_prefix_def:
            if isinstance(elem, type):
                new_prefix_def.append(elem(self.semantics))
            elif isinstance(elem, list):
                new_prefix_def.append(self.activate_prefix_definition(elem))
            else: # so an instantiated operator or a sentence letter
                new_prefix_def.append(elem)
        return new_prefix_def

    def get_derived_prefix_form(self, args):
        '''given a set of arguments, returns a prefix sentence that correctly
        puts them into the derived definition of the derived operator
        returns a sentence in prefix notation (list of AtomSorts and Operator instances)'''
        unact_prefix_def = self.derived_definition(*args)
        return DefinedOperator.activate_prefix_definition(self, unact_prefix_def)
    
    def true_at(self, *args_and_eval_world):
        args, eval_world = args_and_eval_world[0:-1], args_and_eval_world[-1]
        prefix_def = self.get_derived_prefix_form(args)
        operator, new_args = prefix_def[0], prefix_def[1:]
        return operator.true_at(*new_args, eval_world)
    
    def false_at(self, *args_and_eval_world):
        args, eval_world = args_and_eval_world[0:-1], args_and_eval_world[-1]
        prefix_def = self.get_derived_prefix_form(args)
        operator, new_args = prefix_def[0], prefix_def[1:]
        return operator.false_at(*new_args, eval_world)
    
    def find_verifiers_and_falsifiers(self, *argprops):
        prefix_args = [prop.prefix_sentence for prop in argprops]
        prefix_def = self.get_derived_prefix_form(prefix_args)
        prop_class, model_structure = argprops[0].__class__, argprops[0].model_structure
        derived_subprops = (prop_class(pfsent, model_structure) for pfsent in prefix_def[1:])
        operator = prefix_def[0]
        return operator.find_verifiers_and_falsifiers(*derived_subprops)


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

    # B: the idea here is to rely on the instances of Sentences since these do
    # not depend on the semantics or operator_collection. the idea is to gather
    # the sentence_letters, subsentences, and operators with the unpack()
    # method, using these to generate and store the other attributes of this
    # class by appealing to the semantics and operator_collection as needed.

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
        print_impossible=False,
    ):

        # Store inputs
        self.semantics = semantics
        self.operator_collection = operator_collection
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.proposition_class = proposition_class

        # Store settings
        self.max_time = max_time
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint
        self.print_impossible = print_impossible

        # Create Sentence instances for premises and conclusions
        self.premises = {
            prem : Sentence(prem)
            for prem in infix_premises
        }
        self.conclusions = {
            con : Sentence(con)
            for con in infix_conclusions
        }

        # Collect from premises and conclusions and unpack
        inputs = list(self.premises.values()) + list(self.conclusions.values())
        letters, ops, subs = self.unpack(inputs)
        # B: note there is some redundancy with what goes on in all_subsentences
        self.all_sentence_letters = [Const(letter, AtomSort) for letter in letters]

        # B: I'm wondering if it makes sense to only add the operators that
        # occur in the premises and conclusion since they are provided in each
        # instance of the Sentence class. not totally sure how to do that.
        self.operators = {
            op_name: op_class(semantics)
            for (op_name, op_class) in operator_collection.items()
        }
        # B: I considered excluding sentence letters and premises and conclusions to avoid
        # redundancy, renaming the result 'intermediate_sentences'. that way all_subsentences
        # would be the result of combining sentence_letters, intermediate_sentences, premises,
        # and conclusions.
        self.all_subsentences = [self.apply_operator(sub) for sub in subs]

        # B: I'm not getting the right values for the prefix premises below despite
        # the tests the prefix premises working out well in the definition of Sentences
        print("TEST ONLY INFIX PREM", infix_premises)
        premises = [prem.prefix_sentence for prem in self.premises.values()]
        print("TEST ONLY PREFIX PREM", premises)
        self.just_prefix_premises = [self.apply_operator(prem.prefix_sentence[0]) for prem in self.premises.values()]
        print("TEST PREM", self.just_prefix_premises)
        self.just_prefix_conclusions = [self.apply_operator(con.prefix_sentence[0]) for con in self.conclusions.values()]
        print("TEST CON", self.just_prefix_conclusions)

        # B: to be replaced be relying on the instances of the Sentence class as above
        # once the just_prefix_premises and just_prefix_conclusions agree with the below
        self.prefix_premises = [self.prefix(prem) for prem in infix_premises]
        print("TARTGET PREM", self.prefix_premises)
        self.prefix_conclusions = [self.prefix(con) for con in infix_conclusions]
        print("TARTGET CON", self.prefix_conclusions)

        # Use semantics to generate and store Z3 constraints
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

    def apply_operator(self, prefix_sentence):
        # print("TEST APPLY PREFIX", prefix_sentence)
        if len(prefix_sentence) == 1:
            atom = prefix_sentence[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self.operators[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(prefix_sentence[0], AtomSort)]
        op = prefix_sentence.pop(0)
        # print("PRINT APPLY OP", op)
        activated = [self.apply_operator(arg) for arg in prefix_sentence]
        activated.insert(0, self.operators[op])
        return activated 

    def unpack(self, sentences):
        letters = set()
        # letters = [] # if sentence_letters are lists of length 1
        ops = set()
        subs = []
        for sent in sentences:
            # letters.extend(sent.sentence_letters) # if sentence_letters are lists of length 1
            letters.update(sent.sentence_letters)
            ops.update(sent.operators)
            subs.extend(sent.subsentences)
        # sorted_sentence_letters = remove_repeats(letters) # if sentence_letters are lists of length 1
        sorted_sentence_letters = sorted(list(letters), key=lambda x: str(x))
        sorted_operators = sorted(list(ops), key=lambda x: str(x))
        sorted_subsentences = remove_repeats(subs)
        return sorted_sentence_letters, sorted_operators, sorted_subsentences

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
        sorted_sentence_letters = sorted(list(sentence_letters), key=lambda x: str(x))
        return sorted_sentence_letters
        # B: this seems to be working but worth checking; old is below
        # return list(sentence_letters)

    def find_subsentences(self, prefix_sentences):
        """take a set of prefix sentences and returns a set of all subsentences"""
        all_subsentences = []
        for prefix_sent in prefix_sentences:
            all_prefix_subs = subsentences_of(prefix_sent)
            all_subsentences.extend(all_prefix_subs)
        return remove_repeats(all_subsentences)

    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        return parse_expression(tokens, self)


class ModelStructure:
    """Solves and stores the Z3 model for an instance of ModelSetup."""

    def __init__(self, model_setup):
        timeout, z3_model_status, z3_model, z3_model_runtime = self.solve(model_setup)
        # print("TEST", z3_model_status)
        self.model_setup = model_setup
        self.timeout = timeout
        self.z3_model = z3_model if z3_model_status else None
        self.unsat_core = z3_model if not z3_model_status else None
        self.model_status = z3_model_status
        self.model_runtime = z3_model_runtime
        self.print_impossible = model_setup.print_impossible

        self.N = model_setup.semantics.N
        self.all_subsentences = model_setup.all_subsentences
        prefix_sentences = model_setup.prefix_premises + model_setup.prefix_conclusions
        self.sentence_letters = all_sentence_letters(prefix_sentences)
        self.all_bits = find_all_bits(self.N)
        if not z3_model_status:
            self.poss_bits, self.world_bits, self.main_world = None, None, None
            self.all_propositions, self.premise_propositions = None, None
            self.conclusion_propositions = None
            return
        # if isinstance(z3_model, z3.ModelRef):  # Check if z3_model is a ModelRef
        self.poss_bits = [
            bit
            for bit in self.all_bits
            if bool(z3_model.evaluate(model_setup.semantics.possible(bit)))
            # LINTER: cannot access attribute "evaluate" for class "AstVector"
        ]
        self.world_bits = [
            bit
            for bit in self.poss_bits
            if bool(z3_model.evaluate(model_setup.semantics.is_world(bit)))
            # LINTER: cannot access attribute "evaluate" for class "AstVector"
        ]
        self.main_world = z3_model[model_setup.semantics.main_world]
        # LINTER: object of type "None" is not subscriptable
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
        # else: # M: this was being raised when no model was being found
        #     # B: not sure whether to raise error to kill process or print
        #     raise ValueError(f"Unexpected z3_model type: {type(z3_model)}")
        #     print(f"Unexpected z3_model type: {type(z3_model)}")
        #     self.poss_bits = []
        #     self.world_bits = []
        #     self.main_world = None

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

    def print_states(self, output=sys.__stdout__):
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
            if self.print_impossible:
                print(
                    f"  {WHITE}{bin_rep} = {MAGENTA}{state} (impossible){RESET}",
                    file=output,
                )

    def rec_print(self, prop_obj, eval_world, indent):
        prop_obj.print_proposition(eval_world, indent)
        if len(prop_obj.prefix_sentence) == 1:
            return
        sub_prefix_sents = prop_obj.prefix_sentence[1:]
        sub_infix_sentences = (self.infix(sub_prefix) for sub_prefix in sub_prefix_sents)
        subprops = (self.all_propositions[infix] for infix in sub_infix_sentences)
        # LINTER: says for above: Object of type "None" is not subscriptable
        for subprop in subprops:
            self.rec_print(subprop, eval_world, indent + 1)

    def print_inputs_recursively(self, output):
        """does rec_print for every proposition in the input propositions
        returns None"""
        initial_eval_world = self.main_world
        infix_premises = self.model_setup.infix_premises
        infix_conclusions = self.model_setup.infix_conclusions
        start_con_num = len(infix_premises) + 1
        if self.premise_propositions:
            if len(infix_premises) < 2:
                print("INTERPRETED PREMISE:\n", file=output)
            else:
                print("INTERPRETED PREMISES:\n", file=output)
            for index, input_prop in enumerate(self.premise_propositions, start=1):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, 1)
                # input_prop.print_proposition(initial_eval_world, 1)
                print(file=output)
        if self.conclusion_propositions:
            if len(infix_conclusions) < 2:
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
        N = self.model_setup.semantics.N
        if self.model_status:
            print(f"\nThere is a {N}-model of:\n", file=output)
            self.model_setup.print_enumerate(output)
            self.print_states(output)
            self.print_evaluation(output)
            self.print_inputs_recursively(output)
            return
        print(f"\nThere is no {N}-model of:\n")
        self.model_setup.print_enumerate(output)
