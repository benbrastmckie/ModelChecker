"""
file defines model structure class given a Z3 model
"""

from string import Template
import time
import sys
from z3 import (
    Function,
    BitVecSort,
    BoolSort,
    BitVec,
    BitVecVal
)
# from model_checker.semantics import ( # for packaging
from semantics import (
    make_constraints,
    solve_constraints,
)
# from model_checker.model_definitions import ( # for packaging
from model_definitions import (
    find_compatible_parts,
    atomic_propositions_dict,
    coproduct,
    find_all_bits,
    find_max_comp_ver_parts,
    find_null_bit,
    find_poss_bits,
    find_world_bits,
    prefix_combine,
    pretty_set_print,
    find_true_and_false_in_alt,
    product,
    bit_part,
    bitvec_to_substates,
    int_to_binary,
    infix_combine,
    find_subsentences_of_kind,
    is_counterfactual,
    is_modal,

)
# from model_checker.syntax import (
from syntax import (
    AtomSort,
    Infix,
    Prefix,
)

inputs_template = Template(
'''Run time: ${runtime} seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

# input sentences
premises = ${premises}
conclusions = ${conclusions}

# number of atomic states
N = ${N}

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to save output
save_bool = False
'''
)
# NOTE: include below in the template above when working
# # use constraints to find models in stead of premises and conclusions
# use_constraints_bool = False


class Uninitalized:
    """class for uninitalized attributes"""

    def __init__(self, name):
        self.name = name

    def __iter__(self):
        raise AttributeError(
            f"cannot iterate through {self.name} because it isnt initialized")
    
    def __getitem__(self):
        raise AttributeError(
            f"cannot get an item from {self.name} because it isnt initialized")

    def __str__(self):
        return f"{self.name} (uninitialized)"


class ModelStructure:
    """self.premises is a list of prefix sentences
    self.conclusions is a list of prefix sentences
    self.input_sentences is the combination of self.premises and self.conclusions with the
    conclusions negated
    self.sentence letters is a list of atomic sentence letters (each of sort AtomSort)
    self.constraints is a list (?) of constraints
    everything else is initialized as None"""

    def __init__(self, infix_premises, infix_conclusions, verify, falsify, possible, assign, N, w):
        self.verify = verify
        self.falsify = falsify
        self.possible = possible
        self.assign = assign
        self.N = N
        self.w = w # NOTE: this isn't needed by the user, and is only used once in this file

        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.infix_sentences = infix_combine(infix_premises, infix_conclusions)
        self.prefix_premises = [Prefix(prem) for prem in infix_premises]
        self.prefix_conclusions = [Prefix(con) for con in infix_conclusions]
        self.prefix_sentences = prefix_combine(self.prefix_premises, self.prefix_conclusions)

        find_constraints_func = make_constraints(verify, falsify, possible, assign, N, w)
        consts, sent_lets = find_constraints_func(self.prefix_sentences)
        self.sentence_letters = sent_lets
        self.constraints = consts
        ext, modal, cf, altogether = find_subsentences_of_kind(self.prefix_sentences, 'all')
        
        self.extensional_subsentences = ext
        self.counterfactual_subsentences = cf
        self.modal_subsentences = modal
        self.all_subsentences = altogether # in prefix form
        # initialize yet-undefined attributes
        self.model_status = Uninitalized("model_status")
        self.model = Uninitalized("model")
        self.model_runtime = Uninitalized("model_runtime")
        self.null_bit = Uninitalized("null_bit")
        self.all_bits = Uninitalized("all_bits")
        self.poss_bits = Uninitalized("poss_bits")
        self.world_bits = Uninitalized("world_bits")
        self.main_world = Uninitalized("eval_world")
        self.atomic_props_dict = Uninitalized("atomic_props_dict")
        self.extensional_propositions = Uninitalized("extensional_propositions")
        self.modal_propositions = Uninitalized("modal_propositions")
        self.counterfactual_propositions = Uninitalized("counterfactual_propositions")
        self.all_propositions = Uninitalized("all_propositions")
        self.premise_propositions = Uninitalized("premise_propositions")
        self.conclusion_propositions = Uninitalized("premise_propositions")

    def solve(self):
        """solves the model, returns None
        self.model is the ModelRef object resulting from solving the model
        self.model_runtime is the runtime of the model as a float
        self.all_bits is a list of all bits (each of sort BitVecVal)
        self.poss_bits is a list of all possible bits
        self.world_bits is a lsit of all world bits
        self.main_world is the eval world (as a BitVecVal)
        self.atomic_props_dict is a dictionary with keys AtomSorts and keys (V,F)
        """
        model_start = time.time()  # start benchmark timer
        solved_model_status, solved_model = solve_constraints(self.constraints)
        model_end = time.time()
        model_total = round(model_end - model_start, 4)
        self.model_status = solved_model_status
        self.model = solved_model
        self.model_runtime = model_total
        if self.model_status:
            self.null_bit = find_null_bit(self.N) # why do we have this?
            self.all_bits = find_all_bits(self.N)
            self.poss_bits = find_poss_bits(self.model, self.all_bits, self.possible)
            self.world_bits = find_world_bits(self.poss_bits)
            self.main_world = self.model[self.w]
            self.atomic_props_dict = atomic_propositions_dict(self)
            self.extensional_propositions = [Extensional(ext_subsent, self, self.main_world)
                                            for ext_subsent in self.extensional_subsentences]
            self.counterfactual_propositions = [Counterfactual(cf_subsent, self, self.main_world)
                                            for cf_subsent in self.counterfactual_subsentences]
            self.modal_propositions = [Modal(modal_subsent, self, self.main_world)
                                        for modal_subsent in self.modal_subsentences]
            self.all_propositions = (self.extensional_propositions +
                                     self.counterfactual_propositions + self.modal_propositions)
            self.premise_propositions = self.find_propositions(self.prefix_premises)
            self.conclusion_propositions = self.find_propositions(self.prefix_conclusions)
            # TODO: just missing the which-sentences-true-in-which-worlds

    def find_alt_bits(self, ext_prop_verifier_bits, comparison_world=None):
        """
        Finds the alternative bits given verifier bits of an extensional proposition,
        possible states, worlds, and the evaluation world.
        Used in evaluate_cf_expression() and rec_print().
        """
        if comparison_world is None:
            comparison_world = self.main_world
        alt_bits = set()
        for ver in ext_prop_verifier_bits:
            comp_parts = find_compatible_parts(ver, self.poss_bits, comparison_world)
            max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
            for world in self.world_bits:
                if not bit_part(ver, world):
                    continue
                for max_ver in max_comp_ver_parts:
                    if bit_part(max_ver, world) and world.sexpr():
                        alt_bits.add(world)
                        break  # to return to the second for loop over world_bits
        return alt_bits

    def evaluate_modal_expr(self, prefix_modal, eval_world):
        '''evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
        used to initialize Counterfactuals
        returns a bool representing whether the counterfactual is true at the world or not'''
        op, argument = prefix_modal[0], prefix_modal[1]
        if is_modal(argument):
            if self.evaluate_modal_expr(prefix_modal) is True: # ie, verifiers is null state
                return True # both Box and Diamond will return true, since verifiers is not empty
            return False
        if 'Diamond' in op:
            # TODO: linter error: uninitalized is not iterable  "__iter__" does not return object
            for world in self.world_bits:
                if world in self.find_complex_proposition(argument, eval_world)[0]:
                    return True
            return False
        if 'Box' in op:
            # TODO: linter error: uninitalized is not iterable  "__iter__" does not return object
            for world in self.world_bits:
                if world not in self.find_complex_proposition(argument, eval_world)[0]:
                    return False
            return True

    def evaluate_cf_expr(self, prefix_cf, eval_world):
        """evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
        used to initialize Counterfactuals
        returns a bool representing whether the counterfactual is true at the world or not
        """
        op, antecedent_expr, consequent_expr = prefix_cf[0], prefix_cf[1], prefix_cf[2]
        assert "boxright" in op, f"{prefix_cf} is not a counterfactual!"
        ant_prop = self.find_proposition_object(antecedent_expr, ext_only=True)
        ant_alts_to_eval_world = self.find_alt_bits(ant_prop['verifiers'], eval_world)
        for u in ant_alts_to_eval_world:
            # QUESTION: why is string required? Is Z3 removing the lists?
            if is_counterfactual(consequent_expr):
                if self.evaluate_cf_expr(consequent_expr, u) is False:
                    return False
            elif str(consequent_expr) not in str(find_true_and_false_in_alt(u, self)[0]):
                return False
        return True
    
    def true_and_false_worlds_for_cf(self, complex_cf_sent):
        '''used in find_complex_proposition'''
        worlds_true_at, worlds_false_at = set(), set()
        for world in self.world_bits:
            if self.evaluate_cf_expr(complex_cf_sent, world):
                worlds_true_at.add(world)
                continue
            worlds_false_at.add(world)
        return (worlds_true_at, worlds_false_at)

    def find_complex_proposition(self, complex_sentence, eval_world):
        """sentence is a sentence in prefix notation
        For a given complex proposition, returns the verifiers and falsifiers of that proposition
        given a solved model
        for a counterfactual, it'll just give the worlds it's true at and worlds it's not true at
        """
        if not self.atomic_props_dict:
            raise ValueError(
                "There is nothing in atomic_props_dict yet. Have you actually run the model?"
            )
        if len(complex_sentence) == 1:
            sent = complex_sentence[0]
            # TODO: linter error: expected 0 arguments
            return self.atomic_props_dict[sent]
        op = complex_sentence[0]
        Y = complex_sentence[1]
        if "neg" in op:
            Y_V = self.find_complex_proposition(Y, eval_world)[0]
            Y_F = self.find_complex_proposition(Y, eval_world)[1]
            return (Y_F, Y_V)
        null_state = {BitVecVal(0,self.N)}
        if 'Box' in op:
            if self.evaluate_modal_expr(complex_sentence, eval_world):
                return (null_state, set())
            return (set(), null_state)
        if 'Diamond' in op:
            if self.evaluate_modal_expr(complex_sentence, eval_world):
                return (set(), null_state)
            return (null_state, set())
        Z = complex_sentence[2]
        Y_V = self.find_complex_proposition(Y, eval_world)[0]
        Y_F = self.find_complex_proposition(Y, eval_world)[1]
        Z_V = self.find_complex_proposition(Z, eval_world)[0]
        Z_F = self.find_complex_proposition(Z, eval_world)[1]
        if "wedge" in op:
            return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
        if "vee" in op:
            return (coproduct(Y_V, Z_V), product(Y_F, Z_F))
        if "leftrightarrow" in op:
            return (
                product(coproduct(Y_F, Z_V), coproduct(Y_V, Z_F)),
                coproduct(product(Y_V, Z_F), product(Y_F, Z_V)),
            )
        if "rightarrow" in op:
            return (coproduct(Y_F, Z_V), product(Y_V, Z_F))
        if "boxright" in op:
            # NOTE: change to null_state, nothing. 
            # Would a counterfactual be true at a world w
            # (and thus its verifiers should be {null_state})
            # just in case the counterfactual is true at the current world of evaluation?

            if eval_world in self.true_and_false_worlds_for_cf(complex_sentence)[0]:
                return (null_state, set())
            return (set(), null_state)
            # worlds_true_at, worlds_false_at = set(), set()
            # for world in self.world_bits:
            #     if self.evaluate_cf_expr(complex_sentence, world):
            #         worlds_true_at.add(world)
            #         continue
            #     worlds_false_at.add(world)
            # return (worlds_true_at, worlds_false_at)
        raise ValueError(f"Don't know how to handle {op} operator")

    def find_proposition_object(self, prefix_expression, ext_only=False):
        """given a prefix sentence, finds the Proposition object in the model that corresponds
        to it. Can optionally search through only the extensional sentences
        returns a Proposition object"""
        search_list = self.extensional_propositions
        if ext_only is False:
            search_list = self.all_propositions
        for prop in search_list:
            if prop["prefix expression"] == prefix_expression:
                return prop
        raise ValueError(
            f"there is no proposition with prefix expression {prefix_expression}")

    def find_propositions(self, sentences):
        """finds all the Proposition objects in a ModelStructure
        that correspond to the input sentences.
        returns them as a list"""
        propositions = []
        for sent in sentences:
            propositions.append(self.find_proposition_object(sent))
        return propositions

    def print_states(self, output=sys.__stdout__):
        """print all fusions of atomic states in the model
        first print function in print.py"""
        N = self.N
        print("\nPossible states:", file=output)  # Print states
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, N)
            bin_rep = (
                bit.sexpr()
                if N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), N)
            )
            if bit in self.world_bits:
                print(f"  {bin_rep} = {state} (world)", file=output)
                continue
            # NOTE: can probably delete the line below
            # elif bool(self.model.evaluate(self.possible(bit))):
            if bit in self.poss_bits:
                print(f"  {bin_rep} = {state}", file=output)
                continue

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        # TODO: all this seems to do is print the sentences true/false in each world.
        # can this be simplified? might it make sense to store sentence letters true
        # at the designated world and the sentence letters false at the designated
        # world in the class? then those could be easily called here.
        N = self.N
        print(
            f"\nThe evaluation world is {bitvec_to_substates(self.main_world, N)}:",
            file=output,
        )
        true_in_eval = set()
        for sent in self.sentence_letters:
            for bit in self.all_bits:
                # TODO: linter error: expected 0 positional arguments
                ver_bool = self.verify(bit, self.model[sent])
                part_bool = bit_part(bit, self.main_world)
                # TODO: linter error: invalid conditional operand band-aid fixed with bool
                if bool(self.model.evaluate(ver_bool) and part_bool):
                    true_in_eval.add(sent)
                    break  # exits the first for loop
        false_in_eval = {R for R in self.sentence_letters if not R in true_in_eval}
        if true_in_eval:
            true_eval_list = sorted([str(sent) for sent in true_in_eval])
            true_eval_string = ", ".join(true_eval_list)
            print(
                f"  {true_eval_string}  (True in {bitvec_to_substates(self.main_world, N)})",
                file=output,
            )
        if false_in_eval:
            false_eval_list = sorted([str(sent) for sent in false_in_eval])
            false_eval_string = ", ".join(false_eval_list)
            print(
                f"  {false_eval_string}  (False in {bitvec_to_substates(self.main_world, N)})",
                file=output,
            )
        print(file=output)

    def print_constraints(self, consts, output=sys.__stdout__):
        """prints constraints in an numbered list"""
        if self.model_status:
            print("Satisfiable constraints:\n", file=output)
        else:
            print("Unsatisfiable core constraints:\n", file=output)
        for index, con in enumerate(consts, start=1):
            print(f"{index}. {con}\n", file=output)
            # print(f"Constraints time: {time}\n")

    def rec_print(self, prop_obj, world_bit, output, indent=0):
        """recursive print function (previously print_sort)
        returns None"""
        N = self.N
        prop_obj.print_verifiers_and_falsifiers(world_bit, indent, output)
        if str(prop_obj) in [str(atom) for atom in self.sentence_letters]:
            return
        prefix_expr = prop_obj["prefix expression"]
        op = prefix_expr[0]
        first_subprop = self.find_proposition_object(prefix_expr[1])
        indent += 1 # begin subcases, so indent
        if "neg" in op:
            self.rec_print(first_subprop, world_bit, output, indent)
            return
        if 'Diamond' in op or 'Box' in op:
            # TODO: linter error: uninitalized is not iterable  "__iter__"
            # method does not return an object
            for u in self.world_bits:
                self.rec_print(first_subprop, u, output, indent)
            return
        left_subprop = first_subprop
        right_subprop = self.find_proposition_object(prefix_expr[2])
        if "boxright" in op:
            assert (
                left_subprop in self.extensional_propositions
            ), "{prop} not a valid cf because antecedent {left_subprop} is not extensional"
            left_subprop_vers = left_subprop['verifiers']
            phi_alt_worlds_to_world_bit = self.find_alt_bits(left_subprop_vers, world_bit)
            alt_worlds_as_strings = {bitvec_to_substates(u,N) for u in phi_alt_worlds_to_world_bit}
            self.rec_print(left_subprop, world_bit, output, indent)
            print(
                f'{"  " * indent}'
                f'{left_subprop}-alternatives to {bitvec_to_substates(world_bit, N)} = '
                f'{pretty_set_print(alt_worlds_as_strings)}',
                file=output
            )
            indent += 1
            for u in phi_alt_worlds_to_world_bit:
                self.rec_print(right_subprop, u, output, indent)
            return
        self.rec_print(left_subprop, world_bit, output, indent)
        self.rec_print(right_subprop, world_bit, output, indent)

    def print_inputs_recursively(self, output):
        """does rec_print for every proposition in the input propositions
        returns None"""
        initial_eval_world = self.main_world
        start_con_num = len(self.infix_premises) + 1
        if self.premise_propositions:
            if len(self.infix_premises) < 2:
                print("Interpreted premise:\n")
            else:
                print("Interpreted premises:\n")
            for index, input_prop in enumerate(self.premise_propositions, start=1):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, output, 1)
                print(file=output)
        if self.conclusion_propositions:
            if len(self.infix_conclusions) < 2:
                print("Interpreted conclusion:\n")
            else:
                print("Interpreted conclusions:\n")
            for index, input_prop in enumerate(self.conclusion_propositions, start=start_con_num):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, output, 1)
                print(file=output)

    def print_enumerate(self, output):
        """prints the premises and conclusions with numbers"""
        start_con_num = len(self.infix_premises) + 1
        if self.infix_premises:
            if len(self.infix_premises) < 2:
                print("Premise:")
            else:
                print("Premises:")
            for index, sent in enumerate(self.infix_premises, start=1):
                print(f"{index}. {sent}", file=output)
        if self.infix_conclusions:
            if len(self.infix_conclusions) < 2:
                print("\nConclusion:")
            else:
                print("\nConclusions:")
            for index, sent in enumerate(self.infix_conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)

    def print_all(self, output):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        print(f"There is a {self.N}-model of:\n", file=output)
        self.print_enumerate(output)
        self.print_states(output)
        self.print_evaluation(output)
        self.print_inputs_recursively(output)

    def build_test_file(self, output):
        """generates a test file from input to be saved"""
        inputs_data = {
            "N": self.N,
            "premises": self.infix_premises,
            "conclusions": self.infix_conclusions,
            "runtime": self.model_runtime,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)


    # TODO: how can print_to and save_to be cleaned up and made less redundant?
    def print_to(self, print_cons_bool, print_unsat_core_bool, output=sys.__stdout__):
        """append all elements of the model to the file provided"""
        N = self.N
        if self.model_status:
            self.print_all(output)
            if print_cons_bool:
                # print("Satisfiable constraints:\n", file=output)
                self.print_constraints(self.constraints, output)
        else:
            print(f"\nThere are no {N}-models of:\n", file=output)
            self.print_enumerate(output)
            print(file=output)
            if print_unsat_core_bool:
                # print("Unsatisfiable core constraints:\n", file=output)
                self.print_constraints(self.model, output)
        print(f"Run time: {self.model_runtime} seconds\n", file=output)

    def save_to(self, doc_name, parent_file, cons_include, output):
        """append all elements of the model to the file provided"""
        print(f'# TITLE: {doc_name}.py generated from {parent_file}\n"""', file=output)
        if self.model_status:
            self.print_all(output)
            self.build_test_file(output)
            if cons_include:
                print("# Satisfiable constraints", file=output)
                # TODO: print constraint objects, not constraint strings
                print(f"all_constraints = {self.constraints}", file=output)
        else:
            print(f"\nThere are no {self.N}-models of:\n", file=output)
            self.print_enumerate(output)
            # print("\n# Unsatisfiable core constraints", file=output)
            self.print_constraints(self.model, output)
            self.build_test_file(output)
            if cons_include:
                print("# Unsatisfiable constraints", file=output)
                print(f"all_constraints = {self.constraints}", file=output)


class Proposition:
    """class for propositions to store their verifiers, falsifiers, alt worlds, etc
    has two subclasses Extensional and Counterfactual—Counterfactual is a Proposition
    subclass to make stuff easier"""

    def __init__(self, prefix_expr, model_structure, eval_world):
        """prefix_expr is a prefix expression. model is a ModelStructure"""
        self.prop_dict = {}
        self.prop_dict["prefix expression"] = prefix_expr
        self.parent_model_structure = model_structure
        (verifiers, falsifiers) = model_structure.find_complex_proposition(prefix_expr, eval_world)
        # for CFs, verifiers are worlds true at and falsifiers are worlds not true at
        # for modals, if they're true then the verifiers are only the null state and
        # falsifiers are nothing; if they're false the opposite
        self.prop_dict["verifiers"] = verifiers
        self.prop_dict["falsifiers"] = falsifiers

    def __setitem__(self, key, value):
        self.prop_dict[key] = value

    def __getitem__(self, key):
        return self.prop_dict[key]

    def __str__(self):
        return Infix(self["prefix expression"])

    def print_verifiers_and_falsifiers(self, current_world, indent=0, output=sys.__stdout__):
        """prints the possible verifiers and falsifier states for a sentence.
        inputs: the verifier states and falsifier states.
        Outputs: None, but prints the verifiers and falsifiers
        Used in print_prop()"""
        N = self.parent_model_structure.N
        truth_value = self.truth_value_at(current_world)
        indent_num = indent
        possible = self.parent_model_structure.possible
        model = self.parent_model_structure.model
        ver_prints = '∅'
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self["verifiers"]
            if model.evaluate(possible(bit))
        }
        if ver_states:
            ver_prints = pretty_set_print(ver_states)
        fal_prints = '∅'
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self["falsifiers"]
            if model.evaluate(possible(bit))
        }
        if fal_states:
            fal_prints = pretty_set_print(fal_states)
        world_state = bitvec_to_substates(current_world, N)
        print(
            f"{'  ' * indent_num}|{self}| = < {ver_prints}, {fal_prints} >"
            f"  ({truth_value} in {world_state})",
            file=output,
        )

class Extensional(Proposition):
    """Subclass of Proposition for extensional sentences"""

    def truth_value_at(self, eval_world):
        """finds whether a CF is true at a certain world
        returns a Boolean representing yes or no"""
        for verifier in self["verifiers"]:
            if bit_part(verifier, eval_world):
                return True
        return False

class Counterfactual(Proposition):
    """subclass of Proposition for counterfactuals"""
    def truth_value_at(self, eval_world):
        """finds whether a CF is true at a certain world
        returns a Boolean representing yes or no"""
        # TODO: I suspect we need something more like this
        # null_state = {BitVecVal(0,self.N)}
        # if null_state in self["verifiers"]:
        # if eval_world in self["verifiers"]:
        #     return True
        # return False
        return True if self["verifiers"] else False # same as for Modals

class Modal(Proposition):
    '''subclass of Proposition for modals'''
    def __init__(self, prefix_expr, model_structure, eval_world):
        super().__init__(prefix_expr, model_structure, eval_world)
        arg = prefix_expr[1]
        arg_worlds, non_arg_worlds = self.parent_model_structure.find_complex_proposition(arg, eval_world)
        self['arg worlds'] = arg_worlds
        self['non arg worlds'] = non_arg_worlds

    def truth_value_at(self, eval_world):
        if self["verifiers"]: # if null state in self["verifiers"]
            return True
        return False

def make_model_for(N):
    """
    input: N (int of number of atomic states you want in the model)
    returns a function that will solve the premises and conclusions"""

    def make_relations_and_solve(premises, conclusions):
        possible = Function("possible", BitVecSort(N), BoolSort())
        verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        assign = Function("assign", BitVecSort(N), AtomSort, BitVecSort(N))
        w = BitVec("w", N) # what will be the main world
        mod = ModelStructure(
            premises, conclusions, verify, falsify, possible, assign, N, w
        )
        mod.solve()
        return mod

    return make_relations_and_solve
