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
    atomic_propositions_dict_maker,
    find_all_bits,
    find_max_comp_ver_parts,
    find_poss_bits,
    find_world_bits,
    prefix_combine,
    pretty_set_print,
    bit_part,
    bitvec_to_substates,
    int_to_binary,
    infix_combine,
    find_subsentences_of_kind,
    is_counterfactual,
    is_modal,
    true_and_false_worlds_for_cf,
    find_complex_proposition,
)
# from model_checker.syntax import ( # for packaging
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

# print all states including impossible states
print_impossible_states_bool = False

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
            self.all_bits = find_all_bits(self.N)
            self.poss_bits = find_poss_bits(self.model, self.all_bits, self.possible)
            self.world_bits = find_world_bits(self.poss_bits)
            self.main_world = self.model[self.w]
            self.atomic_props_dict = atomic_propositions_dict_maker(self)
            self.extensional_propositions = [Proposition(ext_subsent, self, self.main_world)
                                            for ext_subsent in self.extensional_subsentences]
            self.counterfactual_propositions = [Proposition(cf_subsent, self, self.main_world)
                                            for cf_subsent in self.counterfactual_subsentences]
            self.modal_propositions = [Proposition(modal_subsent, self, self.main_world)
                                        for modal_subsent in self.modal_subsentences]
            self.all_propositions = (self.extensional_propositions +
                                     self.counterfactual_propositions + self.modal_propositions)
            self.premise_propositions = self.find_propositions(self.prefix_premises, prefix=True)
            self.conclusion_propositions = self.find_propositions(self.prefix_conclusions, prefix=True)
            # TODO: just missing the which-sentences-true-in-which-worlds

    # NOTE: could be relevant to user, so leaving it here. @B, what do you think?
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
    
    # Useful to user now that can search an infix expression
    def find_proposition_object(self, expression, prefix=False, ext_only=False):
        """given a sentence, finds the Proposition object in the model that corresponds
        to it. Can optionally search through only the extensional sentences
        Also defaults to searching an infix sentence, though internally it always searches
        prefix. 
        If search infix, make sure you put double backslashes always!!
        returns a Proposition object"""
        search_list = self.extensional_propositions
        if ext_only is False:
            search_list = self.all_propositions
        if prefix == True:
            for prop_object in search_list:
                if prop_object["prefix expression"] == expression:
                    return prop_object
        else:
            for prop_object in search_list:
                if str(prop_object) == expression:
                    return prop_object
        raise ValueError(
            f"there is no proposition with expression {expression}")

    # Useful to user now that can search infix expressions
    def find_propositions(self, sentences, prefix=False):
        """finds all the Proposition objects in a ModelStructure
        that correspond to the prefix sentences in sentences.
        returns them as a list"""
        propositions = []
        for sent in sentences:
            propositions.append(self.find_proposition_object(sent, prefix=prefix))
        return propositions

    def print_states(self, print_impossible, output=sys.__stdout__):
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
            if bit in self.poss_bits:
                print(f"  {bin_rep} = {state}", file=output)
                continue
            if print_impossible:
                print(f"  {bin_rep} = {state} (impossible)", file=output)


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
            # TODO: linter error: "Uninitalized" is not iterable  "__iter__" method does not return an object
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

    def rec_print(self, prop_obj, world_bit, print_impossible, output, indent=0):
        """recursive print function (previously print_sort)
        returns None"""
        N = self.N
        prop_obj.print_verifiers_and_falsifiers(world_bit, print_impossible, indent, output)
        if str(prop_obj) in [str(atom) for atom in self.sentence_letters]:
            return
        prefix_expr = prop_obj["prefix expression"]
        op = prefix_expr[0]
        first_subprop = self.find_proposition_object(prefix_expr[1], prefix=True)
        indent += 1 # begin subcases, so indent
        if "neg" in op:
            self.rec_print(first_subprop, world_bit, print_impossible, output, indent)
            return
        if 'Diamond' in op or 'Box' in op:
            for u in self.world_bits:
                self.rec_print(first_subprop, u, print_impossible, output, indent)
            return
        left_subprop = first_subprop
        right_subprop = self.find_proposition_object(prefix_expr[2], prefix=True)
        if "boxright" in op:
            # assert (
            #     left_subprop in self.extensional_propositions
            # ), f"{prop_obj} is not a valid cf because antecedent {left_subprop} is not extensional"
            left_subprop_vers = left_subprop['verifiers']
            phi_alt_worlds_to_world_bit = self.find_alt_bits(left_subprop_vers, world_bit)
            alt_worlds_as_strings = {bitvec_to_substates(u,N) for u in phi_alt_worlds_to_world_bit}
            self.rec_print(left_subprop, world_bit, print_impossible, output, indent)
            print(
                f'{"  " * indent}'
                f'{left_subprop}-alternatives to {bitvec_to_substates(world_bit, N)} = '
                f'{pretty_set_print(alt_worlds_as_strings)}',
                file=output
            )
            indent += 1
            for u in phi_alt_worlds_to_world_bit:
                self.rec_print(right_subprop, u, print_impossible, output, indent)
            return
        self.rec_print(left_subprop, world_bit, print_impossible, output, indent)
        self.rec_print(right_subprop, world_bit, print_impossible, output, indent)

    def print_inputs_recursively(self, print_impossible, output):
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
                self.rec_print(input_prop, initial_eval_world, print_impossible, output, 1)
                print(file=output)
        if self.conclusion_propositions:
            if len(self.infix_conclusions) < 2:
                print("Interpreted conclusion:\n")
            else:
                print("Interpreted conclusions:\n")
            for index, input_prop in enumerate(self.conclusion_propositions, start=start_con_num):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, print_impossible, output, 1)
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

    def print_all(self, print_impossible, output):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        print(f"There is a {self.N}-model of:\n", file=output)
        self.print_enumerate(output)
        self.print_states(print_impossible, output)
        self.print_evaluation(output)
        self.print_inputs_recursively(print_impossible, output)

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
    def print_to(self, print_cons_bool, print_unsat_core_bool, print_impossible, output=sys.__stdout__):
        """append all elements of the model to the file provided"""
        N = self.N
        if self.model_status:
            self.print_all(print_impossible, output)
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

    def save_to(self, doc_name, parent_file, cons_include, print_impossible, output):
        """append all elements of the model to the file provided"""
        print(f'# TITLE: {doc_name}.py generated from {parent_file}\n"""', file=output)
        if self.model_status:
            self.print_all(print_impossible, output)
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
        (verifiers, falsifiers) = find_complex_proposition(model_structure, prefix_expr, eval_world)
        # for modals and CFS, if they're true then the verifiers are only the null state and
        # falsifiers are nothing; if they're false the opposite
        self.world_bits = model_structure.world_bits # NOTE: this isn't being called anywhere
        self.prop_dict["verifiers"] = verifiers
        self.prop_dict["falsifiers"] = falsifiers
        if is_modal(prefix_expr):
            arg = prefix_expr[1]
            arg_worlds, non_arg_worlds = find_complex_proposition(model_structure, arg, eval_world)
            self['arg worlds'] = arg_worlds
            self['non arg worlds'] = non_arg_worlds
        if is_counterfactual(prefix_expr):
            self.current_eval_world = eval_world
            true_worlds, false_worlds = true_and_false_worlds_for_cf(model_structure, prefix_expr)
            self['worlds cf true at'] = true_worlds
            self['worlds cf false at'] = false_worlds

    def __setitem__(self, key, value):
        self.prop_dict[key] = value

    def __getitem__(self, key):
        '''NOTE: If a user wants to access a modal or counterfactual Proposition's verifiers, 
        THEY SHOULD NOT. They should instead use the truth_value_at() method'''
        return self.prop_dict[key]

    def __str__(self):
        return Infix(self["prefix expression"])

    def update_verifiers(self, new_world):
        if not is_counterfactual(self['prefix expression']):
            raise AttributeError(f'You can only update verifiers for CFs, and {self} is not a CF.')
        N = self.parent_model_structure.N
        if new_world == self.current_eval_world:
            return 
        if new_world in self['worlds cf true at']:
            self['verifiers'], self['falsifiers'] = {BitVecVal(0,N)}, set()
            return
        self['verifiers'], self['falsifiers'] = set(), {BitVecVal(0,N)}
        return

    def print_verifiers_and_falsifiers(self, current_world, print_impossible=False, indent=0, output=sys.__stdout__):
        """prints the possible verifiers and falsifier states for a sentence.
        inputs: the verifier states and falsifier states.
        Outputs: None, but prints the verifiers and falsifiers
        Used in rec_print()"""
        N = self.parent_model_structure.N
        truth_value = self.truth_value_at(current_world) # use in rec_print ensures current_world
                                                         # is in fact the current world, for CFs
        if self in self.parent_model_structure.counterfactual_propositions:
            self.update_verifiers(current_world)
        indent_num = indent
        possible = self.parent_model_structure.possible
        model = self.parent_model_structure.model
        ver_prints = '∅'
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self["verifiers"]
            if model.evaluate(possible(bit))
            or print_impossible
        }
        if ver_states:
            ver_prints = pretty_set_print(ver_states)
        fal_prints = '∅'
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self["falsifiers"]
            if model.evaluate(possible(bit))
            or print_impossible
        }
        if fal_states:
            fal_prints = pretty_set_print(fal_states)
        world_state = bitvec_to_substates(current_world, N)
        print(
            f"{'  ' * indent_num}|{self}| = < {ver_prints}, {fal_prints} >"
            f"  ({truth_value} in {world_state})",
            file=output,
        )

    def truth_value_at(self,eval_world):
        '''Given a world, returns the truth value of the Proposition at that world.
        Used in print_verifiers_and_falsifiers.'''
        prefix_expr = self['prefix expression']
        if is_counterfactual(prefix_expr):
            return True if eval_world in self['worlds cf true at'] else False
        if is_modal(prefix_expr):
            return True if self["verifiers"] else False
         # else case: extensional. Last to be computationally efficient (see def of is_extensional)
        for verifier in self["verifiers"]:
            if bit_part(verifier, eval_world):
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
