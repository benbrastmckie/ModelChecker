"""
file defines model structure class given a Z3 model sdffds
"""

from string import Template
import time
import sys
from z3 import (
    Solver,
    Function,
    BitVecSort,
    BoolSort,
    BitVec,
    BitVecVal,
    sat,
)

# # didn't work
# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# # Get the directory path of the current file
# current_dir = os.path.dirname(__file__)
# # Construct the full path to your project root
# project_root = os.path.abspath(os.path.join(current_dir, ".."))
# # project_root = project_root[:-4] # bandaid fix to remove "/src" from the root
# # Add the project root to the Python path
# sys.path.append(project_root)

# ### FOR TESTING ###
# from semantics import ( # imports issue fixed with above code
#     define_N_semantics,
#     # solve_constraints,
#     all_sentence_letters,
# )
# from model_definitions import (
#     find_compatible_parts,
#     atomic_propositions_dict_maker,
#     find_all_bits,
#     find_max_comp_ver_parts,
#     find_poss_bits,
#     find_subsentences,
#     find_world_bits,
#     pretty_set_print,
#     bit_part,
#     bitvec_to_substates,
#     int_to_binary,
#     true_and_false_worlds_for_cf,
#     find_complex_proposition,
# )
# from syntax import (
#     AtomSort,
#     infix,
#     prefix,
#     add_backslashes_to_infix,
# )

### FOR PACKAGING ###
from model_checker.semantics import ( # imports issue fixed with above code
    define_N_semantics,
    all_sentence_letters,
)
from model_checker.model_definitions import (
    find_compatible_parts,
    atomic_propositions_dict_maker,
    find_all_bits,
    find_max_comp_ver_parts,
    find_poss_bits,
    find_subsentences,
    find_world_bits,
    pretty_set_print,
    bit_part,
    bitvec_to_substates,
    int_to_binary,
    true_and_false_worlds_for_cf,
    find_complex_proposition,
)
from model_checker.syntax import (
    AtomSort,
    infix,
    prefix,
    add_backslashes_to_infix,
)

inputs_template = Template(
'''Run time: ${runtime} seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

### SETTINGS ###

# time cutoff for increasing N
max_time = ${max_time}

# finds a countermodel with the smallest value of N within max_time if True
optimize = False

# print all Z3 constraints if a model is found
print_cons_bool = False

# print all states including impossible states
print_impossible_states_bool = False

# present option to save output
save_bool = False


### EXAMPLE ###

# input sentences
premises = ${premises}
conclusions = ${conclusions}

# number of atomic states
N = ${N}

# makes all propositions contingent if True
contingent_bool = False

# makes all propositions have disjoint subject-matters if True
disjoint_bool = False
'''
)

class ModelSetup:
    """class which includes all elements provided by the user as well as those
    needed to find a model if there is one"""

    def __init__(self, N, infix_premises, infix_conclusions, max_time, contingent, disjoint):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.N = N
        self.max_time = max_time
        self.contingent = contingent
        self.disjoint = disjoint
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.imposition = Function("imposition", BitVecSort(N), BitVecSort(N), BitVecSort(N), BoolSort())
        # self.assign = Function("assign", BitVecSort(N), AtomSort, BitVecSort(N))
        self.w = BitVec("w", N) # what will be the main world
        self.prefix_premises = [prefix(prem) for prem in infix_premises]
        # M: I think below is a problem
        self.prefix_conclusions = [prefix(con) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = find_subsentences(prefix_sentences)
        find_constraints_func = define_N_semantics(
            self.N,
            self.contingent,
            self.disjoint,
            self.verify,
            self.falsify,
            self.possible,
            self.imposition,
            # self.assign,
        )
        frame_cons, prop_cons, premise_cons, conclusion_cons = find_constraints_func(
            self.prefix_premises,
            self.prefix_conclusions,
            self.w,
        )
        self.frame_constraints = frame_cons
        self.prop_constraints = prop_cons
        self.premise_constraints = premise_cons
        self.conclusion_constraints = conclusion_cons
        self.constraints = (
            self.frame_constraints +
            self.prop_constraints +
            self.premise_constraints +
            self.conclusion_constraints
        )
        timeout, z3_model_status, z3_model, model_runtime = self.solve(
            self.constraints,
            self.max_time
        )
        self.timeout = timeout
        self.model_status = z3_model_status
        self.z3_model = z3_model
        self.model_runtime = model_runtime

    # NOTE: seems to mostly be working but occasionally seems to run longer than the printed time
    def solve(self, all_constraints, max_time): # all_constraints is a list of constraints
        """Finds a model for the input constraints within the max_time if there is such a model
        returns a tuple with a boolean representing if (1) the timeout occurred, if (2) the
        constraints were solved or not and, if (3) the model or unsatisfiable core depending"""
        solver = Solver()
        solver.add(all_constraints)
        # Set the timeout (in milliseconds)
        milliseconds = int(max_time * 1000)
        solver.set("timeout", milliseconds)
        try:
            model_start = time.time()  # start benchmark timer
            result = solver.check()
            model_end = time.time()
            model_runtime = round(model_end - model_start, 4)
            if result == sat:
                return False, True, solver.model(), model_runtime
            if solver.reason_unknown() == "timeout":
                return True, False, None, model_runtime
            return False, False, solver.unsat_core(), model_runtime
        except RuntimeError as e:
            # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, False, None, None

    # # NOTE: this was when solve_constraints was in semantics.py
    # def solve(self, constraints, max_time):
    #     """solves for the model, returns None
    #     """
    #     timeout, z3_model_status, z3_model, model_runtime = solve_constraints(constraints, max_time)
    #     return timeout, z3_model_status, z3_model, model_runtime

    def build_test_file(self, output):
        """generates a test file from input to be saved"""
        inputs_data = {
            "N": self.N,
            "premises": self.infix_premises,
            "conclusions": self.infix_conclusions,
            "runtime": self.model_runtime,
            "max_time": self.max_time,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)

    def print_enumerate(self, output):
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

    def no_model_print(self, print_cons, output=sys.__stdout__):
        """prints the argument when there is no model with the option to
        include Z3 constraints."""
        if print_cons:
            self.print_constraints(self.z3_model, 'TOTAL', output)
        print(f"There are no {self.N}-models of:\n", file=output)
        self.print_enumerate(output)
        print(file=output)
        print(f"Run time: {self.model_runtime} seconds\n", file=output)

    def no_model_save(self, print_cons, output):
        """saves the arguments to a new file when there is no model with the
        option to include Z3 constraints."""
        constraints = self.constraints
        print(f"There are no {self.N}-models of:\n", file=output)
        self.print_enumerate(output)
        self.build_test_file(output)
        if self.timeout:
            print("No model found before timeout.\n", file=output)
        if print_cons:
            print("# Unsatisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)

    def print_constraints(self, consts, name, output=sys.__stdout__):
        """prints constraints in an numbered list"""
        if self.timeout:
            # print(f"TIMEOUT: {self.timeout}")
            # print("No model found before timeout.", file=output)
            # print(f"Try increasing max_time > {self.max_time}.\n", file=output)
            return
        if self.model_status:
            print(f"Satisfiable {name} constraints:\n", file=output)
        else:
            print("Unsatisfiable core constraints:\n", file=output)
        for index, con in enumerate(consts, start=1):
            print(f"{index}. {con}\n", file=output)

    def __str__(self):
        '''useful for using model-checker in a python file'''
        return f'{"" if self.model_status else "un"}sat ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions} with status {self.model_status}'

    def __bool__(self):
        '''returns the value of self.model_status (ie, whether the z3 model was solved)
        reasoning: say ms is a ModelSetup object. Now we can check its model_status by doing:
        if ms: # as opposed to if ms.model_status
            (do_something)
        '''
        return self.model_status


class StateSpace:
    """class for all states and their attributes"""

    def __init__(self, model_setup):
        self.model_setup = model_setup
        self.z3_model = model_setup.z3_model
        self.model_runtime = model_setup.model_runtime
        self.model_status = model_setup.model_status
        self.N = model_setup.N
        self.main_world = model_setup.w
        self.all_bits = find_all_bits(self.N)
        self.poss_bits = find_poss_bits(self.z3_model, self.all_bits, model_setup.possible)
        self.world_bits = find_world_bits(self.poss_bits)
        self.main_world = self.z3_model[self.main_world]
        self.verify = model_setup.verify
        self.falsify = model_setup.falsify
        self.all_subsentences = model_setup.all_subsentences
        prefix_sentences = model_setup.prefix_premises + model_setup.prefix_conclusions
        self.sentence_letters = all_sentence_letters(prefix_sentences)
        self.atomic_props_dict = atomic_propositions_dict_maker(self)
        self.all_propositions = [
            Proposition(sent, self, self.main_world) for sent in model_setup.all_subsentences
        ]
        self.premise_propositions = [
            Proposition(sent, self, self.main_world) for sent in model_setup.prefix_premises
        ]
        self.conclusion_propositions = [
            Proposition(sent, self, self.main_world) for sent in model_setup.prefix_conclusions
        ]
        # self.premise_propositions = self.find_propositions(model_setup.prefix_premises, True)
        # self.conclusion_propositions = self.find_propositions(model_setup.prefix_conclusions, True)

    def find_alt_bits(self, verifier_bits, evaulation_world=None):
        """
        Finds the alternative bits given verifier bits of an extensional proposition,
        possible states, worlds, and the evaluation world.
        Used in evaluate_cf_expression() and rec_print().
        """
        if evaulation_world is None:
            evaulation_world = self.main_world
        alt_bits = set()
        for ver in verifier_bits:
            comp_parts = find_compatible_parts(ver, self.poss_bits, evaulation_world)
            max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
            for world in self.world_bits:
                if not bit_part(ver, world):
                    continue
                for max_ver in max_comp_ver_parts:
                    if bit_part(max_ver, world):
                        alt_bits.add(world)
                        break  # to return to the second for loop over world_bits
        return alt_bits

    def find_imp_bits(self, verifier_bits, evaulation_world=None):
        """
        Finds the alternative bits given verifier bits of an extensional proposition,
        possible states, worlds, and the evaluation world.
        Used in evaluate_cf_expression() and rec_print().
        """
        if evaulation_world is None:
            evaulation_world = self.main_world
        imp_bits = set()
        for ver in verifier_bits:
            for world in self.world_bits:
                imp_bool = self.model_setup.imposition(ver, evaulation_world, world)
                if bool(self.z3_model.evaluate(imp_bool)):
                    imp_bits.add(world)
                    break  # to return to the second for loop over world_bits
        return imp_bits

    # Useful to user now that can search an infix expression
    # NOTE: I think this option is no longer available
    def find_proposition_object(self, expression):
        """given a sentence, finds the Proposition object in the model that corresponds
        to it. Can optionally search through only the extensional sentences
        Also defaults to searching an infix sentence, though internally it always searches
        prefix.
        If search infix, make sure you put double backslashes always!!
        returns a Proposition object"""
        # search_list = self.all_propositions
        # if infix_search:
        #     for prop_object in search_list:
        #         if prop_object["prefix expression"] == expression:
        #             return prop_object
        # else:
        #     for prop_object in search_list:
        #         if str(prop_object) == add_backslashes_to_infix(expression):
        #             return prop_object
        for prop_object in self.all_propositions:
            if prop_object["prefix expression"] == expression:
                return prop_object
        raise ValueError(
            f"there is no Proposition with expression {expression}")

    # # Useful to user now that can search infix expressions
    # def find_propositions(self, sentences, prefix_search=False):
    #     """finds all the Proposition objects in a ModelStructure
    #     that correspond to the prefix sentences in sentences.
    #     returns them as a list"""
    #     propositions = []
    #     for sent in sentences:
    #         propositions.append(self.find_proposition_object(sent, prefix_search=prefix_search))
    #     return propositions

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        N = self.model_setup.N
        sentence_letters = self.sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {bitvec_to_substates(main_world, N)}",
            file=output,
        )
        true_in_eval = set()
        for sent in sentence_letters:
            for bit in self.all_bits:
                ver_bool = self.model_setup.verify(bit, self.z3_model[sent])
                part_bool = bit_part(bit, main_world)
                if bool(self.z3_model.evaluate(ver_bool) and part_bool):
                    true_in_eval.add(sent)
                    break  # exits the first for loop
        false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
        GREEN = '\033[32m'
        RED = '\033[31m'
        # YELLOW = '\033[33m'
        RESET = '\033[0m'
        world_state = bitvec_to_substates(main_world, N)
        if true_in_eval:
            true_eval_list = sorted([str(sent) for sent in true_in_eval])
            true_eval_string = ", ".join(true_eval_list)
            print(
                f"  {GREEN}{true_eval_string}  (True in {world_state}){RESET}",
                file=output,
            )
        if false_in_eval:
            false_eval_list = sorted([str(sent) for sent in false_in_eval])
            false_eval_string = ", ".join(false_eval_list)
            print(
                f"  {RED}{false_eval_string}  (False in {world_state}){RESET}",
                file=output,
            )
        print(file=output)

    def print_to(self, print_cons_bool, print_impossible, output=sys.__stdout__):
        """append all elements of the model to the file provided"""
        self.print_all(print_impossible, output)
        structure = self.model_setup
        setup = self.model_setup
        if print_cons_bool:
            structure.print_constraints(setup.frame_constraints, 'FRAME', output)
            structure.print_constraints(setup.prop_constraints, 'PROPOSITION', output)
            structure.print_constraints(setup.premise_constraints, 'PREMISE', output)
            structure.print_constraints(setup.conclusion_constraints, 'CONCLUSION', output)
        print(f"Run time: {self.model_runtime} seconds\n", file=output)

    def save_to(self, cons_include, print_impossible, output):
        """append all elements of the model to the file provided"""
        constraints = self.model_setup.constraints
        self.print_all(print_impossible, output)
        self.model_setup.build_test_file(output)
        if cons_include:
            print("# Satisfiable constraints", file=output)
            # TODO: print constraint objects, not constraint strings
            print(f"all_constraints = {constraints}", file=output)

    def print_states(self, print_impossible, output=sys.__stdout__):
        """print all fusions of atomic states in the model
        print_impossible is a boolean for whether to print impossible states or not
        first print function in print.py"""
        N = self.model_setup.N
        print("\nState Space:", file=output)  # Print states
        YELLOW = '\033[33m'
        BLUE = '\033[34m'
        MAGENTA = '\033[35m'
        CYAN = '\033[36m'
        WHITE = '\033[37m'
        RESET = '\033[0m'
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
                print(f"  {WHITE}{bin_rep} = {MAGENTA}{state} (impossible){RESET}", file=output)

    def rec_print(self, prop_obj, world_bit, print_impossible, output, indent=0):
        """recursive print function (previously print_sort)
        returns None"""
        N = self.model_setup.N
        sentence_letters = self.sentence_letters
        prop_obj.print_verifiers_and_falsifiers(world_bit, print_impossible, indent, output)
        if str(prop_obj) in [str(atom) for atom in sentence_letters]:
            return
        prefix_expr = prop_obj["prefix expression"]
        op = prefix_expr[0]
        first_subprop = self.find_proposition_object(prefix_expr[1])
        indent += 1 # begin subcases, so indent
        if "neg" in op or "not" in op: # or "pre" in op:
            self.rec_print(first_subprop, world_bit, print_impossible, output, indent)
            return
        if 'Diamond' in op or 'Box' in op:
            for u in self.world_bits:
                self.rec_print(first_subprop, u, print_impossible, output, indent)
            return
        left_subprop = first_subprop
        right_subprop = self.find_proposition_object(prefix_expr[2])
        if "boxright" in op:
            CYAN = '\033[36m'
            RESET = '\033[0m'
            left_subprop_vers = left_subprop['verifiers']
            imp_worlds = self.find_alt_bits(left_subprop_vers, world_bit)
            imp_world_strings = {bitvec_to_substates(u,N) for u in imp_worlds}
            self.rec_print(left_subprop, world_bit, print_impossible, output, indent)
            print(
                f'{"  " * indent}'
                f'{CYAN}{left_subprop}-alternatives to {bitvec_to_substates(world_bit, N)} = '
                f'{pretty_set_print(imp_world_strings)}{RESET}',
                file=output
            )
            indent += 1
            for u in imp_worlds:
                self.rec_print(right_subprop, u, print_impossible, output, indent)
            return
        if "imposition" in op:
            CYAN = '\033[36m'
            RESET = '\033[0m'
            left_subprop_vers = left_subprop['verifiers']
            imp_worlds = self.find_imp_bits(left_subprop_vers, world_bit)
            imp_world_strings = {bitvec_to_substates(u,N) for u in imp_worlds}
            self.rec_print(left_subprop, world_bit, print_impossible, output, indent)
            print(
                f'{"  " * indent}'
                f'{CYAN}{left_subprop}-alternatives to {bitvec_to_substates(world_bit, N)} = '
                f'{pretty_set_print(imp_world_strings)}{RESET}',
                file=output
            )
            indent += 1
            for u in imp_worlds:
                self.rec_print(right_subprop, u, print_impossible, output, indent)
            return
        self.rec_print(left_subprop, world_bit, print_impossible, output, indent)
        self.rec_print(right_subprop, world_bit, print_impossible, output, indent)

    def print_inputs_recursively(self, print_impossible, output):
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
                self.rec_print(input_prop, initial_eval_world, print_impossible, output, 1)
                print(file=output)
        if self.conclusion_propositions:
            if len(infix_conclusions) < 2:
                print("INTERPRETED CONCLUSION:\n", file=output)
            else:
                print("INTERPRETED CONCLUSIONS:\n", file=output)
            for index, input_prop in enumerate(self.conclusion_propositions, start=start_con_num):
                print(f"{index}.", end="", file=output)
                self.rec_print(input_prop, initial_eval_world, print_impossible, output, 1)
                print(file=output)

    def print_all(self, print_impossible, output):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        N = self.model_setup.N
        print(f"\nThere is a {N}-model of:\n", file=output)
        self.model_setup.print_enumerate(output)
        self.print_states(print_impossible, output)
        self.print_evaluation(output)
        self.print_inputs_recursively(print_impossible, output)

class Proposition:
    """class for propositions to store their verifiers, falsifiers, alt worlds, etc
    has two subclasses Extensional and Counterfactual—Counterfactual is a Proposition
    subclass to make stuff easier"""

    def __init__(self, prefix_expr, model_setup, eval_world):
        """for modals and counterfactuals, if they're true then the verifiers
        are only the null state and falsifiers are nothing; if they're false the opposite"""
        self.prop_dict = {}
        self.prop_dict["prefix expression"] = prefix_expr
        self.model_setup = model_setup
        verifiers, falsifiers = find_complex_proposition(model_setup, prefix_expr, eval_world)
        self.prop_dict["verifiers"] = verifiers
        self.prop_dict["falsifiers"] = falsifiers
        # TODO: can cf_sentences be treated in a more uniform way, avoiding the if clause below?
        # if 'preceq' in str(prefix_expr[0]):
        #     print(f"TEST: {verifiers}")
        if 'boxright' in str(prefix_expr[0]) or 'imposition' in str(prefix_expr[0]):
            # print(f"TEST: check condition")
            self.cf_world = eval_world
            true_worlds, false_worlds = true_and_false_worlds_for_cf(model_setup, prefix_expr)
            # print(f"TEST WORLDS: true {true_worlds}; false {false_worlds}")
            self['worlds cf true at'] = true_worlds
            self['worlds cf false at'] = false_worlds

    def __setitem__(self, key, value):
        self.prop_dict[key] = value

    def __getitem__(self, key):
        '''NOTE: If a user wants to access a modal or counterfactual Proposition's verifiers, 
        THEY SHOULD NOT. They should instead use the truth_value_at() method'''
        return self.prop_dict[key]

    def __str__(self):
        return infix(self["prefix expression"])

    def update_proposition(self, eval_world):
        """updates the evaluation world for counterfactuals"""
        # if not is_counterfactual(self['prefix expression']):
        #     raise AttributeError(f'You can only update verifiers for CFs: {self} is not a CF.')
        N = self.model_setup.N
        if eval_world == self.cf_world:
            return
        if eval_world in self['worlds cf true at']:
            self['verifiers'], self['falsifiers'] = {BitVecVal(0,N)}, set()
            return
        self['verifiers'], self['falsifiers'] = set(), {BitVecVal(0,N)}
        return

    def truth_value_at(self, eval_world):
        '''Given a world, returns the truth value of the Proposition at that world.
        Used in print_verifiers_and_falsifiers.'''
        # test = self["prefix expression"]
        # print(f"TEST: {test}")
        for verifier in self["verifiers"]:
            if bit_part(verifier, eval_world):
                return True
        for falsifier in self["falsifiers"]:
            # test = self["falsifiers"]
            # print(f"TEST: {test}")
            if bit_part(falsifier, eval_world):
                # N = self.model_structure.N
                # print(f"TEST: falsifier = {bitvec_to_substates(falsifier, N)}")
                return False
        return None
        # raise ValueError(
        #     "Something has gone wrong.\n"
        #     f'No verifier or falsifier for {self["prefix expression"]} at world {eval_world}'
        # )

    def print_verifiers_and_falsifiers(self, eval_world, print_impossible=False, indent=0, output=sys.__stdout__):
        """prints the possible verifiers and falsifier states for a sentence.
        used in: rec_print() 
        ensures eval_world is in fact the eval_world for CFs"""
        N = self.model_setup.N
        truth_value = self.truth_value_at(eval_world)
        # TODO: is this necessary?
        # prefix_expr_op = self.prop_dict["prefix expression"][0]
        # if 'boxright' in str(prefix_expr_op):
        #     # print('TEST: CONFIRM')
        #     self.update_verifiers(eval_world)
        indent_num = indent
        possible = self.model_setup.model_setup.possible
        z3_model = self.model_setup.z3_model
        ver_prints = '∅'
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self["verifiers"]
            if z3_model.evaluate(possible(bit))
            or print_impossible
        }
        if ver_states:
            ver_prints = pretty_set_print(ver_states)
        fal_prints = '∅'
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self["falsifiers"]
            if z3_model.evaluate(possible(bit))
            or print_impossible
        }
        if fal_states:
            fal_prints = pretty_set_print(fal_states)
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
                N = self.model_setup.N
                world_state = bitvec_to_substates(eval_world, N)
                print(
                    f"\n{RED}WARNING:{RESET}"
                    f"{self} is neither true nor false at {world_state}.\n"
                )
        print(
            f"{'  ' * indent_num}{FULL}|{self}| = < {ver_prints}, {fal_prints} >{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}",
            file=output,
        )

def make_model_for(N, premises, conclusions, max_time, contingent, disjoint):
    """
    input: N (int of number of atomic states you want in the model)
    returns a function that will solve the premises and conclusions"""
    backslash_premises = [add_backslashes_to_infix(prem) for prem in premises]
    backslash_conclusions = [add_backslashes_to_infix(concl) for concl in conclusions]
    model_setup = ModelSetup(
        N,
        backslash_premises,
        backslash_conclusions,
        max_time,
        contingent,
        disjoint,
    )
    # z3_model_status, z3_model, model_runtime = model_setup.solve()
    # model_structure = ModelStructure(z3_model_status, model_setup, z3_model, model_runtime)
    return model_setup
    # NOTE: since you save the ModelSetup object as an attribute of the ModelStructure object,
    # there's really no need to return it as well. I'm not going to remove it in case it adds
    # some bugs down the road since it's been a while since I've touched things, but just thought
    # I'd say to consider
