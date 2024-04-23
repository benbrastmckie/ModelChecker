import time
from print import (
    # find_alt_bits,
    find_compatible_parts,
    find_relations,
    print_alt_worlds,
    print_vers_and_fals,
)
from definitions import (
    verify,
    possible,
    bit_part,
    bitvec_to_substates,
    int_to_binary,
    w,
)
from semantics import (
    infix_combine,
    find_all_constraints,
    solve_constraints,
)
from model_definitions import (
    atomic_propositions_dict,
    coproduct,
    find_all_bits,
    find_max_comp_ver_parts,
    find_poss_bits,
    find_world_bits,
    product,
)

# TODO: the three types of objects that it would be good to store as classes
# include: (1) premises, conclusions, input_sentences, prefix_sentences,
# prefix_sub_sentences, infix_sub_sentences, sentence_letters, constraints;
# (2) z3_model, model_status, model_run_time, all_bits, poss_bits, world_bits,
# eval_world_bit; (3) ext_props_dict, true_in_world_dict, alt_worlds_dict.

# NOTE: the ext_props_dict should associate each extensional prefix_sub_sentence
# with its infix form, and its proposition. the true_in_world_dict should
# associate each world with the set of prefix_sub_sentences (extensional or
# otherwise) that are true in that world. the alt_worlds_dict should associate
# the antecedent of any counterfactuals with the alternatives to the world of
# evaluation in question (this will only differ from the eval_world_bit in the
# case of nested counterfactuals).


class ModelStructure():
    '''self.premises is a list of prefix sentences
    self.conclusions is a list of prefix sentences
    self.input_sentences is the combination of self.premises and self.conclusions with the conclusions negated
    self.sentence letters is a list of atomic sentence letters (each of sort AtomSort)
    self.constraints is a list (?) of constraints
    everything else is initialized as None'''
    def __init__(self, input_premises, input_conclusions):
        self.premises = input_premises
        self.conclusions = input_conclusions
        self.input_sentences = infix_combine(input_premises, input_conclusions)
        # TODO: replace prefix_sentences with ext_sub_sentences
        consts, sent_lets, extensional_subsentences = find_all_constraints(self.input_sentences)
        self.sentence_letters = sent_lets
        self.constraints = consts
        self.extensional_subsentences = extensional_subsentences # a list of prefix sentences (lists), not
        # a list of Proposition objects. Cannot make it that in init because that would require having run the model
        # # initialize yet-undefined attributes
        # TODO: add along with other method for error report
        # self.model = None
        # self.model_runtime = None
        # self.all_bits = None
        # self.poss_bits = None
        # self.world_bits = None
        # self.eval_world = None
        # self.atomic_props_dict = None

    def solve(self,N):
        '''solves the model, returns None
        self.model is the ModelRef object resulting from solving the model
        self.model_runtime is the runtime of the model as a float
        self.all_bits is a list of all bits (each of sort BitVecVal)
        self.poss_bits is a list of all possible bits
        self.world_bits is a lsit of all world bits
        self.eval_world is the eval world (as a BitVecVal)
        self.atomic_props_dict is a dictionary with keys AtomSorts and keys (V,F)
        '''
        model_start = time.time() # start benchmark timer
        solved_model_status, solved_model = solve_constraints(self.constraints)
        self.model_status = solved_model_status
        self.model = solved_model
        model_end = time.time()
        model_total = round(model_end - model_start,4)
        self.model_runtime = model_total
        if self.model_status:
            self.all_bits = find_all_bits(N) # var accessed from outside (not bad, just noting)
            # print(self.model)
            self.poss_bits = find_poss_bits(self.model,self.all_bits)
            self.world_bits = find_world_bits(self.poss_bits)
            self.eval_world = self.model[w] # var accessed from outside (not bad, just noting)
            self.atomic_props_dict = atomic_propositions_dict(self.all_bits, self.sentence_letters, self.model)
            self.extensional_propositions = [Proposition(ext_subsent, self) for ext_subsent in self.extensional_subsentences]
            # just missing the which-sentences-true-in-which-worlds
        # else: # NOTE: maybe these should be defined as something for the sake of init above
            
    def find_alt_bits(self, proposition_verifier_bits, compare_world):
        """
        Finds the alternative bits given verifier bits, possible states, worlds, and
        the evaluation world. Used in find_relations().
        """
        alt_bits = set()
        for ver in proposition_verifier_bits:
            comp_parts = find_compatible_parts(ver, self.poss_bits, compare_world)
            max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
            for world in compare_world:
                if not bit_part(ver, world):
                    continue
                for max_ver in max_comp_ver_parts:
                    if bit_part(max_ver, world) and world.sexpr() != compare_world.sexpr():
                        alt_bits.add(world)
                        break  # to return to the second for loop over world_bits
        return alt_bits

    def print_states(self,N):
        """print all fusions of atomic states in the model
        first print function in print.py"""
        # print("\n(Possible) States:")  # Print states
        print("\nStates:")  # Print states
        for bit in self.all_bits:
            # test_state = BitVecVal(val, size) # was instead of bit
            state = bitvec_to_substates(bit)
            bin_rep = (
                bit.sexpr()
                if N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), N)
            )
            if bit in self.world_bits:
                print(f"  {bin_rep} = {state} (world)")
            # TODO: below has invalid conditional operand
            elif self.model.evaluate(possible(bit)):
                print(f"  {bin_rep} = {state} (possible)")
            else:
                # print(f"  {bin_rep} = {state} (impossible)")
                continue

    def find_complex_proposition(self,complex_sentence):
        """sentence is a sentence in prefix notation
        For a given complex proposition, returns the verifiers and falsifiers of that proposition
        given a solved model"""
        if 'boxright' in complex_sentence:
            raise ValueError("There is no proposition for non-extensional sentences.")
        if not self.atomic_props_dict:
            raise ValueError("There is nothing in atomic_props_dict yet. Have you actually run the model?")
        if len(complex_sentence) == 1:
            sent = complex_sentence[0]
            return self.atomic_props_dict[sent]
        op = complex_sentence[0]
        Y = complex_sentence[1]
        if "neg" in op:
            # TODO: linter says object of type "None" is not subscriptable
            # NOTE: was getting an error since Y need not be a sentence letter.
            # fixed by making this match the other cases below.
            Y_V = self.find_complex_proposition(Y)[0]
            Y_F = self.find_complex_proposition(Y)[1]
            return (Y_F,Y_V)
        Z = complex_sentence[2]
        Y_V = self.find_complex_proposition(Y)[0]
        Y_F = self.find_complex_proposition(Y)[1]
        Z_V = self.find_complex_proposition(Z)[0]
        Z_F = self.find_complex_proposition(Z)[1]
        if "wedge" in op:
            return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
        if "vee" in op:
            return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
        if "leftrightarrow" in op:
            return (product(coproduct(Y_F, Z_V), coproduct(Y_V, Z_F)),
                    coproduct(product(Y_V, Z_F), product(Y_F, Z_V)))
        if "rightarrow" in op:
            return (coproduct(Y_F, Z_V), product(Y_V, Z_F))
        # NOTE: could assign the sentence to the worlds which make the
        # counterfactual true in this final case. should probably call another
        # function here which finds that set of worlds if we go this route.
        # if "boxright" in op:
        #     raise ValueError("don't knowhow to handle boxright case yet")

    def print_evaluation(self):
        """print the evaluation world and all sentences true/false in that world
        sentence letters is a list
        second print function in print.py"""
        print(f"\nThe evaluation world is {bitvec_to_substates(self.eval_world)}:")
        true_in_eval = set()
        for sent in self.sentence_letters:
            for bit in self.all_bits:
                ver_bool = verify(bit, self.model[sent])
                part_bool = bit_part(bit, self.eval_world)
                # TODO: below has invalid conditional operand
                if self.model.evaluate(ver_bool) and part_bool:
                    true_in_eval.add(sent)
                    break  # exits the first for loop
        false_in_eval = {R for R in self.sentence_letters if not R in true_in_eval}
        if true_in_eval:
            true_eval_list = sorted([str(sent) for sent in true_in_eval])
            true_eval_string = ", ".join(true_eval_list)
            print(f"  {true_eval_string}  (true in {bitvec_to_substates(self.eval_world)})")
        if false_in_eval:
            false_eval_list = sorted([str(sent) for sent in false_in_eval])
            false_eval_string = ", ".join(false_eval_list)
            print(f"  {false_eval_string}  (not true in {bitvec_to_substates(self.eval_world)})")

    def print_constraints(self,consts):
        """prints constraints in an numbered list"""
        for index, con in enumerate(consts, start=1):
            print(f"{index}. {con}\n")
            # print(f"Constraints time: {time}\n")

    # this is exactly the old thing. Needs to be changed once figure out how to store Proposition info somewhere
    # and in a useable way
    def print_props(self,N,world):
        """print each propositions and the alternative worlds in which it is true"""
        all_bits = find_all_bits(N)
        print("\nPropositions:")
        # TODO: couldn't get these lines to replace the below
        for S in self.input_sentences:
            ver_bits = self.find_complex_proposition(S)[0]
            fal_bits = self.find_complex_proposition(S)[1]
            alt_bits = self.find_alt_bits(ver_bits, world)
            print_vers_and_fals(self.model, S, ver_bits, fal_bits)
            print_alt_worlds(all_bits, S, self.sentence_letters, self.model, alt_bits)
        # for S in self.sentence_letters:
        #     ver_bits, fal_bits, alt_bits = find_relations(all_bits, S, self.model)
        #     print_vers_and_fals(self.model, S, ver_bits, fal_bits)
        #     print_alt_worlds(all_bits, S, self.sentence_letters, self.model, alt_bits)

    def print_all(self, N, print_cons_bool, print_unsat_core_bool):
        """prints all elements of the model"""
        if self.model_status:
            print(f"\nThere is an {N}-model of:\n")
            for sent in self.input_sentences:
                print(sent)
            self.print_states(N)
            self.print_evaluation()
            self.print_props(N,self.eval_world)
            if print_cons_bool:
                print("Satisfiable core constraints:\n")
                self.print_constraints(self.constraints)
                print()
        else:
            print(f"\nThere are no {N}-models of:\n")
            for sent in self.input_sentences:
                print(sent)
            print()
            if print_unsat_core_bool:
                print("Unsatisfiable core constraints:\n")
                self.print_constraints(self.model)
                print()

    # NOTE: from _M_ commit
    # def print_props(self):
    #     # print(self.extensional_subsentences)
    #     for ext_proposition in self.extensional_propositions:
    #         ext_proposition.print_possible_verifiers_and_falsifiers()
    #         ext_proposition.print_alt_worlds()


# the Proposition class is unused because I haven't gotten to a couple of things that would enable it to be integrated, namely:
#     1. I can easily set everything in the input_sentences to be a propositon. How to make subsentences and un-negated conclusions?
#     2. I thought I had another issue but I can't think of it rn off the top of my head
# TODO: inti with model to store props to ext_sub_sentences
class Proposition():
    def __init__(self, prefix_expr, model_structure):
        '''prefix_expr is a prefix expression. model is a ModelStructure'''
        self.prop_dict = {}
        self.prop_dict['prefix expression'] = prefix_expr
        verifiers_in_model, falsifiers_in_model = model_structure.find_complex_proposition(prefix_expr)
        self.prop_dict['verifiers'] = verifiers_in_model
        self.prop_dict['falsifiers'] = falsifiers_in_model
        self.prop_dict['alternative worlds'] = model_structure.find_alt_bits(verifiers_in_model)
        self.parent_model_structure = model_structure

    def __setitem__(self, key, value):
        self.prop_dict[key] = value

    def __getitem__(self, key):
        return self.prop_dict[key]

    def print_possible_verifiers_and_falsifiers(self):
        """prints the possible verifiers and falsifier states for a sentence.
        inputs: the verifier states and falsifier states.
        Outputs: None, but prints the verifiers and falsifiers
        Used in print_prop()"""
        model = self.parent_model_structure.model
        ver_states = {bitvec_to_substates(bit) for bit in self['verifiers'] if model.evaluate(possible(bit))}
        fal_states = {bitvec_to_substates(bit) for bit in self['falsifiers'] if model.evaluate(possible(bit))}
        if ver_states and fal_states:
            print(
                f"  |{self['infix expression']}| = < {make_set_pretty_for_print(ver_states)}, {make_set_pretty_for_print(fal_states)} >"
            )
        elif ver_states and not fal_states:
            print(f"  |{self['infix expression']}| = < {make_set_pretty_for_print(ver_states)}, ∅ >")
        elif not ver_states and fal_states:
            print(f"  |{self['infix expression']}| = < ∅, {make_set_pretty_for_print(fal_states)} >")
        else:
            print(f"  |{self['infix expression']}| = < ∅, ∅ >")

    def print_alt_worlds(self):
        """prints everything that has to do with alt worlds
        Used in print_prop()"""
        model = self.parent_model_structure.model
        alt_worlds = {bitvec_to_substates(alt) for alt in self['alternative worlds']}
        if alt_worlds:
            print(f"  {self['infix expression']}-alternatives to {bitvec_to_substates(model[w])} = {make_set_pretty_for_print(alt_worlds)}")
            for alt_bit in self['alternative worlds']:
                true_in_alt, false_in_alt = find_true_and_false_in_alt(
                    alt_bit, self.parent_model_structure
                )
                print_alt_relation(true_in_alt, alt_bit, "true")
                print_alt_relation(false_in_alt, alt_bit, "not true")
            print()  # for an extra blank line
        else:
            print(f"  There are no {self['infix expression']}-alternatives to {bitvec_to_substates(model[w])}")
            print()  # for an extra blank line

    # TODO: what should this look like?
    def __str__(self):
        return Infix(self['prefix expression']) # it actually works out very nicely if this is it
        # that way instead of doing |{self['infix expression']}| we can do |self|
