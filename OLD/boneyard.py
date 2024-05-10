'''
file contains all basic definitions
'''

from z3 import (
    Not,
    Exists,
    ForAll,
    Implies,
    BoolSort,
    BitVecSort,
    DeclareSort,
    BitVec,
    Function,
    And,
    BitVecNumRef,
    simplify,
)

# TODO: move to test_complete without causing circular import
N = 3

# from user_input import N
# from test_complete import N

# def bit_vec_length():
#     from test_complete import N
#     return N

# N = bit_vec_length()

################################
######## DECLARATIONS ##########
################################

# NOTE: tried moving N to test_complete but created circular import error
# from test_complete import N


# sentence letters sort definition
AtomSort = DeclareSort("AtomSort")

# primitive properties and relations
possible = Function("possible", BitVecSort(N), BoolSort())
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())

# NOTE: I tried to include a more meaningful name for w but it didn't work
# w = BitVec("eval_world_w", N)
# TODO: make eval_world_w global variable
w = BitVec("w", N)




################################
######### DEFINITIONS ##########
################################

# would go to semantics
def is_bitvector(bit_s):
    '''bit_s is a bitvector'''
    if isinstance(bit_s, BitVecNumRef):
        return True
    return False

#would go to semantics
def is_atomic(bit_s):
    '''bit_s has exactly one index with value 1'''
    return And(bit_s != 0, 0 == (bit_s & (bit_s - 1)))



#would go to semantics
def is_proper_part_of(bit_s, bit_t):
    '''the fusion of bit_s and bit_t is identical to bit_t'''
    return And(is_part_of(bit_s, bit_t), Not(bit_t == bit_s))


# would go to sematnics, though I think prop_const supplants this
def proposition(atom):
    """
    atom is a proposition since its verifiers and falsifiers are closed under
    fusion respectively, and the verifiers and falsifiers for atom are
    incompatible (exhaustivity). NOTE: exclusivity crashes Z3 so left off.
    """
    x = BitVec("prop_dummy_x", N)
    y = BitVec("prop_dummy_y", N)
    return And(
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)),
        ), # verifiers for atom are closed under fusion
        ForAll(
            [x, y],
            Implies(And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)),
        ), # falsifiers for atom are closed under fusion
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), falsify(y, atom)), Not(compatible(x, y))),
        ), # verifiers and falsifiers for atom are incompatible
        # ForAll(
        #     x,
        #     Implies(
        #         possible(x),
        #         Exists(y, And(compatible(x, y), Or(verify(y, atom), falsify(y, atom)))),
        #     ),
        # ), # every possible state is compatible with either a verifier or falsifier for atom
        # NOTE: adding the constraint above makes Z3 crash
        # without this constraint the logic is not classical (there could be truth-value gaps)
    )


# would go to semantics
def total_fusion(list_of_states):
    """returns the fusion of a list of states."""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation


# would go to semantics
def Equivalent(cond_a,cond_b):
    '''define the biconditional to make Z3 constraints intuitive to read'''
    return cond_a == cond_b

# came from syntax, would go to either syntax, semantics, or model_definitions
def prefix_combine(prem,con):
    '''combines the premises with the negation of the conclusion(s).
    premises are prefix sentences, and so are the conclusions'''
    # if prem is None:
    #     prem = []
    input_sent = prem
    neg_conclusion_sents = [['\\neg ', sent] for sent in con]
    input_sent.extend(neg_conclusion_sents)
    return input_sent


# removed from model_structure after redid how we do alt worlds and what not
# was a method of Proposition objects
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
    ver_states = {
        bitvec_to_substates(bit, N)
        for bit in self["verifiers"]
        if model.evaluate(possible(bit))
    }
    fal_states = {
        bitvec_to_substates(bit, N)
        for bit in self["falsifiers"]
        if model.evaluate(possible(bit))
    }
    world_state = bitvec_to_substates(current_world, N)
    if ver_states and fal_states:
        print(
            f"{'  ' * indent_num}|{self}| = < {make_set_pretty_for_print(ver_states)}, {make_set_pretty_for_print(fal_states)} >"
            f"  ({truth_value} in {world_state})",
            file=output,
        )
    elif ver_states and not fal_states:
        print(
            f"{'  ' * indent_num}|{self}| = < {make_set_pretty_for_print(ver_states)}, ∅ >"
            f"  ({truth_value} in {world_state})",
            file=output,
        )
    elif not ver_states and fal_states:
        print(
            f"{'  ' * indent_num}|{self}| = < ∅, {make_set_pretty_for_print(fal_states)} >"
            f"  ({truth_value} in {world_state})",
            file=output,
        )
    else:
        print(
            f"{'  ' * indent_num}|{self}| = < ∅, ∅ >"
            f"({truth_value} in {world_state})", file=output
        )

# removed from model_structure after redid how we do alt worlds and what not
        # was a method of ModelStructure objects
def print_props(self, output=sys.__stdout__):
    """prints possible verifiers and falsifiers for every extensional proposition
    and also the prop-alt worlds to the main world of evaluation"""
    # test_print = [ext["prefix expression"] for ext in self.extensional_propositions]
    # print(test_print)
    for ext_proposition in self.extensional_propositions:
        # print([bitvec_to_substates(bv, self.N) for bv in ext_proposition["verifiers"]])
        ext_proposition.print_possible_verifiers_and_falsifiers(output)
        ext_proposition.print_alt_worlds(output)

# removed from model_structure after redid how we do alt worlds and what not
        # was a method of Proposition objects
def print_possible_verifiers_and_falsifiers(self, output=sys.__stdout__):
    """prints the possible verifiers and falsifier states for a sentence.
    inputs: the verifier states and falsifier states.
    Outputs: None, but prints the verifiers and falsifiers
    Used in print_prop()"""
    N = self.parent_model_structure.N
    possible = self.parent_model_structure.possible
    model = self.parent_model_structure.model
    ver_states = {
        bitvec_to_substates(bit, N)
        for bit in self["verifiers"]
        if model.evaluate(possible(bit))
    }
    fal_states = {
        bitvec_to_substates(bit, N)
        for bit in self["falsifiers"]
        if model.evaluate(possible(bit))
    }
    if ver_states and fal_states:
        print(
            f"  |{self}| = < {make_set_pretty_for_print(ver_states)}, {make_set_pretty_for_print(fal_states)} >",
            file=output,
        )
    elif ver_states and not fal_states:
        print(
            f"  |{self}| = < {make_set_pretty_for_print(ver_states)}, ∅ >",
            file=output,
        )
    elif not ver_states and fal_states:
        print(
            f"  |{self}| = < ∅, {make_set_pretty_for_print(fal_states)} >",
            file=output,
        )
    else:
        print(f"  |{self}| = < ∅, ∅ >", file=output)

# removed from model_structure after redid how we do alt worlds and what not
# was a method of Proposition objects
def print_alt_worlds(self, output=sys.__stdout__):
    """prints everything that has to do with alt worlds
    Used in print_prop()
    Takes in a proposition. Note that this proposition has itself a input world.
    This is not inputted into the method, but accessed. So, need to make sure, before the method
    is called, that the proposition has the proper input world before calling the function
    """
    N = self.parent_model_structure.N
    input_world = self["input world"]
    # model = self.parent_model_structure.model  # ModelRef object (unused)
    alt_worlds = {bitvec_to_substates(alt, N) for alt in self["alternative worlds"]}
    if alt_worlds:
        print(
            f"  {self}-alternatives to {bitvec_to_substates(input_world, N)} = {make_set_pretty_for_print(alt_worlds)}",
            file=output,
        )
        for alt_bit in self["alternative worlds"]:
            true_in_alt, false_in_alt = find_true_and_false_in_alt(
                alt_bit, self.parent_model_structure
            )
            print_alt_relation(true_in_alt, alt_bit, "true", N, output)
            print_alt_relation(false_in_alt, alt_bit, "not true", N, output)
        print(file=output)  # for an extra blank line
    else:
        print(
            f"  There are no {self}-alternatives to {bitvec_to_substates(input_world, N)}",
            file=output,
        )
        print(file=output)  # for an extra blank line

# removed from model_structure after redid how we do alt worlds and what not
# was a method of Proposition objects
def update_comparison_world(self, new_world):
    """updates the input world (which is a BitVecVal) to a new one; updates
    the alt worlds based on that
    returns None"""
    if new_world == self["input world"]:
        return
    model_structure = self.parent_model_structure
    if isinstance(self, Extensional):
        self["alternative worlds"] = model_structure.find_alt_bits(
            self["verifiers"], new_world
        )
    self["input world"] = new_world

# from model definitions, usurped by a function that does all of these generally
def find_extensional_subsentences(prefix_sentences):
        '''finds all the extensional subsentences in a list of prefix sentences
        used in find_all_constraints'''
        # all_subsentences = [all_subsentences_of_a_sentence(sent) for sent in prefix_sentences]
        all_subsentences = []
        for prefix_sent in prefix_sentences:
            # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
            all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
        extensional_subsentences = [sent for sent in all_subsentences if not is_counterfactual(sent)]
        return repeats_removed(extensional_subsentences)
def find_cf_subsentences(prefix_sentences):
    '''finds all the counterfactual subsentences in a list of prefix sentences
    used in find_all_constraints'''
    # all_subsentences = [all_subsentences_of_a_sentence(sent) for sent in prefix_sentences]
    all_subsentences = []
    for prefix_sent in prefix_sentences:
        # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
        all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
    cf_subsentences = [sent for sent in all_subsentences if is_counterfactual(sent)]
    return repeats_removed(cf_subsentences)

# from model defintions, idk what it was replaced by 
def print_alt_relation(alt_relation_set, alt_bit, relation_truth_value, N,output=sys.__stdout__):
    """true is a string representing the relation ("true" for true_in_alt; m.m. for false) that is being used for
    alt_relation_set is the set of prefix sentences that have truth value relation_truth_value in a
    given alternative world alt_bit
    returns None, only prints
    Used in print_alt_worlds()"""
    if not alt_relation_set:
        return
    alt_relation_list = sorted([Infix(sent) for sent in alt_relation_set])
    alt_relation_string = ", ".join(alt_relation_list)
    if len(alt_relation_set) == 1:
        print(
            f"    {alt_relation_string} is {relation_truth_value} in {bitvec_to_substates(alt_bit, N)}",
            file=output
        )
    else:
        print(
            f"    {alt_relation_string} are {relation_truth_value} in {bitvec_to_substates(alt_bit, N)}",
            file=output
        )