from definitions import (
    bit_fusion,
    bit_part,
    bit_proper_part,
    bitvec_to_substates,
    summation,
    possible,
    verify,
    falsify,
    w,
)
from z3 import (
    BitVecVal,
)

from convert_syntax import Infix

def find_all_bits(size):
    '''extract all bitvectors from the input model'''
    all_bits = []
    max_bit_number = summation(
        size + 1, lambda x: 2**x
    )  # this should hopefully be enough to cover all states
    for val in range(max_bit_number):
        test_bit = BitVecVal(val, size)
        if test_bit in all_bits:
        # break once bits start to repeat
            continue
        all_bits.append(test_bit)
    return all_bits


def find_poss_bits(model,all_bits):
    '''extract all possible bitvectors from all_bits given the model'''
    poss_bits = []
    for bit in all_bits:
        if model.evaluate(possible(bit)): # of type/sort BoolRef
            poss_bits.append(bit)
    return poss_bits


def find_world_bits(poss_bits):
    '''finds the world bits from a list of possible bits.
    used in print_states() and find_relations()'''
    not_worlds = []
    for potential_world in poss_bits:
        if potential_world in not_worlds:
            continue
        for test in poss_bits:
            if bit_part(test, potential_world):
                continue
            if bit_proper_part(potential_world, test):
                not_worlds.append(potential_world)
                break
    world_bits = [world for world in poss_bits if world not in not_worlds]
    # for world in world_bits:
    #     print(model.evaluate(is_world(world)))
    #     if not model.evaluate(is_world(world)):
    #         raise ValueError(f'{world} was in world_bits but is not a world per the model')
    # for not_world in not_worlds:
    #     print(model.evaluate(is_world(not_world)))
    #     # if model.evaluate(is_world(not_world)):
    #     #     raise ValueError(f'{not_world} was not in world_bits but is a world per the model')
    return world_bits


def find_compatible_parts(verifier_bit, poss_bits, eval_world):
    """
    Finds the parts of the eval_world compatible with the verifier_bit.
    Used in find_alt_bits()
    """
    comp_parts = []
    for part in poss_bits:
        if bit_fusion(verifier_bit, part) in poss_bits and bit_part(part, eval_world):
            comp_parts.append(part)
            # ie, if fusion is possible and the bit part is in the eval_world
    return comp_parts


def find_max_comp_ver_parts(verifier_bit, comp_parts):
    """
    Finds a list of fusions of the verifier_bit and a maximal compatible part.
    Used in find_alt_bits(), immediately after find_compatible_parts() above.
    """
    not_max_comp_part = []
    for max_part in comp_parts:
        for test in comp_parts:
            if bit_proper_part(max_part, test):
                not_max_comp_part.append(max_part)
                break  # continues with the first for loop
    max_comp_parts = [part for part in comp_parts if part not in not_max_comp_part]
    max_comp_ver_parts = [bit_fusion(verifier_bit, max) for max in max_comp_parts]
    return max_comp_ver_parts

def relate_sents_and_states(all_bits, sentence, model, relation):
    """helper function for finding verifier and falsifier states to sentences in a model
    Used in find_relations()
    DOES NOT CHECK IF THESE ARE POSSIBLE. """
    relation_set = set()
    for bit in all_bits:
        if model.evaluate(relation(bit, model[sentence])):
            relation_set.add(bit)
    return relation_set

def find_true_and_false_in_alt(alt_bit, parent_model_structure):
    """returns two sets as a tuple, one being the set of sentences true in the alt world and the other the set being false.
    Used in Proposition class print_alt_worlds"""
    extensional_sentences = parent_model_structure.extensional_subsentences
    all_bits = parent_model_structure.all_bits
    true_in_alt = []
    for R in extensional_sentences:
        for bit in all_bits:
            # print(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True))
            # print(type(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True)))
            if bit in parent_model_structure.find_complex_proposition(R)[0] and bit_part(bit, alt_bit):
                true_in_alt.append(R)
                break  # returns to the for loop over sentence_letters
    false_in_alt = [R for R in extensional_sentences if not R in true_in_alt] # replace with 
    return (true_in_alt, false_in_alt)


def make_set_pretty_for_print(set_with_strings):
    """input a set with strings
    print that same set but with no quotation marks around each individual string, and also with the set in order
    returns the set as a string
    Used in print_vers_and_fals() and print_alt_worlds()"""
    sorted_set = sorted(list(set_with_strings))  # actually type list, not set
    print_str = "{"
    for i, elem in enumerate(sorted_set):
        print_str += elem
        if i != len(sorted_set) - 1:
            print_str += ", "
    print_str += "}"
    return print_str

def product(set_A, set_B):
    product_set = set()
    for a in set_A:
        for b in set_B:
            product_set.add(bit_fusion(a,b))
    return product_set

def coproduct(set_A, set_B):
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))

def atomic_propositions_dict(all_bits, sentence_letters, model):
    atomic_VFs_dict = {}
    for letter in sentence_letters:
        ver_bits = relate_sents_and_states(all_bits, letter, model, verify)
        fal_bits = relate_sents_and_states(all_bits, letter, model, falsify)
        atomic_VFs_dict[letter] = (ver_bits, fal_bits)
    return atomic_VFs_dict

def print_alt_relation(alt_relation_set, alt_bit, relation_truth_value):
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
        print(f"    {alt_relation_string} is {relation_truth_value} in {bitvec_to_substates(alt_bit)}")
    else:
        print(f"    {alt_relation_string} are {relation_truth_value} in {bitvec_to_substates(alt_bit)}")
