from definitions import *
from print import *
from semantics import *

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


def find_alt_bits(ver_bits, poss_bits, world_bits, eval_world):
    """
    Finds the alternative bits given verifier bits, possible states, worlds, and
    the evaluation world. Used in find_relations().
    """
    alt_bits = set()
    # print(f"poss_bits = {poss_bits}")
    # print(f"world_bits = {world_bits}")
    # print(f"eval_world = {eval_world}")
    for ver in ver_bits:
        # print(f"ver_bit = {ver}")
        comp_parts = find_compatible_parts(ver, poss_bits, eval_world)
        # print(f"comp_parts = {comp_parts}")
        max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
        # print(f"max_comp_parts = {max_comp_ver_parts}")
        for world in world_bits:
            if not bit_part(ver, world):
                continue
            for max_ver in max_comp_ver_parts:
                if bit_part(max_ver, world) and world.sexpr() != eval_world.sexpr():
                    alt_bits.add(world)
                    # print(f"world = {world} = {world.sexpr()}")
                    # print(f"eval_world = {eval_world} = {eval_world.sexpr()}")
                    break  # to return to the second for loop over world_bits
    return alt_bits


def relate_sents_and_states(all_bits, sentence, model, relation):
    """helper function for finding verifier and falsifier states to sentences in a model
    Used in find_relations()"""
    relation_set = set()
    for bit in all_bits:
        if model.evaluate(relation(bit, model[sentence])):
            relation_set.add(bit)
    return relation_set


def find_relations(all_bits, S, model):
    """for a given sentence letter S and a list all_bits and a model, finds the relations verify, falsify, and alt_bits for that sentence in that model
    returns a tuple (ver_states, fal_states, alt_bits)
    Used in print_prop()"""
    ver_bits = relate_sents_and_states(all_bits, S, model, verify)
    fal_bits = relate_sents_and_states(all_bits, S, model, falsify)
    poss_bits = find_poss_bits(model,all_bits)
    world_bits = find_world_bits(poss_bits)
    eval_world = model[w]
    alt_bits = find_alt_bits(ver_bits, poss_bits, world_bits, eval_world)
    return (ver_bits, fal_bits, alt_bits)


def find_true_and_false_in_alt(alt_bit, sentence_letters, all_bits, model):
    """returns two sets as a tuple, one being the set of sentences true in the alt world and the other the set being false.
    Used in print_alt_worlds()"""
    true_in_alt = set()
    for R in sentence_letters:
        for bit in all_bits:
            if model.evaluate(verify(bit, model[R])) and bit_part(bit, alt_bit):
                true_in_alt.add(R)
                break  # returns to the for loop over sentence_letters
    false_in_alt = {R for R in sentence_letters if not R in true_in_alt}
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

class ModelStructure():
    def __init__(self, input_premises, input_conclusions, N):
        self.premises = input_premises
        self.conclusions = input_conclusions
        self.input_sentences = combine(input_premises, input_conclusions)
        constraints, sentence_letters = find_all_constraints(self.input_sentences)

    def print_model(self):
        pass


