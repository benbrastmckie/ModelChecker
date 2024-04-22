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

def find_complex_proposition(complex_sentence, atomic_props_dict):
    """sentence is a sentence in prefix notation
    For a given complex proposition, returns the verifiers and falsifiers of that proposition
    given a solved model"""
    if not atomic_props_dict:
        raise ValueError("There is nothing in atomic_props_dict yet. Have you actually run the model?")
    if len(complex_sentence) == 1:
        sent = complex_sentence[0]
        return atomic_props_dict[sent]
    op = complex_sentence[0]
    if "neg" in op:
        return (atomic_props_dict[complex_sentence][1], atomic_props_dict[complex_sentence][0])
    Y = complex_sentence[1]
    Z = complex_sentence[2]
    Y_V = find_complex_proposition(Y)[0]
    Y_F = find_complex_proposition(Y)[1]
    Z_V = find_complex_proposition(Z)[0]
    Z_F = find_complex_proposition(Z)[1]
    if "wedge" in op:
        return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
    if "vee" in op:
        return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
    if "leftrightarrow" in op:
        return (product(coproduct(Y_F, Z_V), coproduct(Y_V, Z_F)),
                coproduct(product(Y_V, Z_F), product(Y_F, Z_V)))
    if "rightarrow" in op:
        return (coproduct(Y_F, Z_V), product(Y_V, Z_F))
    if "boxright" in op:
        raise ValueError("don't knowhow to handle boxright case yet")


def find_alt_bits(ver_bits, poss_bits, world_bits, eval_world):
    """
    Finds the alternative bits given verifier bits, possible states, worlds, and
    the evaluation world. Used in find_relations().
    """
    alt_bits = set()
    for ver in ver_bits:
        comp_parts = find_compatible_parts(ver, poss_bits, eval_world)
        max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
        for world in world_bits:
            if not bit_part(ver, world):
                continue
            for max_ver in max_comp_ver_parts:
                if bit_part(max_ver, world) and world.sexpr() != eval_world.sexpr():
                    alt_bits.add(world)
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

# Note to self: this will be rendered obsolete in the model_structure file
# but leave it for now because it's still needed bc problem is not completely solved yet
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

def product(set_A, set_B):
    product_set = set()
    for a in set_A:
        for b in set_B:
            product_set.add(bit_fusion(a,b)) # NOTE: pretty sure it should be bit_fusion and not fusion, but not certain

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



###############################################
##### STUFF WITH PROPS FROM PRINT.PY THAT #####
##### WE EVENTUALLY WANNA GET RID OF BUT  #####
##### HAVEN'T FOUND A WAY TO YET          #####
###############################################
def print_vers_and_fals(model, S, ver_bits, fal_bits):
    """prints the possible verifiers and falsifier states for a sentence.
    inputs: the verifier states and falsifier states.
    Outputs: None, but prints the verifiers and falsifiers
    Used in print_prop()"""
    ver_states = {bitvec_to_substates(bit) for bit in ver_bits if model.evaluate(possible(bit))}
    fal_states = {bitvec_to_substates(bit) for bit in fal_bits if model.evaluate(possible(bit))}
    if ver_states and fal_states:
        print(
            f"  |{S}| = < {make_set_pretty_for_print(ver_states)}, {make_set_pretty_for_print(fal_states)} >"
        )
    elif ver_states and not fal_states:
        print(f"  |{S}| = < {make_set_pretty_for_print(ver_states)}, ∅ >")
    elif not ver_states and fal_states:
        print(f"  |{S}| = < ∅, {make_set_pretty_for_print(fal_states)} >")
    else:
        print(f"  |{S}| = < ∅, ∅ >")


def print_alt_relation(alt_relation_set, alt_bit, relation_truth_value):
    """true is a string representing the relation ("true" for true_in_alt; m.m. for false) that is being used for
    returns None, only prints
    Used in print_alt_worlds()"""
    if not alt_relation_set:
        return
    alt_relation_list = sorted([str(sent) for sent in alt_relation_set])
    alt_relation_string = ", ".join(alt_relation_list)
    if len(alt_relation_set) == 1:
        print(f"    {alt_relation_string} is {relation_truth_value} in {bitvec_to_substates(alt_bit)}")
    else:
        print(f"    {alt_relation_string} are {relation_truth_value} in {bitvec_to_substates(alt_bit)}")


def print_alt_worlds(all_bits, S, sentence_letters, model, alt_bits):
    """prints everything that has to do with alt worlds
    Used in print_prop()"""
    alt_worlds = {bitvec_to_substates(alt) for alt in alt_bits}
    if alt_worlds:
        print(f"  {S}-alternatives to {bitvec_to_substates(model[w])} = {make_set_pretty_for_print(alt_worlds)}")
        for alt_bit in alt_bits:
            true_in_alt, false_in_alt = find_true_and_false_in_alt(
                alt_bit, sentence_letters, all_bits, model
            )
            print_alt_relation(true_in_alt, alt_bit, "true")
            print_alt_relation(false_in_alt, alt_bit, "not true")
        print()  # for an extra blank line
    else:
        print(f"  There are no {S}-alternatives to {bitvec_to_substates(model[w])}")
        print()  # for an extra blank line


# NOTE: I added this to ModelStructure but I'm not sure this is best
# def print_propositions(model, sentence_letters):
#     """print each propositions and the alternative worlds in which it is true"""
#     # from test_complete import N
#     all_bits = find_all_bits(N)
#     print("\nPropositions:")
#     for S in sentence_letters:
#         ver_states, fal_states, alt_bits = find_relations(all_bits, S, model)
#         print_vers_and_fals(model, S, ver_states, fal_states)
#         print_alt_worlds(all_bits, S, sentence_letters, model, alt_bits)
