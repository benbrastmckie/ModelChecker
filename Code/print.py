from z3 import (
    BitVecVal,
)
from semantics import (
    w,
)
from user_input import N
from definitions import (
    # N,
    bit_fusion,
    bit_part,
    bit_proper_part,
    possible,
    verify,
    falsify,
    bitvec_to_substates,
    summation,
    int_to_binary,
)

'''
the three main functions are print_states(), print_evaluations(), and print_propositions().
all other functions feed into print_propositions()
'''

# TODO: abstract functions to define a data class in `model_builder.py`




################################
### MODEL BUILDER DEFINITIONS ##
################################


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
                if bit_part(max_ver, world): # and world.sexpr() != eval_world.sexpr():
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

# Note to self: this has kind of been rendered obsolete in the model_structure file
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


################################
### START PRINT DEFINITIONS ####
################################


# NOTE: should N be included in the inputs?
def print_states(model):
    """print all fusions of atomic states in the model"""
    all_bits = find_all_bits(N)
    poss_bits = find_poss_bits(model,all_bits)
    world_bits = find_world_bits(poss_bits)

    # print("\n(Possible) States:")  # Print states
    print("\nStates:")  # Print states
    for bit in all_bits:
        # test_state = BitVecVal(val, size) # was instead of bit
        state = bitvec_to_substates(bit)
        bin_rep = (
            bit.sexpr()
            if N % 4 != 0
            else int_to_binary(int(bit.sexpr()[2:], 16), N)
        )
        if bit in world_bits:
            print(f"  {bin_rep} = {state} (world)")
        elif model.evaluate(possible(bit)):
            print(f"  {bin_rep} = {state} (possible)")
        else:
            # print(f"  {bin_rep} = {state} (impossible)")
            continue


# NOTE: should N be included in the inputs?
def print_evaluation(model, sentence_letters):
    """print the evaluation world and all sentences true/false in that world
    sentence letters is an iterable (a list, I think?)"""
    all_bits = find_all_bits(N)
    eval_world = model[w]
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}:")
    true_in_eval = set()
    for sent in sentence_letters:
        for bit in all_bits:
            if model.evaluate(verify(bit, model[sent])) and bit_part(bit, eval_world):
                true_in_eval.add(sent)
                break  # exits the first for loop
    false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
    if true_in_eval:
        true_eval_list = sorted([str(sent) for sent in true_in_eval])
        true_eval_string = ", ".join(true_eval_list)
        print(f"  {true_eval_string}  (true in {bitvec_to_substates(model[w])})")
    if false_in_eval:
        false_eval_list = sorted([str(sent) for sent in false_in_eval])
        false_eval_string = ", ".join(false_eval_list)
        print(f"  {false_eval_string}  (not true in {bitvec_to_substates(model[w])})")


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


def print_propositions(model, sentence_letters):
    """print each propositions and the alternative worlds in which it is true"""
    all_bits = find_all_bits(N)
    print("\nPropositions:")
    for S in sentence_letters:
        ver_states, fal_states, alt_bits = find_relations(all_bits, S, model)
        print_vers_and_fals(model, S, ver_states, fal_states)
        print_alt_worlds(all_bits, S, sentence_letters, model, alt_bits)


def print_model(result, model, input_sent, sentence_let):
    """print the elements of the model"""
    if result:
        # print(f"\nModel time: {time}")
        print(f"\nThere is an {N}-model of:\n")
        for sent in input_sent:
            print(sent)
        print_states(model)
        print_evaluation(model, sentence_let)
        print_propositions(model, sentence_let)
    # # NOTE: use to look for problem cases
    else:
        print(f"\nThere are no {N}-models of:\n")
        for sent in input_sent:
            print(sent)
        print("\nUnsatisfiable core:\n") # NOTE: what is the unsat core supposed to do?
        print_constraints(model)
    # else:
    #     print(f"\nThere are no {N}-models of:\n")
    #     for sent in input_sent:
    #         print(sent)
    #     print()


def print_constraints(consts, time):
    """prints constraints in an numbered list"""
    for index, con in enumerate(consts, start=1):
        print(f"{index}. {con}\n")
        print(f"Constraints time: {time}\n")
