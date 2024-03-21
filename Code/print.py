from z3 import (
    BitVecVal,
)

from definitions import (
    N,
    bit_fusion,
    bit_part,
    bit_proper_part,
    w,
    possible,
    verify,
    falsify,
    bitvec_to_substates,
    is_bitvector,
    summation,
    int_to_binary,
)

# Organizational note
# the three main functions are print_states(), print_evaluations(), and print_propositions().
# all other functions feed into print_propositions()

# TODO: restructure towards defining a data class
# NOTE: this is looking really good! eventually we will want to be building a data class
# or something like that. with an eye towards this, it would be good to separate the
# printing functions from the model_builder functions (i.e., extracting all_bits, poss_bits,
# and world_bits from the model) and the eval_builder elements (i.e., defining functions
# from each atom to ver_bits,fal_bits, and a function from each atom and eval_world to alt_bits).
# the thought is that model_builder and eval_builder can be used to build a data class where
# the print functions will then operate on that data class. but it seems that we now have
# all the key ingredients that we need.
# M: Sounds good! I'm guessing that may be better to do once we finish semantics and all that?
# B: Yes, that sounds good! I will start working on that now

# TODO: define helper function from model to eval_world, all_bits, poss_bits, world_bits,
# NOTE: all_bits should include all relevant states

# TODO: define helper function from model, sentence_letters, and eval_world to: true_in_eval, ver_bits, fal_vits, alt_bits, and true_in_alt


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

# NOTE: below was added to above for comparison
# def find_bits(size, model):
    # model_bits = {
    #     model[element]
    #     for element in model.decls()
    #     if is_bitvector(model[element])
    # }
    # return (all_bits, model_bits)


def find_poss_bits(model,all_bits):
    '''extract all possible bitvectors from all_bits given the model'''
    poss_bits = []
    for bit in all_bits:
        if model.evaluate(possible(bit)):
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
    return world_bits


# NOTE: should N be included in the inputs?
def print_states(model):
    """print all fusions of atomic states in the model"""
    all_bits = find_all_bits(N)
    poss_bits = find_poss_bits(model,all_bits)
    world_bits = find_world_bits(poss_bits)

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
            print(f"  {bin_rep} = {state} (impossible)")
            # continue


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
            if model.evaluate(verify(bit, model[sent])) and bool(bit_part(bit, eval_world)):
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


################################
#### END PRINT STATES/EVALS ####
################################


################################
### START PRINT PROPOSITIONS ###
################################


def relate_sents_and_states(all_bits, sentence, model, relation):
    """helper function for finding verifier and falisifer states to sentences in a model
    Used in find_relations()"""
    return {bit for bit in all_bits if model.evaluate(relation(bit, model[sentence]))}


def find_compatible_parts(verifier_bit, poss_bits, eval_world):
    """Finds the parts of the eval_world compatible with a verifier.
    Used in find_alt_bits()"""
    comp_parts = []
    for part in poss_bits:
        if bit_fusion(verifier_bit, part) in poss_bits and bool(bit_part(part, eval_world)):
            comp_parts.append(part)
            # ie, if fusion is possible and the bit part is in the eval_world
    return comp_parts


def find_max_comp_ver_parts(verifier_bit, comp_parts):
    """Finds a list of fusions of the verifier_bit and a maximal compatible part 
    Used in find_alt_bits(), immediately after find_compatible_parts() above"""
    not_max_comp_part = []
    for max_part in comp_parts:
        for test in comp_parts:
            if bit_proper_part(max_part, test):
                not_max_comp_part.append(max_part)
                break  # exits the first for loop
    max_comp_parts = [part for part in comp_parts if part not in not_max_comp_part]
    max_comp_ver_parts = [bit_fusion(verifier_bit, max) for max in max_comp_parts]
    return max_comp_ver_parts


def find_alt_bits(ver_bits, poss_bits, world_bits, eval_world):
    """finds the alternative bits given verifier states, possible states, worlds, and the model.
    Used in find_relations()"""
    alt_bits = set()
    # eval_world = model[w] moved eval_world to find_relations... is that what you had in mind?
    # this means that w is ALWAYS the eval world... we must ensure this
    # TODO: we may abstract on eval_world, adding it to the inputs
    # this will make the function useful for nested counterfactuals
    for ver in ver_bits:
        comp_parts = find_compatible_parts(ver, poss_bits, eval_world)
        max_comp_ver_parts = find_max_comp_ver_parts(ver, comp_parts)
        for world in world_bits:
            for max_ver in max_comp_ver_parts:
                if bool(bit_part(max_ver, world)) and world.sexpr() != eval_world.sexpr():
                    alt_bits.add(world)
                    break  # to break out of first for loop
    return alt_bits


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


def print_vers_and_fals(S, ver_bits, fal_bits):
    """prints the verifiers and falsifier states for a Sentence.
    inputs: the verifier states and falsifier states.
    Outputs: None, but prints the stuff we want printed
    Used in print_prop()"""
    ver_states = {bitvec_to_substates(bit) for bit in ver_bits}
    fal_states = {bitvec_to_substates(bit) for bit in fal_bits}
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


def find_true_and_false_in_alt(alt_bit, sentence_letters, all_bits, model):
    """returns two sets as a tuple, one being the set of sentences true in the alt world and the other the set being false.
    Used in print_alt_worlds()"""
    true_in_alt = set()
    for R in sentence_letters:
        for bit in all_bits:
            if model.evaluate(verify(bit, model[R])) and bool(bit_part(bit, alt_bit)):
                true_in_alt.add(R)
                break  # breaks the `for bit in all_bits` for loop, NOT the big for loop
    false_in_alt = {R for R in sentence_letters if not R in true_in_alt}
    return (true_in_alt, false_in_alt)


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
        print_vers_and_fals(S, ver_states, fal_states)
        print_alt_worlds(all_bits, S, sentence_letters, model, alt_bits)


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
