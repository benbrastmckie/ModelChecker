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
)

# TODO: define alternatives rather than declaring 'alternative' in Z3

# QUESTION: I wonder if it would be better to work with states in bitvector
# form since I imagine it will be easier and faster to operate on them.

# TODO: I suspect there is something wrong with is_bitvector below since it
# seems to include outputs x, s, w, t, u, y, k!491 when N = 5
# is this related to the cap on states below 26? would be good to use
# subscripts if more states are needed

def print_states(model):
    '''print all fusions of atomic states in the model'''
    all_bits = {model[element] for element in model.decls() if is_bitvector(element)}
    bits_as_nums = [bit.as_long() for bit in all_bits]
    # possible_states = [bitvec_to_substates(BitVecVal(val, N)) for val in range(max_num * 2) if model.evaluate(possible(val))]
    possible_bits = [bit for bit in all_bits if model.evaluate(possible(bit))]
    world_bits = possible_bits
    for world in world_bits:
    # what is this for loop doing?
    # B: this is my attempt to define the worlds (as bits) given only possible_bits
    # it starts with all possible_bits and then kicks out any that are proper parts
    # of any possible_bit, thereby capturing the maximality of worlds. I trust there
    # are better ways to do this.
        for poss in possible_bits:
            if bit_proper_part(world, poss):
                world_bits.remove(world)
                break

    print("\nStates:")  # Print states
    max_num = max(bits_as_nums)
    already_seen = set()
    for val in range(max_num * 2):
        test_state = BitVecVal(val, N)
        as_substates = bitvec_to_substates(test_state)
        if test_state in already_seen:
            break
        if test_state in world_bits:
            print(f"  {test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"  {test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)


def print_evaluation(model, sentence_letters):
    '''print the evaluation world and all sentences true/false in that world
    sentence letters is an iterable (a list, I think?)'''
    all_bits = [model[element] for element in model.decls() if is_bitvector(element)]
    eval_world = model[w]
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}:")
    true_in_eval = set()
    for sent in sentence_letters:
        for bit in all_bits:
            if model.evaluate(verify(bit, model[sent])) and bit_part(bit, eval_world):
                true_in_eval.add(sent)
                break
    # what is the for loop doing?
    # B: this is my attempt to determine which sentences have verifiers in the evaluation world,
    # including just those sentences in true_in_eval. for each sentence letter and bit, the loop
    # checks if that bit is a part of the eval_world and verifies the sentence letter. as soon as
    # it finds a bit that is a part of the eval world that verifies the sentence, it adds it to
    # the true_in_eval set and breaks out of the loop since we only need one verifier to make the
    # sentence true and be a part of the eval_world.
    false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
    if true_in_eval:
        true_eval_list = sorted([str(sent) for sent in true_in_eval])
        true_eval_string = ", ".join(true_eval_list)
        print("  " + true_eval_string + f"  (true in {bitvec_to_substates(model[w])})")
    if false_in_eval:
        false_eval_list = sorted([str(sent) for sent in false_in_eval])
        false_eval_string = ", ".join(false_eval_list)
        print("  " + false_eval_string + f"  (not true in {bitvec_to_substates(model[w])})")


# BELOW is everything that was once in the big original function print_propositions.
def relate_sents_and_states(all_bits, sentence, model, relation):
    '''helper function for finding verifier and falisifer states to sentences in a model'''
    return {
            bit
            for bit in all_bits
            if model.evaluate(relation(bit, model[sentence]))
        }


def find_relations(all_bits, S, model):
    '''for a given sentence letter S and a list all_bits and a model, finds the relations verify, falsify, alt_num_worlds, and alt_worlds for that sentence in that model
    returns a tuple (ver_states, fal_states, alt_num_worlds, alt_worlds)'''
    ver_bits = relate_sents_and_states(all_bits, S, model, verify)
    fal_bits = relate_sents_and_states(all_bits, S, model, falsify)
    ver_states = {
        bitvec_to_substates(bit)
        for bit in ver_bits
    }
    fal_states = {
        bitvec_to_substates(bit)
        for bit in fal_bits
    }
    poss_bits = [element for element in all_bits if model.evaluate(possible(element))]
    world_bits = poss_bits
    copy_wbits = poss_bits
    for world in copy_wbits:
        for poss in poss_bits:
            if bit_proper_part(world, poss):
                world_bits.remove(world)
                break
    eval_world = model[w]
    # TODO: define alt_worlds in some better way
    # TODO: use bits until printing states
    alt_num_worlds = set()
    for ver in ver_bits:
        comp_parts = set()
        for part in poss_bits:
            if bit_fusion(ver, part) in poss_bits:
                if bit_part(part, eval_world):
                    comp_parts.add(part)
        max_comp_parts = comp_parts
        copy_mcp = comp_parts
        for max_part in copy_mcp:
            for test in comp_parts:
                if bit_proper_part(max_part, test):
                    max_comp_parts.remove(max_part)
                    break
        max_comp_ver_parts = {
            bit_fusion(ver, max)
            for max in max_comp_parts
        }
        for world in world_bits:
            for max_ver in max_comp_ver_parts:
                if bit_part(max_ver, world):
                    alt_num_worlds.add(world)
    alt_worlds = {
        bitvec_to_substates(alt)
        for alt in alt_num_worlds
    }
    return (ver_states, fal_states, alt_num_worlds, alt_worlds)


def print_vers_and_fals(S, ver_states, fal_states):
    '''prints the verifiers and falsifier states for a Sentence.
    inputs: the verifier states and falsifier states. 
    Outputs: None, but prints the stuff we want printed'''
    if ver_states and fal_states:
        print(f"  |{S}| = < {make_set_pretty_for_print(ver_states)}, {make_set_pretty_for_print(ver_states)} >")
    elif ver_states and not fal_states:
        print(f"  |{S}| = < {make_set_pretty_for_print(ver_states)}, ∅ >")
    elif not ver_states and fal_states:
        print(f"  |{S}| = < ∅, {make_set_pretty_for_print(ver_states)} >")
    else:
        print(f"  |{S}| = < ∅, ∅ >")

def print_alt_worlds(all_bits, S, sentence_letters, model, alt_num_worlds, alt_worlds):
    '''prints everything that has to do with alt worlds'''
    if alt_worlds:
        print(f"  {S}-alternatives to {bitvec_to_substates(model[w])} = {make_set_pretty_for_print(alt_worlds)}")
        # TODO: not sure how to sort alt_worlds and alt_num_worlds so that they appear in order
        for alt_num in alt_num_worlds:
            true_in_alt = set()
            for sent in sentence_letters:
                for bit in all_bits:
                    # NOTE: replacing string_part with bit_part works but makes the linter angry
                    if model.evaluate(verify(bit, model[sent])) and bit_part(bit, alt_num):
                        true_in_alt.add(sent)
                        break
            false_in_alt = {R for R in sentence_letters if not R in true_in_alt}
            if true_in_alt:
                true_alt_list = sorted([str(sent) for sent in true_in_alt])
                true_alt_string = ", ".join(true_alt_list)
                if len(true_in_alt) == 1:
                    print(f"    {true_alt_string} is true in {bitvec_to_substates(alt_num)}")
                else:
                    print(f"    {true_alt_string} are true in {bitvec_to_substates(alt_num)}")
            if false_in_alt:
                false_alt_list = sorted([str(sent) for sent in false_in_alt])
                false_alt_string = ", ".join(false_alt_list)
                if len(false_in_alt) == 1:
                    print(f"    {false_alt_string} is not true in {bitvec_to_substates(alt_num)}")
                else:
                    print(f"    {false_alt_string} are not true in {bitvec_to_substates(alt_num)}")
        print()

    else:
        print(f"  There are no {S}-alternatives to {bitvec_to_substates(model[w])}")
        print()

def print_prop(all_bits, S, sentence_letters, model):
    '''prints all the stuff for one proposition. returns None'''
    ver_states, fal_states, alt_num_worlds, alt_worlds = find_relations(all_bits, S, model)
    # Print propositions:
    print_vers_and_fals(S, ver_states, fal_states)
    print_alt_worlds(all_bits, S, sentence_letters, model, alt_num_worlds, alt_worlds)

def print_propositions(model, sentence_letters):
    # TODO: too many branches? can this be simplified?
    # TODO: I couldn't figure out how to remove the quotes from the states
    # NOTE: seems like it might be better to use sorted lists than sets as below?
    '''
    print each propositions and the alternative worlds in which it is true
    '''
    all_bits = {model[element] for element in model.decls() if is_bitvector(element)}
    print("\nPropositions:")
    for S in sentence_letters:
        print_prop(all_bits, S, sentence_letters, model)

def make_set_pretty_for_print(set_with_strings):
    '''input a set with strings
    print that same set but with no quotation marks around each individual string, and also with the set in order
    returns the set as a string'''
    sorted_set = sorted(list(set_with_strings)) # actually a list, unlike name suggests
    print_str = "{"
    for i, elem in enumerate(sorted_set):
        print_str += elem
        if i != len(sorted_set) - 1:
            print_str += ', '
    print_str += "}"
    return print_str
