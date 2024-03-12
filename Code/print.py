from z3 import (
    BitVecVal,
)

from definitions import (
    N,
    bit_part,
    bit_proper_part,
    w,
    possible,
    verify,
    falsify,
    alternative,
    bitvec_to_substates,
    string_part,
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
    max_num = max(bits_as_nums)
    # possible_states = [bitvec_to_substates(BitVecVal(val, N)) for val in range(max_num * 2) if model.evaluate(possible(val))]
    possible_bits = [bit for bit in all_bits if model.evaluate(possible(bit))]
    world_bits = possible_bits
    for world in world_bits:
        for poss in possible_bits:
            if bit_proper_part(world, poss):
                world_bits.remove(world)
                break

    print("\nStates:")  # Print states
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
    '''print the evaluation world and all sentences true/false in that world'''
    all_bits = [model[element] for element in model.decls() if is_bitvector(element)]
    eval_world = model[w]
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}:")
    true_in_eval = set()
    for sent in sentence_letters:
        for bit in all_bits:
            if model.evaluate(verify(bit, model[sent])) and bit_part(bit, eval_world):
                true_in_eval.add(sent)
                break
    false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
    if true_in_eval:
        true_eval_list = sorted([str(sent) for sent in true_in_eval])
        true_eval_string = ", ".join(true_eval_list)
        print("  " + true_eval_string + f"  (true in {bitvec_to_substates(model[w])})")
    if false_in_eval:
        false_eval_list = sorted([str(sent) for sent in false_in_eval])
        false_eval_string = ", ".join(false_eval_list)
        print("  " + false_eval_string + f"  (not true in {bitvec_to_substates(model[w])})")


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
        ver_states = {  # verifier states for S
            bitvec_to_substates(bit)
            for bit in all_bits
            if model.evaluate(verify(bit, model[S]))
        }
        fal_states = {  # falsifier states for S
            bitvec_to_substates(bit)
            for bit in all_bits
            if model.evaluate(falsify(bit, model[S]))
        }
        alt_num_worlds = {  # S-alternatives to the designated world w as numbers
            alt_world
            for alt_world in all_bits
            for bit in all_bits
            if model.evaluate(verify(bit, model[S]))
            and model.evaluate(alternative(alt_world, bit, model[w]))
        }
        alt_worlds = {  # S-alternatives to the designated world w as states
            bitvec_to_substates(alt_num)
            for alt_num in alt_num_worlds
        }

        # Print propositions:
        if ver_states and fal_states:
            print(f"  |{S}| = < {ver_states}, {fal_states} >")
        elif ver_states and not fal_states:
            print(f"  |{S}| = < {ver_states}, ∅ >")
        elif not ver_states and fal_states:
            print(f"  |{S}| = < ∅, {fal_states} >")
        else:
            print(f"  |{S}| = < ∅, ∅ >")
        if alt_worlds:
            print(f"  {S}-alternatives to {bitvec_to_substates(model[w])} = {alt_worlds}")
            # TODO: not sure how to sort alt_worlds and alt_num_worlds so that they appear in order
            for alt_num in alt_num_worlds:
                true_in_alt = set()
                for sent in sentence_letters:
                    for bit in all_bits:
                        if model.evaluate(verify(bit, model[sent])) and string_part(bit, alt_num):
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

    
