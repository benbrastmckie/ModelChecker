from z3 import (
    BitVecVal,
)

from definitions import (
    N,
    is_bitvector,
    w,
    A,
    B,
    C,
    world,
    possible,
    verify,
    falsify,
    alternative,
    bitvec_to_substates,
    string_part,
)

# NOTE: one idea is to extract a model from Z3, working entirely with bitvectors
# so that the output could be stored in this form by build_model. we could then
# define the print_model function which will convert these elements to fusions
# of appropriately named atomic states, printing the various elements. another
# idea is to convert directly to to fusions, and then define parthood, etc., all
# over again for these objects considered as strings. but I assume this will be
# slower and less useful of an output except for the purposes of printing. here
# is the former strategy described in greater detail.

# TODO: define model_builder given the model and sentence_letters as inputs
# 1. store all bitvectors in the model, e.g., #b010, in a sorted list
    # NOTE: could store them as fusions a.b.c, b.c, etc., but probably easier
    # to work with bitvectors in order to identify the worlds. below I used
    # string_part but seems not as good as working with bitvectors directly.
# 2. identify and store which bitvectors are possible in a sorted list
    # NOTE: the aim is to avoid declaring the Z3 constant 'world'
    # so worlds cannot be extracted from the model directly (as they are now)
    # something similar may be said for 'alternative' currently being used
# 3. for each sentence letter, store sorted lists of its verifiers/falsifiers
# 4. identify and store the world states in a sorted list
# 5. for each sentence letter, store a sorted list of alternatives to w

# TODO: define print function given the output of the model_builder function
# 1. print all states as fusions of atomic states
# 2. print evaluation world w and all sentence letters verified by a part of w
# 3. for each sentence letter, print its verifiers, falsifiers, and alternatives
    # where for each alternative u, print all sentences verified by a part of u

def print_states(model):
    '''print all fusions of atomic states in the model'''
    # TODO: I suspect there is something wrong with is_bitvector since it
    # seems to include outputs x, s, w, t, u, y, k!491 when N = 5
    # is this related to the cap on states below 26? would be good to use
    # subscripts if more states are needed
    all_states = [element for element in model.decls() if is_bitvector(element)]
    # print(f"{all_states}")
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    already_seen = set()

    print("\nStates:")  # Print states
    for val in range(max_num * 2):
        # bc binary; the best-case last one (stopped at) is the first one repeated, so we're good
        # B: that makes good sense!
        test_state = BitVecVal(val, N)
        as_substates = bitvec_to_substates(test_state)
        if as_substates in already_seen:
            break
        if model.evaluate(world(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"  {test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)


def print_evaluation(model, sentence_letters):
    '''print the evaluation world and all sentences true/false in that world'''
    all_states = [element for element in model.decls() if is_bitvector(element)]
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}:")
    true_in_eval = set()
    for sent in sentence_letters:
        for state in all_states:
            if model.evaluate(verify(model[state], model[sent])) and string_part(model[state],model[w]):
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
    '''
    print each propositions and the alternative worlds in which it is true
    '''
    all_states = [element for element in model.decls() if is_bitvector(element)]
    print("\nPropositions:")
    for S in sentence_letters:
        ver_states = {  # verifier states for S
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
        }
        fal_states = {  # falsifier states for S
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(falsify(model[state], model[S]))
        }
        alt_num_worlds = {  # S-alternatives to the designated world w as numbers
            model[alt_world]
            for alt_world in all_states
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(alternative(model[alt_world], model[state], model[w]))
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
                    for state in all_states:
                        if model.evaluate(verify(model[state], model[sent])) and string_part(model[state], alt_num):
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

    
