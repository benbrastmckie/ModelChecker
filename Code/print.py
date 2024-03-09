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
    parthood,
)

# TODO: it would be better to be able to call a print function from the files
# that include the solvers instead of importer their models here

# TODO: eventually replace sentence_letters with something more general

# from crimson_cmodel import model
# sentence_letters = [A, B]
# """
# A, B does not entail if A were the case then B would be the case.
#
# given that the ball is red and mary likes it does not follow that:
# if the ball were red then mary would like it
# """

# from simp_disj_ant import ( model )
# '''
# if A or B were the case then C would be the case entails both:
# if A were the case then C would be the case;
# if B were the case then C would be the case
#
# if jon or lynda were to join then the part would be great entails:
# if jon were to join then the part would be great;
# if lynda were to join then the part would be great
# '''

# from cf_excl_mid import ( model )
# '''
# if A were the case then B or C would be the case does not entail either:
# if A were the case then B would be the case;
# if A were the case then C would be the case.
# '''

def print_model(model, sentence_letters):

    all_states = [element for element in model.decls() if is_bitvector(element)]
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    already_seen = set()

    print("\nStates:")  # Print states
    for val in range(max_num * 2):
        # bc binary; the best-case last one (stopped at) is the first one repeated, so we're good
        # B: that makes good sense!
        test_state = BitVecVal(val, N)
        as_substates = bitvec_to_substates(test_state)
        # print(f"TEST STATE: {test_state}")
        if as_substates in already_seen:
            break
        elif model.evaluate(is_world(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"  {test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)

    # Print evaluation world:
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}:")
    true_in_eval = set()
    for T in sentence_letters:
        for state in all_states:
            if model.evaluate(verify(model[state], model[T])) and model.evaluate(parthood(model[state], model[w])):
                true_in_eval.add(T)
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

     # Print propositions
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
                for T in sentence_letters:
                    for state in all_states:
                        if model.evaluate(verify(model[state], model[T])) and model.evaluate(parthood(model[state], alt_num)):
                            true_in_alt.add(T)
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
            print(f"  There are no {S}-alternatives to {bitvec_to_substates(model[w])}\n")

    print()  # Print states
    # TODO: I couldn't figure out how to remove the quotes from the states
