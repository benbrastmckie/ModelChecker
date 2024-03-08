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

from crimson_cmodel import model

sentence_letters = [A, B]
"""
A, B does not entail if A were the case then B would be the case.

given that the ball is red and mary likes it does not follow that:
if the ball were red then mary would like it
"""

# from simp_disj_ant import ( model )
# sentence_letters = [A, B, C]
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
# sentence_letters = [A, B, C]
# '''
# if A were the case then B or C would be the case does not entail either:
# if A were the case then B would be the case;
# if A were the case then C would be the case.
# '''

if model != "nil":

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
        elif model.evaluate(world(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"  {test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"  {test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)

    # Print evaluation world:
    print(f"\nThe evaluation world is {bitvec_to_substates(model[w])}.")

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
        alt_bitvectors = {  # S-alternatives to the designated world w
            alt
            for alt in all_states
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(alternative(model[alt], model[state], model[w]))
        }
        alt_worlds = {  # S-alternatives to the designated world w
            bitvec_to_substates(model[alt])
            for alt in alt_bitvectors
        }
        # alt_worlds = {  # S-alternatives to the designated world w
        #     bitvec_to_substates(model[alt])
        #     for alt in all_states
        #     for state in all_states
        #     if model.evaluate(verify(model[state], model[S]))
        #     and model.evaluate(alternative(model[alt], model[state], model[w]))
        # }
        true_states = {  # verifier states for S that are part of w
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(parthood(model[state], model[w]))
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
        if true_states:
            print(f"  {S} is true in {bitvec_to_substates(model[w])}")
        else:
            print(f"  {S} is false in {bitvec_to_substates(model[w])}")
        if alt_worlds:
            print(
                f"  {S}-alternatives to {bitvec_to_substates(model[w])} = {alt_worlds}"
            )

            # TODO: need something like the below to print all sentences
            # that are true in the alternative world. trouble seems to be the
            # elements in alt_world are fusions rather than bitvectors. also
            # not sure how to check to see if ANY part of the alternative world
            # verifies a given sentence.

            # for alt in alt_bitvectors:
            #     true_in_alt = set()
            #     for T in sentence_letters:
            #         if any(
            #             model.evaluate(verify(model[state], model[T]))
            #             and model.evaluate(parthood(model[state], model[alt]))
            #             for state in all_states
            #         ):
            #             true_in_alt.add(T)
            #     if true_in_alt:
            #         print(f"  {true_in_alt} are true in {bitvec_to_substates(model[alt])}")
            # print()

            # NOTE: attempt #2
            # for alt in alt_worlds:
            #     true_in_alt = set()
            #     for T in sentence_letters:
            #         if any(
            #             model.evaluate(verify(model[state], model[T]))
            #             and model.evaluate(parthood(model[state], model[alt_bit]))
            #             and alt == bitvec_to_substates(model[alt_bit])
            #             for state in all_states
            #             for alt_bit in alt_bitvectors
            #         ):
            #             true_in_alt.add(T)
            #     if true_in_alt:
            #         print(f"  {true_in_alt} are true in {bitvec_to_substates(model[alt])}")
            # print()

        else:
            print(f"  {S}-alternatives to {bitvec_to_substates(model[w])} = ∅\n")

    print()  # Print states
    # TODO: I couldn't figure out how to remove the quotes from the states
else:
    print("\nThere are no models.\n")
