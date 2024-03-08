# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
    Var,
    sat,
    simplify,
    help_simplify,
    Exists,
    ForAll,
    Implies,
    Solver,
    And,
    Not,
    Or,
    BitVec,
    BitVecVal,
    # DeclareSort,
    # Consts,
    # BoolSort,
    BitVecSort,
    # Function,
)

from definitions import (
    N,
    a,
    b,
    c,
    r,
    s,
    t,
    u,
    v,
    w,
    x,
    y,
    z,
    A,
    B,
    X,
    # Y,
    fusion,
    is_part_of,
    compatible,
    world,
    is_world,
    possible,
    verify,
    falsify,
    is_alternative,
    compatible_part,
    alternative,
    proposition,
    bitvec_to_substates,
    maximal,
    Equivalent,
    is_bitvector,
    parthood
)

solver = Solver()

solver.add(
    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion
    ForAll([x, y], Equivalent(parthood(x, y),is_part_of(x,y))),
    # states are closed under fusion
    ForAll(w, Equivalent(
        world(w),
        # is_world(w),  # NOTE: ditto to NOTE for is_alternative below
        And(possible(w), maximal(w))
    )),
    ForAll(
        [u, y],
        Equivalent(  # TODO: replace with Z3 equiv if any?
            alternative(u, y, w),
            # is_alternative(u, y, w),
            # NOTE: making constraints on alternative() explicit here could
            # make things easier to tweak and keep track of rather than having
            # two similar sounding terms, one defined and one primitive
            And(
                world(u),
                is_part_of(y, u),
                Exists(z, And(is_part_of(z, u), compatible_part(z, w, y))),
            ),
        ),
    ),

    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),  # every X of AtomSort is a proposition

    # EVAL CONSTRAINTS
    world(w),  # there is a world w
    is_part_of(s, w),  # s is a part of w
    verify(s, A),  # s verifies A
    is_part_of(t, w),  # t is part of w
    verify(t, B),  # t verifies B

    # CF constraints: it is not true that, if A were the case, B would be the case
    verify(y, A),
    is_alternative(u, y, w),
    Exists(b, And(is_part_of(b, u), falsify(b, B))),

    # NOTE: although the above is equivalent to the below modulo exhaustivity
    # the latter produces truth-value gaps (see issue on github)

    # ForAll(b, Implies(is_part_of(b, u), Not(verify(b, B)))),

        # NOTE: replacing the CF constraints above with the below produces
        # models with no A-alternatives to w despite what the constraint would
        # seem to require. However, adding the constraint 'falsify(z, B)'
        # populates A-alternatives. I'm not sure why this is.
    # Not(  # in w, it is not the case that if A were true then B would be true
    #     ForAll(
    #         [a, v],
    #         Implies(
    #             And(verify(a, A), is_alternative(v, a, w)),
    #             Exists(b, And(is_part_of(b, v), verify(b, B))),
    #         ),
    #     ),
    # ),

)

if solver.check() == sat:

    model = solver.model()

    # TODO: eventually replace with something more general
    sentence_letters = [A, B]
    all_states = [element for element in model.decls() if is_bitvector(element)]
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    already_seen = set()


    print("\nStates:\n")  # Print states
    for val in range(max_num * 2):
        # bc binary; the best-case last one (stopped at) is the first one repeated, so we're good
        # B: that makes good sense!
        test_state = BitVecVal(val, N)
        as_substates = bitvec_to_substates(test_state)
        # print(f"TEST STATE: {test_state}")
        if as_substates in already_seen:
            break
        elif model.evaluate(world(test_state)):
            print(f"{test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"{test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"{test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)

    print("\nPropositions:")  # Print states
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
        alt_world = {  # S-alternatives to the designated world w
            bitvec_to_substates(model[alt])
            for alt in all_states
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(alternative(model[alt], model[state], model[w]))
        }
        true_states = {  # verifier states for S that are part of w
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(parthood(model[state], model[w]))
        }

        # Print propositions:
        if ver_states and fal_states:
            print(f"\n|{S}| = < {ver_states}, {fal_states} >")
        elif ver_states and not fal_states:
            print(f"\n|{S}| = < {ver_states}, ∅ >")
        elif not ver_states and fal_states:
            print(f"\n|{S}| = < ∅, {fal_states} >")
        else:
            print(f"\n|{S}| = < ∅, ∅ >")
        if true_states:
            print(f"{S} is true in {bitvec_to_substates(model[w])}")
        else:
            print(f"{S} is false in {bitvec_to_substates(model[w])}")
        if alt_world:
            print(f"{S}-alternatives to {bitvec_to_substates(model[w])} = {alt_world}")

            # TODO: need something like the below to print all sentences
            # that are true in the alternative world. trouble seems to be the
            # elements in alt_world are fusions rather than bitvectors. also
            # not sure how to check to see if ANY part of the alternative world
            # verifies a given sentence.

            # for alt in alt_world:
            #     true_in_alt = {
            #         T for T in sentence_letters
            #         # NOTE: need to check if there is some state in all_states
            #         # that verifies T and is a part of the alt world
            #         if model.evaluate(verify(model[state], model[T]))
            #         and model.evaluate(parthood(model[state], model[alt]))
            #     }
            #     if true_in_alt:
            #         print(f"{true_in_alt} are true in {alt}")

        else:
            print(f"{S}-alternatives to {bitvec_to_substates(model[w])} = ∅")

    print()  # Print states
        # TODO: I couldn't figure out how to remove the quotes from the states
