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
    is_bitvector,
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
    C,
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
)

solver = Solver()

solver.add(
    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion
    ForAll(
        w,
        Equivalent(
            world(w),
            And(possible(w), maximal(w)),
        ),
    ),
    # constraints on world predicate
    ForAll(
        [u, y],
        Equivalent(  # TODO: replace with Z3 equiv if any?
            alternative(u, y, w),
            And(
                world(u),
                is_part_of(y, u),
                Exists(z, And(is_part_of(z, u), compatible_part(z, w, y))),
            ),
        ),
    ),
    # constraints on alternative predicate
    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),
    # every X of AtomSort is a proposition
    world(w),
    # there is a world w
    ForAll(
        [s, v],
        Implies(
            And(verify(s, A), is_alternative(v, s, w)),
            Exists(t, And(
                is_part_of(t, v),
                Or(
                    verify(s, B),
                    verify(s, C),
                    Exists(
                        [a, b],
                        And(
                            s == fusion(a, b),
                            verify(a, B),
                            verify(b, C),
                        ),
                    ),
                ),
            )),
        ),
    ),
    # A \boxright B \vee C
    verify(a, A),
    is_alternative(u, a, w),
    Exists(x, And(is_part_of(x, u), falsify(x, B))),
    # \neg(A \boxright B)
    verify(b, A),
    is_alternative(v, b, w),
    Exists(y, And(is_part_of(y, v), falsify(y, C))),
    # \neg(A \boxright C)
)

if solver.check() == sat:

    model = solver.model()

    # TODO: eventually replace with something more general
    sentence_letter_objects = [A, B, C]
    all_states = [element for element in model.decls() if is_bitvector(element)]
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    already_seen = set()

    print("States:")  # Print states
    for val in range(max_num * 2):
        test_state = BitVecVal(val, N)
        as_substates = bitvec_to_substates(test_state)
        if as_substates in already_seen:
            break
        elif model.evaluate(world(test_state)):
            print(f"{test_state.sexpr()} = {as_substates} (world)")
        elif model.evaluate(possible(test_state)):
            print(f"{test_state.sexpr()} = {as_substates} (possible)")
        else:
            print(f"{test_state.sexpr()} = {as_substates} (impossible)")
        already_seen.add(as_substates)

    print("Propositions:")  # Print propositions and alternatives
    for S in sentence_letter_objects:
        ver_states = {
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
        }
        fal_states = {
            bitvec_to_substates(model[state])
            for state in all_states
            if model.evaluate(falsify(model[state], model[S]))
        }
        alt_states = {  # S-alternatives to designated world w
            bitvec_to_substates(model[alt])
            for alt in all_states
            for state in all_states
            if model.evaluate(verify(model[state], model[S]))
            and model.evaluate(alternative(model[alt], model[state], w))
        }
        # true_states = {
        #     bitvec_to_substates(model[state])
        #     for state in ver_states
        #     if model.evaluate(parthood(model[state], model[w]))
        # }

        # TODO: the aim above is to define a set of verifiers for S that are part
        # of the designated world w so as to say whether S is true at w
        # there may be a better way to do this

        # Print propositions:
        if ver_states and fal_states:
            print(f"|{S}| = < {ver_states}, {fal_states} >")
        elif ver_states and not fal_states:
            print(f"|{S}| = < {ver_states}, ∅ >")
        elif not ver_states and fal_states:
            print(f"|{S}| = < ∅, {fal_states} >")
        else:
            print(f"|{S}| = < ∅, ∅ >")
        if alt_states:
            print(f"{S}-alternatives to {bitvec_to_substates(model[w])} = {alt_states}")
        else:
            print(f"{S}-alternatives to {bitvec_to_substates(model[w])} = ∅")

        # TODO: I couldn't figure out how to remove the quotes from the states
else:
    print("There are no models")
