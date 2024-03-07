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
)

# dummy = BitVec('dummy',N)
solver = Solver()

solver.add(
    # M: a little testing area with some stuff
    # dummy == 9,
    # Not(possible(dummy)),
    # FRAME CONSTRAINT: every part of a possible state is possible
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # NOTE: the below draws an equivalence between the primitive 'world' and the defined term 'is_world'
    # TODO: it would be good to make do with just one of these, preferably the defined 'is_world'
    ForAll(w, Equivalent(is_world(w), world(w))),
    # NOTE: I defined equivalent in definitions.py; it is not a Z3 func. Though I can look for a Z3 one
    ForAll(
        [u, y],
        Equivalent(
            alternative(u, y, w),
            And(
                is_world(u),
                is_part_of(y, u),
                Exists(z, And(is_part_of(z, u), compatible_part(z, w, y))),
            ),
        ),
    ),
    # NOTE: this constraint seems to make the model not terminate :(
    # MODEL CONSTRAINT: every X of AtomSort is a proposition
    ForAll(X, proposition(X)),
    # EVAL CONSTRAINTS
    is_world(w),  # there is a world w
    is_part_of(s, w),  # s is a part of w
    verify(s, A),  # s verifies A
    falsify(c, A),  # s verifies A
    is_part_of(t, w),  # t is part of w
    verify(t, B),  # t verifies A
    falsify(z, B),  # t verifies A
    Not(  # in w, it is not the case that if A were true then B would be true
        ForAll(
            [a, v],
            Implies(
                And(verify(a, A), is_alternative(v, a, w)),
                Exists(b, And(is_part_of(b, v), verify(b, B))),
            ),
        ),
    ),
)

if solver.check() == sat:

    model = solver.model()

    # TODO: eventually replace with something more general
    sentence_letter_objects = [A, B]
    sentence_letter_names = {
        S.sexpr() for S in sentence_letter_objects
    }  # set because we're only testing for membership
    # M: got the for loop issue working. It was a type mismatch issue.
    # needed to make a list of sentence letter objects and names

    # QUESTION: the above seems motivated by the role sentence_letter_names
    # plays in all_states below. I wonder if there is a better way to define
    # all_states that does not need sentence_letter_names? perhaps we can
    # filter directly by asking if d in model.decls() is a bitvec?

    all_states = [
        d
        for d in model.decls()
        if d.arity() == 0 and d.name() not in sentence_letter_names
    ]
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    already_seen = set()

    print("States:")  # Print states
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

    print("Propositions:")  # Print states
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

        # TODO: not sure if the above has the right syntax but want to define the
        # alternatives to w that result from imposing a verifier for S on w


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
