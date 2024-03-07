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
    alternative,
    alt_world,
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
    # NOTE: the below draws an equivalence between the primitive 'world' and the defined term 'is_world'
    # TODO: it would be good to make do with just one of these, preferably the defined 'is_world'
    ForAll(w,Equivalent(is_world(w),world(w))),
    # NOTE: I defined equivalent in definitions.py; it is not a Z3 func. Though I can look for a Z3 one
    # ForAll([u,y,w],Equivalent(alternative(u,y,w), alt_world(u,y,w))),
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
                And(verify(a, A), alternative(v, a, w)),
                Exists(b, And(is_part_of(b, v), verify(b, B))),
            ),
        ),
    ),
)

if solver.check() == sat:

    model = solver.model()

    # TODO: eventually replace with something more general
    sentence_letter_objects = [A,B]
    sentence_letter_names = {S.sexpr() for S in sentence_letter_objects} # set because we're only testing for membership
    all_states = [d for d in model.decls() if d.arity() == 0 and d.name() not in sentence_letter_names]
    # M: got the for loop issue working. It was a type mismatch issue. Z3 types are a bit finicky lol. 
    # But to do so, needed to make a list of sentence letter objects and a list of the accompanying names
    # B: looks great!

    # TODO: how can we print all the states and not just the ones mentioned in the constraints?
    # if they weren't added to the solver, I don't think they'd be in the model
    print("States:")  # Print states
    for state in all_states:
        # NOTE: looks like we can't use is_world since it is not a declared primitive
        # see hack above, introducing 'world' which is made equivalent
        if model.evaluate(world(model[state])):
            # TODO: why does it say invalid conditional operand? # M: right now it works. What was making it say that? It looks fine now, since .evaluate() returns a Bool
            print(f"{state.name()} = {bitvec_to_substates(model[state])} (world)")
        elif model.evaluate(possible(model[state])):
            print(f"{state.name()} = {bitvec_to_substates(model[state])} (possible)")
        else:
            print(f"{state.name()} = {bitvec_to_substates(model[state])} (impossible)")

    # for loop over sentences
    for S in sentence_letter_objects:
        ver_states = {
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(verify(model[decl], model[S]))
        }
        fal_states = {
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(falsify(model[decl], model[S]))
        }

        # Print propositions:
        if ver_states:
            print(f"Verifiers({S}) = {ver_states}")
        else:
            print(f"Verifiers({S}) = ∅")
        if fal_states:
            print(f"Falsifiers({S}) = {fal_states}")
        else:
            print("∅")
    

    # hidden states attempt here
    states_as_nums = [model[state].as_long() for state in all_states]
    max_num = max(states_as_nums)
    for val in range(max_num + 1): # bc stop is exclusive
        test_state = BitVecVal(val,N)
        if model.evaluate(world(test_state)):
            print(f"{state.name()} = {bitvec_to_substates(test_state)} (world)")
        elif model.evaluate(possible(model[state])):
            print(f"{state.name()} = {bitvec_to_substates(test_state)} (possible)")
        else:
            print(f"{state.name()} = {bitvec_to_substates(test_state)} (impossible)")
