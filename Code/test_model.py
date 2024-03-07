# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
    Var,
    sat,
    # simplify,
    Exists,
    ForAll,
    Implies,
    Solver,
    And,
    Not,
    Or,
    BitVec,
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
    ForAll(
        w,
        Equivalent(is_world(w),world(w)) # NOTE: I defined equivalent in definitions.py; it is not a Z3 func. Though I can look for a Z3 one
        # And(
        #     # TODO: is there an Equiv function? I couldn't find one
        #     # M: I don't know of one either but this should do the job
        #     # I mean we could define one...
              # just defined one at the bottom of definiitons and replaced it here. Maybe more transparent? we can use it for all biconditionals
              # I'll look for a "real" one (ie in Z3) also
        #     Implies(is_world(w), world(w)),
        #     Implies(world(w), is_world(w)),
        # ),
    ),
    # TODO: ditto above. perhaps this can be improved. remains to print all alt_worlds that result from imposing a verifier for A on w
    ForAll(
        [u,y,w],
        And(
            # TODO: is there an Equiv function? I couldn't find one
            Implies(alternative(u,y,w), alt_world(u,y,w)),
            Implies(alt_world(u,y,w), alternative(u,y,w)),
        ),
    ), # this constraint seems to make the model not terminate :(
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
    # M: got the for loop issue working. It was a type mismatch issue. Z3 types are a bit finicky lol. But to do so, needed to make a list of sentence letter objects and a list of the accompanying names

    # TODO: how can we print all the states and not just the ones mentioned in the constraints?
    # if they weren't added to the solver, I don't think they'd be in the model
    print("States:")  # Print states
    for state in all_states:
        # NOTE: looks like we can't use is_world since it is not a declared primitive
        # see hack above, introducing 'world' which is made equivalent
        if model.evaluate(world(model[state])):  # TODO: why does it say invalid conditional operand? # M: right now it works. What was making it say that? It looks fine now, since .evaluate() returns a Bool
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
        # TODO: use symbol for empty set if either of the below are empty
        if ver_states:
            print(f"Verifiers({S}) = {ver_states}")
        else:
            print("∅")
        if fal_states:
            print(f"Falsifiers({S}) = {fal_states}")
        else:
            print("∅")

    # # TODO: delete once for loop over sentence letters works
    # ver_states = {
    #     bitvec_to_substates(model[decl])
    #     for decl in all_states
    #     if model.evaluate(verify(model[decl], model[B]))
    # }
    # fal_states = {  # TODO: use symbol for empty set if empty
    #     bitvec_to_substates(model[decl])
    #     for decl in all_states
    #     if model.evaluate(falsify(model[decl], model[B]))
    # }
    # print(f"Verifiers({B}) = {ver_states}")
    # print(f"Falsifiers({B}) = {fal_states}")

### END BEN'S ATTEMPT


# dummy = BitVec('dummy',N)
# solver = Solver()
#
# def attempt_a(solver):
#     if solver.check() == sat:
#         model = solver.model()
#
#         # TODO: replace ["A", "B"] with something more general
#         states = [d for d in model.decls() if d.arity() == 0 and d.name() not in ["A", "B"]]
#
#         # Print states
#         print("States:")
#         for decl in states:
#             # TODO: how can we print all the states and whether world/poss/imposs
#             print(f"{decl.name()} = {bitvec_to_substates(model[decl])}")
#
#         possible = [d for d in model.decls() if d.arity() == 1]
#         # TODO: unlock var bool string
#         
#         print("Possible States:")
#         for func in possible:
#             # TODO: store and print all verifiers/falsifiers for atom
#             print(f"{func.name()} = {model[func].as_list()}")
#     else:
#         print("No model found.")
#
# def attempt_b(solver):
#     if solver.check() == sat:
#         model = solver.model() # is of sort ModelRef
#         states_dict = {declaration: model[declaration] for declaration in model if declaration.arity() == 0 and declaration.name() not in ['A','B']}
#         print(states_dict)
#         for state in states_dict:
#             # the .evaluate() method adds something to the model and evaluates it. We don't even need to look at the extensions! 
#             print(f'{bitvec_to_substates(model[state])} is possible: {model.evaluate(possible(states_dict[state]))}')
#             print(f'{bitvec_to_substates(model[state])} verifies A: {model.evaluate(verify(states_dict[state],A))}')
#             print(f'{bitvec_to_substates(model[state])} falsifies A: {model.evaluate(falsify(states_dict[state],A))}') 
#             print('\n')           
#             # print(f'{state} is a world: {simplify(is_world(states_dict[state]))}')
#         # print(model[possible].as_list())
#         # print(model.evaluate(possible(dummy)))
#         # print(model.num_sorts())
#         # print(model.sexpr())
#         # print(model.decls)
#         # print(s)
#         # print(model[s])
#         # print(s.sort())
#         # print(model[s].sort())
#         # print(s == model[s])
#
#
#         # for declaration in model: # declarations are of type FuncDeclRef
#         #     if declaration.arity()==0:
#         #         pass
# attempt_b(solver)

#         a= [type(declaration) for declaration in model]
#         print(a)
#         states_dict = {model[declaration]: (model[declaration], bitvec_to_substates(model[declaration])) for declaration in model if declaration.arity() == 0}
#         funcs_dict = {declaration.name(): model[declaration].as_list() for declaration in model if declaration.arity() != 0}

# TODO: check scrap code and delete if not needed
# can always look back through old commits if something is needed

# for decl in model.decls():
#     if decl.arity() == 0:  # Filter out function declarations
#         print(f"{decl.name()} = {model[decl]}")
#     elif decl.arity() == 1:
#         for i in range(10):  # Adjust range as needed
#         arg = IntVal(i)
#         print(f"{arg}: {model.evaluate(decl(arg))}")
# elif decl.arity() == 2:
#     for i in range(10):  # Adjust range as needed
#         for j in range(10):  # Adjust range as needed
#             arg1, arg2 = IntVal(i), IntVal(j)
#             print(f"{arg1}, {arg2}: {model.evaluate(decl(arg1, arg2))}")

# # TODO: fix printing
# print(solver.check())
# model = solver.model()
# # print(model)
# print("Model:")
# states_dict = {}
# funcs_dict = {}
#
# for declaration in model.decls():
#
#     try:  # do this to print bitvectors how we like to see them (as vectors)
#         model[declaration].sexpr()
#         states_dict[declaration.name()] = model[
#             declaration
#         ]  # model declaration is of type bitvec
#         # print(f"{declaration.name()} = {bitvec_to_substates(model[declaration])}")
#         # print(f"{declaration.name()} = {model[declaration]}")
#         # print(f"{possible(model[declaration])}")
#     except:  # this is for the "else" case (ie, "map everything to x value")
#         funcs_dict[declaration.name()] = model[declaration].as_list()
#         function = model[declaration].as_list
#         # print(FuncInterp.as_list(function))
#         # print(FuncInterp.else_value(function))
#         # print(FuncInterp.num_entries(function))
#         # print(f"this is the declaration name: {declaration.name()}")
#         print(
#             f"{declaration.name()} = {model[declaration].as_list()}"
#         )  # now is a list with boolrefs inside
#
# Possible = funcs_dict["possible"][0]
#
# for state in states_dict:
#     state_solver = Solver()
#     state_solver.add(Possible)
#     state_solver.add(state)
#     print(solver.check())
#
