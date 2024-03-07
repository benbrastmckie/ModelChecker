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
    proposition,
    bitvec_to_substates,
    maximal,
)

# dummy = BitVec('dummy',N)
solver = Solver()

solver.add(
    # M: a little testing area with some stuff
    # dummy == 9,
    # Not(possible(dummy)),
    # ForAll([A,x], Implies(possible(x), Or(verify(x,A),falsify(x,A)))), #@B: adding this (which—I think—is a requirement that every possible state either verifies or falsifies every sentence) makes it unsat
    # FRAME CONSTRAINT: every part of a possible state is possible
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # NOTE: the below draws an equivalence between the primitive 'world' and the defined term 'is_world'
    # TODO: it would be good to make do with just one of these, preferably the defined 'is_world'
    ForAll(
        w,
        And(
            # TODO: is there an Equiv function? I couldn't find one
            Implies(is_world(w), world(w)),
            Implies(world(w), is_world(w)),
        ),
    ),
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

def attempt_a(solver):
    if solver.check() == sat:

        model = solver.model()

        # TODO: eventually replace with something more general
        sentence_letters = ["A","B",]

        all_states = [d for d in model.decls() if d.arity() == 0 and d.name() not in sentence_letters]

        # TODO: how can we print all the states and not just the ones mentioned in the constraints?
        print("States:")  # Print states
        for state in all_states:
            # NOTE: looks like we can't use is_world since it is not a declared primitive
            # see hack above, introducing 'world' which is made equivalent
            if model.evaluate(world(model[state])):  # TODO: why does it say invalid conditional operand?
                print(f"{state.name()} = {bitvec_to_substates(model[state])} (world)")
            elif model.evaluate(possible(model[state])):
                print(f"{state.name()} = {bitvec_to_substates(model[state])} (possible)")
            else:
                print(f"{state.name()} = {bitvec_to_substates(model[state])} (impossible)")

        # TODO: can't get for loop over sentence_letters to work
        # NOTE: I tried replacing 'A' with 'atom', un-commenting the line below, but no dice
        # for atom in sentence_letters:
        ver_states = {
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(verify(model[decl], model[A]))
        }
        fal_states = {
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(falsify(model[decl], model[A]))
        }

        # Print propositions:
        # TODO: use symbol for empty set if either of the below are empty
        print(f"Verifiers({A}) = {ver_states}")
        print(f"Falsifiers({A}) = {fal_states}")

        # TODO: delete once for loop over sentence letters works
        ver_states = {
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(verify(model[decl], model[B]))
        }
        fal_states = {  # TODO: use symbol for empty set if empty
            bitvec_to_substates(model[decl])
            for decl in all_states
            if model.evaluate(falsify(model[decl], model[B]))
        }
        print(f"Verifiers({B}) = {ver_states}")
        print(f"Falsifiers({B}) = {fal_states}")
    else:
        print("No model found.")

def attempt_b(solver):
    if solver.check() == sat:
        model = solver.model() # is of sort ModelRef
        states_dict = {declaration: model[declaration] for declaration in model if declaration.arity() == 0 and declaration.name() not in ['A','B']}
        print(states_dict)
        for state in states_dict:
            # the .evaluate() method adds something to the model and evaluates it. We don't even need to look at the extensions! 
            print(f'{bitvec_to_substates(model[state])} is possible: {model.evaluate(possible(states_dict[state]))}')
            print(f'{bitvec_to_substates(model[state])} verifies A: {model.evaluate(verify(states_dict[state],A))}')
            print(f'{bitvec_to_substates(model[state])} falsifies A: {model.evaluate(falsify(states_dict[state],A))}') 
            print('\n')           
            # print(f'{state} is a world: {simplify(is_world(states_dict[state]))}')
        # print(model[possible].as_list())
        # print(model.evaluate(possible(dummy)))
        # print(model.num_sorts())
        # print(model.sexpr())
        # print(model.decls)
        # print(s)
        # print(model[s])
        # print(s.sort())
        # print(model[s].sort())
        # print(s == model[s])


        # for declaration in model: # declarations are of type FuncDeclRef
        #     if declaration.arity()==0:
        #         pass
    else:
        print("No model found.")

attempt_a(solver)
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
