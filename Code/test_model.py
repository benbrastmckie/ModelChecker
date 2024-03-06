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
    # BitVec,
    # DeclareSort,
    # Consts,
    # BoolSort,
    # BitVecSort,
    # Function,
)

from definitions import (
    # N,
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
    is_world,
    possible,
    verify,
    falsify,
    alternative,
    proposition,
    bitvec_to_substates,
)


solver = Solver()

solver.add(
    # FRAME CONSTRAINT: every part of a possible state is possible
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # MODEL CONSTRAINT: every X of AtomSort is a proposition
    ForAll(X, proposition(X)),
    # EVAL CONSTRAINTS
    is_world(w),  # there is a world w
    is_part_of(s, w),  # s is a part of w
    verify(s, A),  # s verifies A
    is_part_of(t, w),  # t is part of w
    verify(t, B),  # t verifies A
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

    # TODO: replace ["A", "B"] with something more general
    states = [d for d in model.decls() if d.arity() == 0 and d.name() not in ["A", "B"]]

    # Print states
    print("States:")
    for decl in states:
        # TODO: how can we print all the states and whether world/poss/imposs
        print(f"{decl.name()} = {bitvec_to_substates(model[decl])}")

    # possible = [d for d in model.decls() if d.arity() == 1]
    # # TODO: unlock var bool string

    # print("Possible States:")
    # for func in possible:
    #     # TODO: store and print all verifiers/falsifiers for atom
    #     print(f"{func.name()} = {model[func].as_list()}")

    # proposition = [d for d in model.decls() if d.arity() == 2]
    # # TODO: unlock var bool string
    #
    # print("Propositions:")
    # for prop in possible:
    #     # TODO: store and print all verifiers/falsifiers for atom
    #     print(f"{func.name()} = {model[func].as_list()}")

else:
    print("No model found.")

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
