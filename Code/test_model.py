# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
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
    bitvec_to_substates,
)


solver = Solver()

solver.add(
    # FRAME CONSTRAINT
    # 1. For every `x` and `y`, if `possible(y)` and `is_part_of(x,y)`, then `possible(x)`.
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # requires all X to be a proposition
    ForAll(
        X,
        And(  # TEST BOUND VAR
            ForAll(
                [x, y],
                Implies(And(verify(x, X), verify(y, X)), verify(fusion(x, y), X)),
            ),
            ForAll(
                [x, y],
                Implies(And(falsify(x, X), falsify(y, X)), falsify(fusion(x, y), X)),
            ),
            ForAll(
                [x, y],
                Implies(And(verify(x, X), falsify(y, X)), Not(possible(fusion(x, y)))),
            ),
            # ForAll(x, Implies(possible(x), Exists(y, And(compatible(x,y), Or(verify(y,X), falsify(y,X)))))),
            # NOTE: adding the constraint above makes Z3 crash
            # without this constraint the logic is not classical (there could be truth-value gaps)
        ),
    ),
    # EVAL CONSTRAINTS
    # Exists([w,s,t], And( # TEST BOUND VAR
    is_world(w),
    # is_world(v),
    # there is a world w
    is_part_of(s, w),
    verify(s, A),
    falsify(c, A),
    # A is true in w
    is_part_of(t, w),
    verify(t, B),
    falsify(r, B),
    # B is true in w
    Not(
        ForAll(
            [a, v],
            Implies(
                And(verify(a, A), alternative(v, a, w)),
                Exists(b, And(is_part_of(b, v), verify(b, B))),
            ),
        ),
    ),
    # in w, it is not the case that if A were true then B would be true
    # NOTE: there should be a world state v where A is true and B is false
    # so far it doesn't print the values of bound variables
    # )), # MATCH EXIST ABOVE
)


# TODO: fix printing so that numbers are readable
print(solver.check())
model = solver.model()
# print(model)
print("Model:")
states_dict = {}
funcs_dict = {}

for declaration in model.decls():

    try:  # do this to print bitvectors how we like to see them (as vectors)
        model[declaration].sexpr()
        states_dict[declaration.name()] = model[
            declaration
        ]  # model declaration is of type bitvec
        # print(f"{declaration.name()} = {bitvec_to_substates(model[declaration])}")
        # print(f"{declaration.name()} = {model[declaration]}")
        # print(f"{possible(model[declaration])}")
    except:  # this is for the "else" case (ie, "map everything to x value")
        funcs_dict[declaration.name()] = model[declaration].as_list()
        function = model[declaration].as_list
        # print(FuncInterp.as_list(function))
        # print(FuncInterp.else_value(function))
        # print(FuncInterp.num_entries(function))
        # print(f"this is the declaration name: {declaration.name()}")
        print(
            f"{declaration.name()} = {model[declaration].as_list()}"
        )  # now is a list with boolrefs inside

Possible = funcs_dict["possible"][0]

for state in states_dict:
    state_solver = Solver()
    state_solver.add(Possible)
    state_solver.add(state)
    print(solver.check())


# # TODO: fix printing so that numbers are readable
#
# if solver.check() == sat:
#     model = solver.model()
#
#     # TODO: replace ["A", "B"] with something more general
#     arity_0_decls = [d for d in model.decls() if d.arity() == 0 and d.name() not in ["A", "B"]]
#
#     # Print states
#     print("States:")
#     for decl in arity_0_decls:
#         # TODO: add world/possible/impossible after each state
#         print(f"{decl.name()} = {model[decl].sexpr()}")
# else:
#     print("No model found.")

# # Print propositions
# print("Propositions:")
# for atom in ["A", "B"]:
#     # TODO: store all verifies for atom
#     print(f"{atom.name()} = {model[atom]}")
#
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
