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
)


solver = Solver()

solver.add(
    # FRAME CONSTRAINT
    # 1. For every `x` and `y`, if `possible(y)` and `is_part_of(x,y)`, then `possible(x)`.
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # MODEL CONSTRAINTS: requires X to be a proposition where X is a sentence letter
    # 1. For all `x`, `y`, if `verify(x,X)` and `verify(y,X)`, then `verify(fusion(x,y),X)`.
    # 2. For all `x` and `y`, if `falsify(x,X)` and `falsify(y,X)`, then `falsify(fusion(x,y,X))`.
    # 3. For all `x` and `y`, if `verify(x,X)` and `falsify(y,X)`, then `Not(possible(fusion(x,y)))`.
    # 4. For all `x`, if `possible(x)`, then there is some `y` where `possible(fusion(x,y))` and: `verify(y,X)` or `falsify(y,X)`.
    # TODO: is it possible to make X bound by a universal quantifier?
    # first try didn't work
    # requires A to be a proposition
    # ForAll(A, And( # TEST BOUND VAR
    # ForAll([x,y], Implies(And(verify(x,A),verify(y,A)), verify(fusion(x,y),A))),
    # ForAll([x,y], Implies(And(falsify(x,A),falsify(y,A)), falsify(fusion(x,y),A))),
    # ForAll([x,y], Implies(And(verify(x,A),falsify(y,A)), Not(possible(fusion(x,y))))),
    # ForAll(x, Implies(possible(x), Exists(y, And(compatible(x,y), Or(verify(y,A), falsify(y,A)))))),
    # )), ### MATCH FORALL ABOVE
    # requires B to be a proposition
    # ForAll(B, And( # TEST BOUND VAR
    # ForAll([x,y], Implies(And(verify(x,B),verify(y,B)), verify(fusion(x,y),B))),
    # ForAll([x,y], Implies(And(falsify(x,B),falsify(y,B)), falsify(fusion(x,y),B))),
    # ForAll([x,y], Implies(And(verify(x,B),falsify(y,B)), Not(possible(fusion(x,y))))),
    # ForAll(x, Implies(possible(x), Exists(y, And(compatible(x,y), Or(verify(y,B), falsify(y,B)))))),
    # )), ### MATCH FORALL ABOVE
    # TODO: replace constraints below with proposition(X) from definitions
    # requires X to be a proposition
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
    ),  ### MATCH FORALL ABOVE
    # EVAL CONSTRAINTS
    # Exists([w,s,t], And( # TEST BOUND VAR
    is_world(w),
    is_world(v),
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

if solver.check() == sat:
    model = solver.model()

    # TODO: replace ["A", "B"] with something more general
    arity_0_decls = [d for d in model.decls() if d.arity() == 0 and d.name() not in ["A", "B"]]

    # Print states
    print("States:")
    for decl in arity_0_decls:
        # TODO: add world/possible/impossible after each state
        print(f"{decl.name()} = {model[decl].sexpr()}")

    # Print propositions
    print("Propositions:")
    for atom in ["A", "B"]:
        # TODO: store all verifies for atom
        print(f"{atom.name()} = {model[atom]}")

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
else:
    print("No model found.")

# # Check satisfiability
# if solver.check() == sat:
#     model = solver.model()
#     # Iterate over all declarations in the model
#     for decl in model.decls():
#         if decl.arity() > 0:  # Filter out function declarations
#             print(f"{decl.name()} extension:")
#             # Iterate over all possible arguments
#             if decl.arity() == 1:
#                 for i in range(10):  # Adjust range as needed
#                     arg = IntVal(i)
#                     print(f"{arg}: {model.evaluate(decl(arg))}")
#             elif decl.arity() == 2:
#                 for i in range(10):  # Adjust range as needed
#                     for j in range(10):  # Adjust range as needed
#                         arg1, arg2 = IntVal(i), IntVal(j)
#                         print(f"{arg1}, {arg2}: {model.evaluate(decl(arg1, arg2))}")
# else:
#     print("No model found.")

# print(solver.check())
# if solver.check() == sat:
#     model = solver.model()
#     # Print the model extensions for the predicates
#     print("Model:")
#     for decl in model.decls():
#         # if decl.arity() == 0 and decl.kind() == Z3_OP_UNINTERPRETED:
#         print(f"{decl.name()} = {model[decl]}")
#         # print(f"{decl.name()} = {model[possible]}")

# for declaration in model.decls():
#     try:  # do this to print bitvectors how we like to see them (as vectors)
#         print(f"{declaration.name()} = {model[declaration].sexpr()}")
#         print(f"{model[declaration.possible]}")
#     except:  # this is for the "else" case (ie, "map everything to x value")
#         function = model[declaration]
#         # print(FuncInterp.as_list(function))
#         # print(FuncInterp.else_value(function))
#         # print(FuncInterp.num_entries(function))
#         # print(f"this is the declaration name: {declaration.name()}")
#         print(f"{declaration.name()} = {model[declaration]}")
