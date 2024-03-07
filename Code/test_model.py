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
    is_world,
    possible,
    verify,
    falsify,
    alternative,
    proposition,
    bitvec_to_substates,
    maximal,
)

dummy = BitVec('dummy',N)
solver = Solver()

solver.add(
    # M: a little testing area with some stuff
    # dummy == 9,
    Not(possible(dummy)),
    # ForAll([A,x], Implies(possible(x), Or(verify(x,A),falsify(x,A)))), #@B: adding this (which—I think—is a requirement that every possible state either verifies or falsifies every sentence) makes it unsat
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

def attempt_a(solver):
    if solver.check() == sat:
        model = solver.model()

        # TODO: replace ["A", "B"] with something more general
        states = [d for d in model.decls() if d.arity() == 0 and d.name() not in ["A", "B"]]

        # Print states
        print("States:")
        for decl in states:
            # TODO: how can we print all the states and whether world/poss/imposs
            print(f"{decl.name()} = {bitvec_to_substates(model[decl])}")

        possible = [d for d in model.decls() if d.arity() == 1]
        # TODO: unlock var bool string
        
        print("Possible States:")
        for func in possible:
            # TODO: store and print all verifiers/falsifiers for atom
            print(f"{func.name()} = {model[func].as_list()}")
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
attempt_b(solver)
#         a= [type(declaration) for declaration in model]
#         print(a)
#         states_dict = {model[declaration]: (model[declaration], bitvec_to_substates(model[declaration])) for declaration in model if declaration.arity() == 0}
#         funcs_dict = {declaration.name(): model[declaration].as_list() for declaration in model if declaration.arity() != 0}

#         print(states_dict)
#         print(funcs_dict)
#         return states_dict, funcs_dict, model


#     else:
#         print("No model found.")
#     # proposition = [d for d in model.decls() if d.arity() == 2]
#     # # TODO: unlock var bool string
#     #
#     # print("Propositions:")
#     # for prop in possible:
#     #     # TODO: store and print all verifiers/falsifiers for atom
#     #     print(f"{func.name()} = {model[func].as_list()}")
# states_dict, funcs_dict, model = attempt_b(solver)


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
