# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
    # sat,
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
    # c,
    # r,
    # s,
    # t,
    # z,
    # u,
    a,
    b,
    x,
    y,
    v,
    w,
    A,
    B,
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
    ForAll([x,y], Implies(And(possible(y),is_part_of(x,y)), possible(x))),

    # MODEL CONSTRAINTS: requires X to be a proposition where X is a sentence letter
    # 1. For all `x`, `y`, if `verify(x,X)` and `verify(y,X)`, then `verify(fusion(x,y),X)`.
    # 2. For all `x` and `y`, if `falsify(x,X)` and `falsify(y,X)`, then `falsify(fusion(x,y,X))`.
    # 3. For all `x` and `y`, if `verify(x,X)` and `falsify(y,X)`, then `Not(possible(fusion(x,y)))`.
    # 4. For all `x`, if `possible(x)`, then there is some `y` where `possible(fusion(x,y))` and: `verify(y,X)` or `falsify(y,X)`.
        # TODO: is it possible to make X bound by a universal quantifier?
        # first try didn't work

    # requires A to be a proposition
    ForAll([x,y], Implies(And(verify(x,A),verify(y,A)), verify(fusion(x,y),A))),
    ForAll([x,y], Implies(And(falsify(x,A),falsify(y,A)), falsify(fusion(x,y),A))),
    ForAll([x,y], Implies(And(verify(x,A),falsify(y,A)), Not(possible(fusion(x,y))))),
    ForAll(x, Implies(possible(x), Exists(y, And(compatible(x,y), Or(verify(y,A), falsify(y,A)))))),

    # requires B to be a proposition
    # ForAll([x,y], Implies(And(verify(x,B),verify(y,B)), verify(fusion(x,y),B))),
    # ForAll([x,y], Implies(And(falsify(x,B),falsify(y,B)), falsify(fusion(x,y),B))),
    # ForAll([x,y], Implies(And(verify(x,B),falsify(y,B)), Not(possible(fusion(x,y))))),
    # ForAll(x, Implies(possible(x), Exists(y, And(compatible(x,y), Or(verify(y,B), falsify(y,B)))))),
        # TODO: investigate why adding these constraints for B makes the program fail to halt

    # EVAL CONSTRAINTS
    is_world(w), # there is a world
    # And( # A is true in w
        is_part_of(x,w),
        verify(x,A),
    # ),
    # And( # B is true in w
        is_part_of(y,w),
        verify(y,B),
    # ),
    Not(ForAll([a,v], Implies( # in w it is not the case that if A were true then B would be true
        And(verify(a,A), alternative(w,a,v)),
        Exists(b, And(is_part_of(b,v), verify(b,B)))
    )))
)


# TODO: fix printing so that numbers are readable
print(solver.check())
model = solver.model()
# print(model)
print("Model:")
for declaration in model.decls():
    try:  # do this to print bitvectors how we like to see them (as vectors)
        print(f"{declaration.name()} = {model[declaration].sexpr()}")
        print(f"{possible(model[declaration])}")
    except:  # this is for the "else" case (ie, "map everything to x value")
        function = model[declaration]
        # print(FuncInterp.as_list(function))
        # print(FuncInterp.else_value(function))
        # print(FuncInterp.num_entries(function))
        # print(f"this is the declaration name: {declaration.name()}")
        print(f"{declaration.name()} = {model[declaration]}")
        # rn this is printing a monster, not sure what to make of it
