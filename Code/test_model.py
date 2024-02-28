# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
    # sat,
    # simplify,
    Exists,
    ForAll,
    Implies,
    Or,
    BitVec,
    Not,
    DeclareSort,
    Consts,
    Solver,
    BoolSort,
    BitVecSort,
    Function,
    And,
)

from states import (
    N,
    fusion,
    is_new_world,
    is_part_of,
    possible,
    is_world,
)

AtomSort = DeclareSort("AtomSort")
A, B = Consts("A B", AtomSort)

# NOTE: N is defined in states.md
x = BitVec("x", N)
y = BitVec("y", N)
z = BitVec("z", N)
w = BitVec("w", N)


verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())


solver = Solver()

solver.add(
    # FRAME CONSTRAINT
    # Exists(w,is_new_world(x,w)),
    # verify(x,A),
    possible(z),
    Exists(x, verify(x,A)),
    # ForAll([x,y], Implies(And(possible(x), is_part_of(x,y)), possible(y))),
    # WORLD STATE EXISTS
    And(
        possible(w),
        ForAll(x, Implies(And(possible(x), possible(fusion(x,w))), is_part_of(x,w)))
    ),
    # GENERAL WORLD CONSTRAINTS
    # ForAll(w, Implies(is_world(w), possible(w))),
    # ForAll([x,w], Implies(And(is_world(w), possible(x), possible(fusion(x,w))), is_part_of(x,w))),
    # WORLDS ARE THE SAME AS MAX POSSIBLE STATES
    # ForAll(w, Implies(And(possible(w),
    #                       ForAll(x, Implies(possible(fusion(x,w)),
    #                                         is_part_of(x,w)))),
    #                   is_world(w))),
    # MODEL CONSTRAINT
    # ForAll([x,y], Implies(And(verify(x,A), verify(y,A)), verify(fusion(x,y),A))), # NOTE: seems to cause trouble
    # ForAll([x,y], Implies(And(falsify(x,A), falsify(y,A)), falsify(fusion(x,y),A))),
    # ForAll([x,y], Implies(And(verify(x,A), falsify(y,A)), Not(possible(fusion(x,y))))),
    # ForAll(x, Implies(possible(x),
    #                   Exists(y, And(possible(fusion(x,y)), Or(verify(y,A), falsify(y,A)))))),
    # EVAL CONSTRAINT
    Exists([w,z], And(is_new_world(x,w), is_part_of(z,w), verify(z,A)) )

)





print (solver.check())
model = solver.model()
print (model)
print ("interpretations assigned to AtomSort and A:")
print (model[AtomSort])
print (model[A])
for declaration in model.decls():
    try: # do this to print bitvectors how we like to see them (as vectors)
        print(f"{declaration.name()} = {model[declaration].sexpr()}")
        print(f'is {model[declaration]} possible?: {possible(model[declaration])}')
    except: # this is for the "else" case (ie, "map everything to x value")
        function = model[declaration]
        # print(FuncInterp.as_list(function))
        # print(FuncInterp.else_value(function))
        # print(FuncInterp.num_entries(function))
        print(f'this is the declaration name: {declaration.name()}')
        print(f"{declaration.name()} = {model[declaration]}")
        # rn this is printing a monster, not sure what to make of it
