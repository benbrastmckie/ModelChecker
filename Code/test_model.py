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


verify = Function("verify", BitVecSort(8), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(8), AtomSort, BoolSort())


solver = Solver()

solver.add(
    # FRAME CONSTRAINT
    ForAll([x,y], Implies(And(possible(x), is_part_of(x,y)), possible(y))),
    ForAll(w, Implies(is_world(w), possible(w))),
    ForAll([x,w], Implies(And(is_world(w), possible(x), possible(fusion(x,w))), is_part_of(x,w))),
    ForAll(w, Implies(And(possible(w),
                          ForAll(x, Implies(possible(fusion(x,w)),
                                            is_part_of(x,w)))),
                      is_world(w))),
    # # MODEL CONSTRAINT
    # ForAll([x,y], Implies(And(verify(x,A), verify(y,A)), verify(fusion(x,y),A))), # NOTE: seems to cause trouble
    # ForAll([x,y], Implies(And(falsify(x,A), falsify(y,A)), falsify(fusion(x,y),A))),
    # ForAll([x,y], Implies(And(verify(x,A), falsify(y,A)), Not(possible(fusion(x,y))))),
    # ForAll(x, Implies(possible(x),
    #                   Exists(y, And(possible(fusion(x,y)), Or(verify(y,A), falsify(y,A)))))),
)

print (solver.check())
model = solver.model()
print (model)
print ("interpretations assigned to AtomSort and A:")
print (model[AtomSort])
print (model[A])
