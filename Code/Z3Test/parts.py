# from typing import TYPE_CHECKING
# from z3 import *
#
# if TYPE_CHECKING:

from z3 import (
    BoolSort,
    BitVecSort,
    Function,
    simplify,
    Solver,
    BitVec,
    Not,
    Exists,
    And,
    Implies,
    ForAll,
    sat,
)

# Define the predicates
possible = Function("possible", BitVecSort(7), BoolSort())
# dummy_predicate = Function("dummy")


def fusion(bit_s, bit_t):
    return bit_s | bit_t  # | is the or operator
    # seems like the issue was that BitVecs work different from BitVecVals. I think we want to work with BitVecs? so rn it's good


def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t

# Create an instance of Z3 solver
solver = Solver()

# Define the constraints
x = BitVec("x", 7)
y = BitVec("y", 7)
z = BitVec("z", 7)
w = BitVec("w", 7)

solver.add( # NOTE: right now it is not finding a model but should be able to
    ForAll([x, y], Implies(
        And(is_part_of(x, y), possible(y)),
        possible(x))
    ),
    Exists([x,y],And(
        Not(possible(x)),
        is_part_of(x, y),
        # possible(y),
        # NOTE: once a model is found, uncomment the above to see if this makes it unsat
        # M: yeah it does
           # B: That's great!
           # B: This should allow to start setting up some of the other constraints
           # B: Once we can use these to find countermodels by hand we can think about
           # B: the functions that will generate these constraints (once it is working)
    ),)
    # M: I don't think we actually ever add any of our vars to the solver bc x and y above are bound by quantifiers. 
        # B: I tried commenting out the variables, but then it throws errors
        # B: Perhaps defining the variable is more like defining its sort/type?
        # B: I'll add this to `Questions`
    # BONEYARD:
    # Exists(x, possible(x)),
    # Exists(y, Not(possible(y))),
    # Exists([x,y],And(
    #     possible(x),
    #     possible(y),
    #     Not(possible(fusion(x,y)))
    # )),
    # Exists(x,And(
    #     possible(x),
    #     ForAll(y, Implies(
    #         possible(fusion(y,x)),
    #         is_part_of(y,x)))
    # )),
    # Exists([x,y], And(possible(x), possible(y))),
    # Exists([x,y], And(is_part_of(x,y),possible(y)))
    # NOTE: is_part_of seems not to work in this context
)

# Check if there exists a model
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for declaration in model.decls():
        try: # do this to print bitvectors how we like to see them (as vectors)
            print(f"{declaration.name()} = {model[declaration].sexpr()}")
        except: # this is for the "else" case (ie, "map everything to x value")
            print(f"{declaration.name()} = {model[declaration]}")
        # NOTE: I don't think this prints all of what the model includes
        # M: I think it works. rn it prints "possible = [else -> False]", which means map everything (ie, x and y) to false
else:
    print("No model found")
