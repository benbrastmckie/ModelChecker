from z3 import *

# Define the predicates
possible = Function("possible", BitVecSort(8), BoolSort())
# NOTE: what is a BitVecSort and BoolSort, and also Function type? looks like they'll be very useful
# B: I think this defines functions from bitvectors to truth-values which is effectively a predicate


def fusion(bit_s, bit_t):
    fused = bit_s | bit_t  # | is the or operator
    return simplify(fused)  # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object. 

def is_part_of(bit_s, bit_t):
    return (
        # fusion(bit_s, bit_t) == bit_t
        fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
    )  # I think this is the right OR operation?
    # adding the sexpr()s above seemed to do the trick, not sure why.


# Create an instance of Z3 solver
solver = Solver()

# Define the constraints
x = BitVec("x", 8)
y = BitVec("y", 8)

solver.add(
    # Exists(x, possible(x)),
    Exists(y, Not(possible(y))),
    ForAll([x,y], Implies(And(is_part_of(x,y), possible(y)), possible(x))),
    Exists(x, And(
        possible(x),
        ForAll(y, Implies(possible(fusion(y,x)), is_part_of(y,x)))
    )),
    # Exists([x,y], And(possible(x), possible(y))),
    # Exists([x,y], And(is_part_of(x,y),possible(y))) 
    # NOTE: is_part_of seems not to work in this context
)

# Check if there exists a model
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for d in model.decls():
        print(f"{d.name()} = {model[d]}")
        # NOTE: I don't think this prints all of what the model includes
else:
    print("No model found")
