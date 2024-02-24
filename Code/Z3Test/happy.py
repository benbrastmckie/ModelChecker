from z3 import *

# Define the variables
happy = Function("happy", BitVecSort(8), BoolSort())
dancing = Function("dancing", BitVecSort(8), BoolSort())
# NOTE: what is a BitVecSort and BoolSort, and also Function type? looks like they'll be very useful

# Create an instance of Z3 solver
solver = Solver()

# Define the constraint: everyone who is happy is dancing
x = BitVec("x", 8)
solver.add(ForAll(x, Implies(happy(x), dancing(x))))

# Add the constraint: someone is happy
y = BitVec("y", 8)
solver.add(Exists(y, happy(y)))

# Check if there exists a model
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for d in model.decls():
        print(f"{d.name()} = {model[d]}")
else:
    print("No model found")
