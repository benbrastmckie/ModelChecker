from z3 import (
    BoolSort,
    BitVecSort,
    Function,
    Solver,
    # BitVec,
    Not,
    Exists,
    And,
    Implies,
    ForAll,
    sat,
    DeclareSort,
    Consts,
    Bool,
    Or,
)

# I was thinking this would be a good place to try to get a toy solver going for
# the predicates 'verify' and 'falsify'

# NOTE: I think this makes X, Y have the sort Atoms... not sure this is useful
AtomSort = DeclareSort('AtomSort')
X, Y = Consts('X Y', AtomSort)

# NOTE: want 'verify' to be a function that takes a bitvector and sentence as
# input and a truth-value as output
verify = Function("verify", BitVecSort(8), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(8), AtomSort, BoolSort())

solver = Solver()
solver.add(

)

print (solver.check())
model = solver.model()
print (model)
print ("interpretation assigned to AtomSort:")
print (model[AtomSort])

# NOTE TO SELF (M): try just writing all the constraints (note to remember for later)

# def find_happy_dancing_model():
#     # Define a set of people
#     people = ["Alice", "Bob", "Charlie"]
#
#     # Define boolean variables for happiness and dancing for each person
#     happy = {person: Bool(f"{person}_happy") for person in people}
#     dancing = {person: Bool(f"{person}_dancing") for person in people}
#
#     # Create Z3 solver instance
#     solver = Solver()
#
#     # Add constraints
#     for person in people:
#         # If a person is happy, they must be dancing
#         solver.add(Implies(happy[person], dancing[person]))
#         # If a person is dancing, they may not be happy
#         solver.add(Not(Implies(dancing[person], Not(happy[person]))))
#
#     # Add constraint that at least one person is happy
#     solver.add(Or([happy[person] for person in people]))
#
#     # Check if there is a model
#     if solver.check() == sat:
#         model = solver.model()
#         # Print the model
#         print(
#             "Model where someone is happy, and everyone who is happy is dancing but not everyone who is dancing is happy:"
#         )
#         for person in people:
#             print(f"{person}: happy={model[happy[person]]}, dancing={model[dancing[person]]}")
#     else:
#         print("No model found.")
#
#
# # Find a model
# find_happy_dancing_model()
