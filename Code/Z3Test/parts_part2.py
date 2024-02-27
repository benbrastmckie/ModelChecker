from z3 import * 
(
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
    FuncInterp
)

# Define the predicates
possible = Function("possible", BitVecSort(7), BoolSort())

def fusion(bit_s, bit_t):
    return bit_s | bit_t  # | is the or operator

def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t

# Create an instance of Z3 solver
solver = Solver()

# Define the constraints
x = BitVec("x", 7)
y = BitVec("y", 7)
z = BitVec("z", 7)
w = BitVec("w", 7)

solver.add(
    ForAll([x, y], Implies(
        And(is_part_of(x, y), possible(y)),
        possible(x))
    ),
    Not(possible(y)),
    is_part_of(x, y),
    possible(z),
    is_part_of(w,z),
    z == 5, # change this to 0 and no model is found. This is good and checks out with intuitive result
    w != 0,
    x != y,
)

# Check if there exists a model
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for declaration in model.decls():
        try: # do this to print bitvectors how we like to see them (as vectors)
            print(f"{declaration.name()} = {model[declaration].sexpr()}")
            print(f'is {model[declaration]} possible?: {possible(model[declaration])}')
        except: # this is for the "else" case (ie, "map everything to x value")
            function = model[declaration]
            # print(FuncInterp.as_list(function))
            # print(FuncInterp.else_value(function))
            print(FuncInterp.num_entries(function))

            print(f"{declaration.name()} = {model[declaration]}")
            # rn this is printing a monster, not sure what to make of it
else:
    print("No model found")

# below is the output (the monster). Seems that this defaults to nand format :(
#output = And(
#        Not(
#            And(
#                Not(Var(0) == 1),
#                Not(Var(0) == 5),
#                Not(Var(0) == 8),
#                Not(Var(0) == 52),
#                Not(Var(0) == 40),
#                Not(Var(0) == 0),
#                Not(Var(0) == 4),
#                Not(Var(0) == 54),
#                Not(Var(0) == 47),
#                Not(Var(0) == 116)
#            )
#        ),
#        Not(
#            And(
#                Var(0) == 54,
#                Not(Var(0) == 47),
#                Not(Var(0) == 116)
#            )
#        ),
#        Not(
#            And(
#                Var(0) == 40,
#                Not(Var(0) == 0),
#                Not(Var(0) == 4),
#                Not(Var(0) == 54),
#                Not(Var(0) == 47),
#                Not(Var(0) == 116)
#            )
#        ),
#        Not(Var(0) == 116),
#        Not(
#            And(
#                Var(0) == 52,
#                Not(Var(0) == 40),
#                Not(Var(0) == 0),
#                Not(Var(0) == 4),
#                Not(Var(0) == 54),
#                Not(Var(0) == 47),
#                Not(Var(0) == 116)
#            )
#        ),
#        Not(
#            And(
#                Var(0) == 47, 
#                Not(Var(0) == 116)
#            )
#        ),
#        Not(
#            And(
#                Var(0) == 8,
#                Not(Var(0) == 52),
#                Not(Var(0) == 40),
#                Not(Var(0) == 0),
#                Not(Var(0) == 4),
#                Not(Var(0) == 54),
#                Not(Var(0) == 47),
#                Not(Var(0) == 116)
#            )
#        )
#    )