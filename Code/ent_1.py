# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import *
from definitions import *
from print import *

# TODO: eventually replace sentence_letters with something more general
sentence_letters = [A, B, C]

solver = Solver()

solver.add(

    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion

    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),
    # every X of AtomSort is a proposition
    is_world(w),
    # there is a world w




)












if solver.check() == sat:
    print("\nThere is a model of:")
    print("A => B")
    print("~(B -> A)")
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A => B")
    print("~(A -> C)")
