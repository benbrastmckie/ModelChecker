# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import *
from definitions import *
from print import *

# TODO: eventually replace sentence_letters with something more general
sentence_letters = [A, B, C]

solver = Solver()











if solver.check() == sat:
    print("\nThere is a model of:")
    print("A => B")
    print("B => C")
    print("~(A => C)")
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A => B")
    print("B => C")
    print("~(A => C)")