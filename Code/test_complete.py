from z3 import *
from prefix_infix import *
from semantics import *
from definitions import *
from print import *
input_sentences = ['(A \\boxright B)','((A \\wedge B) \\boxright C)','\\neg (A \\boxright B)']
prefix_sentences = [Prefix(input_sent) for input_sent in input_sentences]
atomic_sentences = all_sentence_letters(prefix_sentences)
print(atomic_sentences)
solver = Solver()
add_general_constraints(solver)
add_input_constraints(solver, prefix_sentences)

if solver.check() == sat:
    print("\nThere is a model of:")
    print(input_sentences)
    model = solver.model()
    print_states(model)
    print_evaluation(model, atomic_sentences)
    print_propositions(model, atomic_sentences)
else:
    print("\nThere are no models of:\n")
    print(input_sentences)