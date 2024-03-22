from z3 import *
from prefix_infix import *
from semantics import *
from definitions import *
from print import *
# everything different is in prefix_infix and semantics. Everything else is the same.
input_sentences = ['(A \\boxright B)','(B \\boxright C)','\\neg (A \\boxright C)']
prefix_sentences = [Prefix(input_sent) for input_sent in input_sentences] # this works
atomic_sentences = all_sentence_letters(prefix_sentences) # this works

solver = Solver()
add_general_constraints(solver) # I think this works
add_input_constraints(solver, prefix_sentences) # I think this is where the problem's at

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