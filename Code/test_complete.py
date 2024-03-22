from z3 import *
from prefix_infix import *
from semantics import *
from definitions import *
from print import *
# everything different is in prefix_infix and semantics. Everything else is the same.
input_sentences = ['(A \\boxright B)','(B \\boxright C)','\\neg (A \\boxright C)']
prefix_sentences = [Prefix(input_sent) for input_sent in input_sentences] # this works
sentence_letters = all_sentence_letters(prefix_sentences) # this works

solver = Solver()
add_general_constraints(solver) # I should be working, it's nothing complicated
add_input_constraints(solver, prefix_sentences) # I think this is where the problem's at
# an issue may be whether the sentence letters are actually in the constraints. I think they are
# but the issue may also be about states (ie, bitvecs) and quantifier binding. 
# a new semantics file, semantics_2.py, with slightly different semantics, yields very different results

if solver.check() == sat:
    print("\nThere is a model of:")
    print(input_sentences)
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print(input_sentences)

# please just work
# please please
    # attepmt 3