from z3 import (
    Solver,
    sat,
    BitVecs,
)
from prefix_infix import (
    Prefix,
    all_sentence_letters,
)
# from semantics_2 import (
from semantics import (
    add_input_constraints,
    add_general_constraints,
)
from definitions import (
    N,
    A,
    B,
    C,
)
from print import (
    print_states,
    print_evaluation,
    print_propositions,
)

import time

sentence_letters = [A, B, C]

# NOTE: for now we may declare a fixed set of variables
# however, it is likely that at some point these definitions will have to be an
# output along with the constraints generated
aa, bb, cc = BitVecs("aa bb cc", N)
a, b, c = BitVecs("a b c", N)
r, s, t = BitVecs("r s t", N)
u, v, w = BitVecs("u v w", N)
x, y, z = BitVecs("x y z", N)



################################
############ TESTS #############
################################

### WORKING ###

# INVALID
# input_sentences = ['\\neg A','(A \\boxright (B \\vee C))','\\neg (A \\boxright B)','\\neg (A \\boxright C)']
# input_sentences = ['(A \\boxright (B \\vee C))','\\neg ((A \\boxright B) \\vee (A \\boxright C))']
# input_sentences = ['A','B','\\neg (A \\boxright B)']

# VALID
# input_sentences = ['(A \\rightarrow B)','A','\\neg B']
# input_sentences = ['(A \\boxright B)','\\neg (A \\rightarrow B)']
# input_sentences = ['((A \\vee B) \\boxright C)','\\neg (A \\boxright C)']
# input_sentences = ['((A \\vee B) \\boxright C)','\\neg ((A \\wedge B) \\boxright C)']
# input_sentences = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)','\\neg ((A \\vee B) \\boxright C)']
# input_sentences = ['(A \\boxright (B \\wedge C))','\\neg (A \\boxright B)']
# input_sentences = ['(A \\boxright B)','(A \\boxright C)','\\neg (A \\boxright (B \\wedge C))']
# input_sentences = ['(A \\boxright B)','((A \\wedge B) \\boxright C)','\\neg (A \\boxright C)']

### NOT WORKING ###

# NOTE: these are the highest priority
input_sentences = ['(A \\boxright B)','(B \\boxright C)','\\neg (A \\boxright C)']
# input_sentences = ['(A \\boxright C)','(B \\boxright C)','\\neg ((A \\wedge B) \\boxright C)']
# input_sentences = ['(A \\boxright C)','\\neg ((A \\wedge B) \\boxright C)']

# NOTE: requires recursive consideration of alternatives
# input_sentences = ['((A \\wedge B) \\boxright C)','\\neg (A \\boxright (B \\boxright C))']
# input_sentences = ['(A \\boxright (B \\boxright C))','\\neg ((A \\wedge B) \\boxright C)',]

# NOTE: likely to do with no alternatives issue
# input_sentences = ['(A \\boxright B)','\\neg B','\\neg (\\neg B \\boxright \\neg A)']
# input_sentences = ['\\neg A','\\neg (A \\boxright B)','\\neg (A \\boxright \\neg B)']

prefix_sentences = [Prefix(input_sent) for input_sent in input_sentences] # this works
# print(f"Prefix Input Sentences:\n {prefix_sentences}")
sentence_letters = all_sentence_letters(prefix_sentences) # this works
# print(f"Sentence Letters: {sentence_letters}")

solver = Solver()
add_general_constraints(solver, sentence_letters) # should be working, it's nothing complicated
add_input_constraints(solver, prefix_sentences) # I think this is where the problem's at
# an issue may be whether the sentence letters are actually in the constraints. I think they are
# but the issue may also be about states (ie, bitvecs) and quantifier binding. 
# a new semantics file, semantics_2.py, with slightly different semantics, yields very different results

start_time = time.time()

if solver.check() == sat:
    print("There is a model of:")
    print(input_sentences)
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print(input_sentences)

end_time = time.time()
execution_time = end_time - start_time

print("Execution time:", execution_time)
