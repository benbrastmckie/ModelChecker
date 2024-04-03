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

sentence_letters = [A, B, C]

# NOTE: for now we may declare a fixed set of variables
# however, it is likely that at some point these definitions will have to be an
# output along with the constraints generated
aa, bb, cc = BitVecs("aa bb cc", N)
a, b, c = BitVecs("a b c", N)
r, s, t = BitVecs("r s t", N)
u, v, w = BitVecs("u v w", N)
x, y, z = BitVecs("x y z", N)

# everything different is in prefix_infix and semantics. Everything else is the same.
# input_sentences = ['(A \\boxright (B \\vee C))','\\neg (A \\boxright B)','\\neg (A \\boxright C)']
# input_sentences = ['(A \\boxright B)','((A \\wedge B) \\boxright C)','\\neg (A \\boxright C)']
# input_sentences = ['A','B','\\neg (A \\wedge B)']
# input_sentences = ['A','\\neg A'] # finds a model for a contradiction, something seems to be wrong
# input_sentences = ['A','B','\\neg (A \\wedge B)']
prefix_sentences = [Prefix(input_sent) for input_sent in input_sentences] # this works
print(f"Prefix Input Sentences:\n {prefix_sentences}")
sentence_letters = all_sentence_letters(prefix_sentences) # this works
# print(f"Sentence Letters: {sentence_letters}")

solver = Solver()
add_general_constraints(solver, sentence_letters) # should be working, it's nothing complicated
add_input_constraints(solver, prefix_sentences) # I think this is where the problem's at
# an issue may be whether the sentence letters are actually in the constraints. I think they are
# but the issue may also be about states (ie, bitvecs) and quantifier binding. 
# a new semantics file, semantics_2.py, with slightly different semantics, yields very different results

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
