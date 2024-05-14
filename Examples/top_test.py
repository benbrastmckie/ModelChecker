'''
Model Checker: top_test.py
'''
import os
parent_directory = os.path.dirname(__file__)
from model_structure import make_model_for

################################
########## SETTINGS ############
################################

# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to append output to file
save_bool = False

################################
########### ARGUMENT ###########
################################

### INVALID ###

# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']

### VALID ###

# premises = ['(\\top \\boxright (A \\boxright B))', 'A']
# conclusions = ['\\neg B']

# premises = ['(\\top \\boxright A)', '((A \\wedge B) \\boxright C)', '\\neg (\\top \\boxright \\neg D)']
# conclusions = ['\\neg A']

# premises = ['(\\top \\boxright A)']
# # conclusions = ['\\neg A'] # exists model, as desired
# conclusions = ['A'] # no models, as desired
# conclusions = ['\\neg (\\top \\boxright \\neg A)'] # no models, as desired

# should this be valid? to me it seems intuitively it should be, but not sure
# B: yes this should be valid but it crashed the mit servers. I added it to examples
premises = ['Box A', '((A \\wedge B) \\boxright C)']
conclusions = ['(B \\boxright C)']

# premises = ['\\Box A']
# premises = ['\\Diamond A']
# conclusions = ['A']

mod = make_model_for(N)(premises, conclusions)
# mod.print_inputs_recursively()
# mod.print_evaluation()
mod.print_to(print_cons_bool, print_unsat_core_bool)
# print(mod.sentence_letters)
# print(mod.all_subsentences)
# for sent_let in mod.sentence_letters:
#     print(sent_let, type(sent_let))

