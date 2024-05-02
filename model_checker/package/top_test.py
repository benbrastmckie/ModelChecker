
'''
Model Checker: top_test.py
'''
import os
parent_directory = os.path.dirname(__file__)

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

# use constraints to find models in stead of premises and conclusions
use_constraints_bool = False

################################
########### ARGUMENT ###########
################################

### INVALID ###

# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']

### VALID ###

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

premises = ['\\neg (\\top \\boxright \\neg (A \\wedge B))','((A \\wedge B) \\boxright C)', 'F']
conclusions = ['(A \\boxright (B \\boxright C))']

# premises = ['(\\top \\boxright A)']
# conclusions = ['\\neg A'] # exists model, as desired
# conclusions = ['A'] # no models, as desired

