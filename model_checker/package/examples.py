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
append_bool = False


################################
########### WORKING ############
################################


### INVALID ###

# premises = []
# conclusions = []

# premises = ['A']
# conclusions = []

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']

# premises = ['Ball_is_red','Mary_loves_it']
# conclusions = ['(Ball_is_red \\boxright Mary_loves_it)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']

# # NOTE: slow with non_triv_verify/falsify constraints
# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# # NOTE: slow with both skolemized exhaustivity and non_triv_verify/falsify constraints
# # NOTE: not slow with either individually
# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# premises = ['A \\boxright C', '\\neg (A \\boxright \\neg B)']
# conclusions = ['\\neg ((A \\wedge B) \\boxright C)']


### VALID ###

# premises = ['A','(A \\rightarrow B)']
# conclusions = ['B']

# # NOTE: crashes with non_triv_verify/falsify and without skolemized exhaustivity
# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']

premises = ['(A \\boxright B)','(A \\boxright C)']
conclusions = ['(A \\boxright (B \\wedge C))']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']


################################
######### NOT WORKING ##########
################################


### HIGH PRIORITY: NEGATION PROBLEM ###

# # NOTE: ssh finds unsat_core but should have countermodels
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # NOTE: ssh finds unsat_core but should have countermodels
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']


### MEDIUM PRIORITY ###

# # NOTE: it is finding a model by making A and B incompatible
# # premises = ['\\neg ((A \\wedge B) \\boxright D)','((A \\wedge B) \\boxright C)']
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this does not find models for N = 3
# # very slow for N = 5 (ran for minutes on the remote server)
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: doesn't work b/c should countermodel
# # recursive printing would be helpful.
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
