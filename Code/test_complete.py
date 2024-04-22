from model_structure import (
    ModelStructure,
)
from definitions import N


################################
########## SETTINGS ############
################################

# TODO: define bitvec length N here
# NOTE: N needs to be removed from definitions.py
# N = 3

print_cons_bool = False
print_unsat_core_bool = True


################################
########### WORKING ############
################################


### INVALID ###

premises = ['\\neg A','(A \\boxright (B \\vee C))']
conclusions = ['(A \\boxright B)','(A \\boxright C)']

# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# premises = ['(A \\boxright C)'] # works
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']


### VALID ###

# premises = ['A','(A \\rightarrow B)']
# conclusions = ['B']

# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # takes very long with new semantics on my (M) machine
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']

# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']




################################
######### NOT WORKING ##########
################################

### HIGH PRIORITY ###

# # NOTE: doesn't work b/c should countermodel
# # recursive printing would be helpful.
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: should find a model. works without `\\neg A`.
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

### MEDIUM PRIORITY ###

# # NOTE: this isn't finding models still
# premises = ['(A \\boxright B)','\\neg B']
# conclusions = ['(\\neg B \\boxright \\neg A)']


# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this is slow for N = 5 and does not find models for N = 3
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']



# this is what used to be print_model, can easily make this an attribute if wanted

################################
############ SOLVER ############
################################

mod = ModelStructure(premises, conclusions)
mod.solve(N)
mod.print_all(N, print_cons_bool, print_unsat_core_bool)
