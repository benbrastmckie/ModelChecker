'''This file includes all user inputs'''

# TODO: make it so that this file can be run while including all user inputs

# NOTE: aim was to import and use functions needed to find and print models
# import runpy
# import test_complete
# from test_complete import (
#     model_constraints,
#     model_print,
#     model_search,
# )


################################
########## VARIABLES ###########
################################

# number of atomic states
N = 3


################################
########## SETTINGS ############
################################

# NOTE: aim was to provide all user settings here that adjust the print statement

print_cons_bool = False
print_unsat_core_bool = True




################################
########## ARGUMENT ############
################################

# NOTE: aim was to provide input sentences here

################################
########### WORKING ############
################################


### INVALID ###

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']
# # conclusions = ['(A \\boxright B)','(A \\boxright C)']

# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']



### VALID ###

# premises = ['A','(A \\rightarrow B)']
# conclusions = ['B']

# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

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

# M: for the not working ones, can you put what the current output is (not
# making or making a model), and what the desired output is?
# B: are you able to run the file? I will add output to issues in github

### HIGH PRIORITY ###

# premises = ['(A \\boxright C)']
# # premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # premises = ['(A \\boxright C)']
# premises = ['\\neg A','(A \\boxright C)'] # NOTE: super slow
# conclusions = ['((A \\wedge B) \\boxright C)']

### MEDIUM PRIORITY ###

# # NOTE: this isn't finding models still
# # premises = ['(A \\boxright B)','\\neg B']
# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this is slow for N = 5 and does not find models for N = 3
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']




################################
############ SOLVER ############
################################

# NOTE: aim was to call functions here so that this file can be run
# still hitting circular imports problem

# NOTE: this requires runpy import above but doesn't work
# runpy.run_module('test_complete')

# constraints, input_sentences, sentence_letters = test_complete.model_constraints(premises, conclusions, print_cons_bool)
# result, model, model_total = test_complete.model_search(constraints)
# test_complete.model_print(result, model, input_sentences, sentence_letters, model_total)
