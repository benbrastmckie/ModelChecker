'''
converts infix_sentences to Z3 constraints and adds to solver, printing results
'''
import time
# import cProfile
# from pyinstrument import Profiler
# import multiprocessing # NOTE: couldn't get this to work (see below)
from semantics import (
    find_all_constraints,
    solve_constraints,
    combine,
)
from print import (
    print_constraints,
    print_model,
)

# TODO: define N here




################################
########### WORKING ############
################################


### INVALID ###

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# # conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']
# # # NOTE: does not work with exhaustivity
# # # NOTE: only the following conclusion works with prop constraints applied to sentence letters
# conclusions = ['(A \\boxright B)','(A \\boxright C)']

# # NOTE: only works with prop constraints applied to sentence letters
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']



### VALID ###

# # NOTE: only works with prop constraints applied to sentence letters
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

### HIGH PRIORITY ###

# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # premises = ['(A \\boxright C)']
# premises = ['\\neg A','(A \\boxright C)'] # NOTE: super slow
# conclusions = ['((A \\wedge B) \\boxright C)']

### MEDIUM PRIORITY ###

# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['(A \\boxright B)','\\neg B']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# NOTE: this is slow for N = 5 and does not find models for N = 3
premises = ['(A \\boxright (B \\boxright C))']
conclusions = ['((A \\wedge B) \\boxright C)']



################################
############ SOLVER ############
################################

"""find input sentences, sentence letters, and constraints"""
# constraints_start = time.time() # start benchmark timer
input_sentences = combine(premises,conclusions)
prefix_sentences, constraints, sentence_letters = find_all_constraints(input_sentences)
# constraints_end = time.time() # start benchmark timer
# constraints_total = round(constraints_end - constraints_start,4)
# print_constraints(constraints)

"""find model in any in timed enviornment"""
model_start = time.time() # start benchmark timer
# cProfile.run('model = solve_constraints(constraints)') # for detailed report
result, model = solve_constraints(constraints)
model_end = time.time()
model_total = round(model_end - model_start,4)

"""print results"""
print_start = time.time()
print_model(result, model, input_sentences, sentence_letters)
print_end = time.time()
print_total = round(print_end - print_start,4)
# print(f"Constraints time: {constraints_total}")
print(f"Model time: {model_total}")
print(f"Print time: {print_total}\n")


# NOTE: this works; must import pyinstrument
# profiler = Profiler()
# profiler.start()
# CODE
# profiler.stop()
# print(profiler.output_text(unicode=True, color=True))
