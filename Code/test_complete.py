'''
converts infix_sentences to Z3 constraints and adds to solver, printing results
'''
import time
import cProfile
# from pyinstrument import Profiler
# import multiprocessing # NOTE: couldn't get this to work (see below)
from semantics import (
    find_all_constraints,
    solve_constraints,
    combine,
)
from print import (
    print_model,
)

# TODO: define N here




################################
########### WORKING ############
################################


### INVALID ###

premises = ['\\neg A','(A \\boxright (B \\vee C))','\\neg (A \\boxright B)']
conclusions = ['\\neg (A \\boxright C)']

# premises = ['(A \\boxright (B \\vee C))']
# conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']

# premises = ['A','B']
# conclusions = ['(A \\boxright B)']


### VALID ###

# premises = ['(A \\rightarrow B)','A']
# conclusions = ['B']

# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
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

# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']


### MEDIUM PRIORITY ###

# NOTE: likely to do with no alternatives issue
# premises = ['(A \\boxright B)','\\neg B']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# NOTE: likely to do with no alternatives issue
# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']


### LOW PRIORITY ###

# NOTE: requires recursive consideration of alternatives
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# NOTE: requires recursive consideration of alternatives
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']





################################
############ SOLVER ############
################################

"""find input sentences, sentence letters, and constraints"""
input_sentences = combine(premises,conclusions)
constraints, sentence_letters = find_all_constraints(input_sentences)

"""find model in any in timed enviornment"""
start_time = time.time() # start benchmark timer
# cProfile.run('model = solve_constraints(constraints)') # for detailed report
model = solve_constraints(constraints)
end_time = time.time()

"""print results"""
print_model(model, input_sentences, sentence_letters)
execution_time = end_time - start_time
print(f"Execution time: {execution_time}\n")


# NOTE: this works; must import pyinstrument
# profiler = Profiler()
# profiler.start()
# CODE
# profiler.stop()
# print(profiler.output_text(unicode=True, color=True))
