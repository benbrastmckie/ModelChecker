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
from user_input import (
    # NOTE: add these once user_input can be run
    # premises,
    # conclusions,
    print_cons_bool,
    print_unsat_core_bool,
)



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

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# premises = ['(A \\boxright C)'] # works
# conclusions = ['((A \\wedge B) \\boxright C)']



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

# M: for the not working ones, can you put what the current output is (not
# making or making a model), and what the desired output is?
# B: are you able to run the file? I will add output to issues in github

### HIGH PRIORITY ###

# # NOTE: doesn't work b/c should countermodel
# # recursive printing would be helpful.
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: should find a model. works without `\\neg A`.
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

### MEDIUM PRIORITY ###

# NOTE: this isn't finding models still
premises = ['(A \\boxright B)','\\neg B']
# NOTE: this seems to work now but the print statement is hard to read
# premises = ['(A \\boxright B)']
conclusions = ['(\\neg B \\boxright \\neg A)']


# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this is slow for N = 5 and does not find models for N = 3
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']



################################
############ SOLVER ############
################################

# TODO: can these functions be improved? It seems like prefix_sentences doesn't
# do anything. also model_print has a lot of arguments. maybe these can be reduced?

def model_constraints(premises, conclusions, print_cons_bool):
    """find input sentences, sentence letters, and constraints"""
    constraints_start = time.time() # start benchmark timer
    input_sentences = combine(premises,conclusions)
    prefix_sentences, constraints, sentence_letters = find_all_constraints(input_sentences)
    constraints_end = time.time() # start benchmark timer
    constraints_total = round(constraints_end - constraints_start,4)
    if print_cons_bool:
        print_constraints(constraints, constraints_total)
    return (constraints, input_sentences, sentence_letters)

def model_search(constraints):
    """find model in a timed enviornment"""
    model_start = time.time() # start benchmark timer
    # cProfile.run('model = solve_constraints(constraints)') # for detailed report
    result, model = solve_constraints(constraints)
    model_end = time.time()
    model_total = round(model_end - model_start,4)
    return (result, model, model_total)

def model_print(result, model, input_sentences, sentence_letters, print_unsat_core_bool):
    """print results"""
    print_start = time.time()
    print_model(result, model, input_sentences, sentence_letters, print_unsat_core_bool)
    print_end = time.time()
    print_total = round(print_end - print_start,4)
    # print(f"Constraints time: {constraints_total}")
    print(f"Model time: {model_total}")
    print(f"Print time: {print_total}\n")

constraints, input_sentences, sentence_letters = model_constraints(premises, conclusions, print_cons_bool)
result, model, model_total = model_search(constraints)
model_print(result, model, input_sentences, sentence_letters, print_unsat_core_bool)

# NOTE: this works; must import pyinstrument
# profiler = Profiler()
# profiler.start()
# CODE
# profiler.stop()
# print(profiler.output_text(unicode=True, color=True))
