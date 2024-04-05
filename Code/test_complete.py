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
)
from print import (
    print_model,
)

# TODO: define N here


################################
########### WORKING ############
################################

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



################################
######### NOT WORKING ##########
################################

# NOTE: these are the highest priority
input_sentences = ['(A \\boxright C)','\\neg ((A \\wedge B) \\boxright C)'] # WEAKENING
# input_sentences = ['(A \\boxright C)','(B \\boxright C)','\\neg ((A \\wedge B) \\boxright C)'] # ABSORPTION
# input_sentences = ['(A \\boxright B)','(B \\boxright C)','\\neg (A \\boxright C)'] # TRANSITIVITY

# NOTE: requires recursive consideration of alternatives
# input_sentences = ['((A \\wedge B) \\boxright C)','\\neg (A \\boxright (B \\boxright C))']
# input_sentences = ['(A \\boxright (B \\boxright C))','\\neg ((A \\wedge B) \\boxright C)',]

# NOTE: likely to do with no alternatives issue
# input_sentences = ['(A \\boxright B)','\\neg B','\\neg (\\neg B \\boxright \\neg A)']
# input_sentences = ['\\neg A','\\neg (A \\boxright B)','\\neg (A \\boxright \\neg B)']

################################
############ SOLVER ############
################################


"""find constraints and sentence letters"""
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

# NOTE: adapt below to run multiprocessing
# if __name__ == '__main__':
#     constraints, sentence_letters = find_all_constraints(input_sentences)
#
#     # Divide constraints into smaller subsets
#     num_processes = multiprocessing.cpu_count() - 2  # Use all but two of the number of CPU cores
#     chunk_size = len(constraints) // num_processes
#     chunks = [constraints[i:i+chunk_size] for i in range(0, len(constraints), chunk_size)]
#
#     # Create a multiprocessing pool
#     with multiprocessing.Pool(processes=num_processes) as pool:
#         # Distribute solving tasks to different processes
#         results = pool.map(solve_con, chunks)
#
#     # Combine results from different processes
#     combined_results = combine_results(results)
#
#     # Close the pool to free up resources
#     pool.close()
#     pool.join()
#
#     # Process the results
#     if combined_results:
#         print("There is a model of:")
#         print(input_sentences)
#         print_states(model)
#         print_evaluation(model, sentence_letters)
#         print_propositions(model, sentence_letters)
#     else:
#         print("\nThere are no models of:\n")
#         print(input_sentences)
