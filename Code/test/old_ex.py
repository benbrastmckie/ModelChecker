
from model_structure import *
from z3 import *
# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = False

# present option to append output to file
save_bool = False

################################
############ SYNTAX ############
################################

### SENTENCES ###

# 'A', 'B', 'C',... can be used for sentence letters

# Alternatively, 'RedBall', 'MarySings',... can be used for sentence letters.

# 'top' is a designated sentence for the trivial truth verified by everything and falsified by nothing.


### UNARY OPERATORS ###

# Negation: 'neg', e.g., 'neg A'.
# Necessity: 'Box', e.g., 'Box A'.
# Possibility: 'Diamond', e.g., 'Diamond RedBall'. 


### BINARY OPERATORS ###

# Conjunction: 'wedge', e.g., '(A wedge B)'
# Disjunction: 'vee', e.g., '(A vee B)'
# Conditional: 'rightarrow', e.g., '(A rightarrow B)'
# Biconditional: 'leftrightarrow', e.g., '(A leftrightarrow B)'
# Counterfactual: 'boxright', e.g., '(A boxright B)' where 'A' cannot include 'Box', 'Diamond', or 'boxright'.

# NOTE: parentheses must always be included for binary operators.


################################
########## ARGUMENTS ###########
################################

### INVALID ###

premises = ['\\top']
conclusions = ['A']

### VALID ###

premises = ['((A vee B) boxright C)']
conclusions = ['(A boxright C)']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

premises = ['(A \\boxright B)','(B \\boxright C)']
conclusions = ['(A \\boxright C)']

premises = ['(A \\boxright ((B \\boxright C) \\wedge (D \\boxright E)))']
conclusions = ['C']

# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['B']

# premises = ['ball_is_red', '(ball_is_red boxright mary_likes_it)']
# conclusions = ['mary_likes_it']

# premises = ['R', '(R boxright L)']
# conclusions = ['L']

# # premises = ['A', '(A \\boxright B)']
# # conclusions = ['B']

# # premises = ['A', 'B']
# # conclusions = ['\\neg B']

# premises = ['(john_at_party wedge mary_at_party)', '(john_at_party boxright neg party_is_good)', '(mary_at_party boxright party_is_good)','party_is_good']
# conclusions = ['party_is_good']


mod_setup, mod_structure = make_model_for(N, premises, conclusions)
# print(mod_setup)
# print(mod_structure)
# print(mod_setup == mod_structure.model_setup)
# print(mod_structure.model_status)
if mod_structure:
    state_space = StateSpace(mod_setup, mod_structure)
    state_space.print_all(False, None)
