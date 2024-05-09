from model_structure import *
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

premises = ['neg A','(A boxright (B vee C))']
conclusions = ['(A boxright B)','(A boxright C)']

### VALID ###

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

mod = make_model_for(N)(premises, conclusions)

mod.print_to(print_cons_bool, print_unsat_core_bool)