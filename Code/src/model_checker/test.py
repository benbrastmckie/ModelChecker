from model_structure import *
from syntax import *

"don't delete this file yet, I'll delete it once I'm done debugging"
################################
########## SETTINGS ############
################################

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

premises = ['ball_is_red', '(ball_is_red rightarrow neg mary_likes_it)']
conclusions = ['mary_likes_it']

# premises = ['A', '(A \\boxright B)']
# conclusions = ['B']

# premises = ['A', 'B']
# conclusions = ['\\neg B']


mod = make_model_for(N)(premises, conclusions)
mod.solve()
mod.print_to(print_cons_bool, print_unsat_core_bool, True)
if mod.model_status:
    A = Const('ball_is_red', AtomSort)
    print(mod.find_proposition_object(str(A), prefix_search=False))
    red_prop = mod.find_proposition_object([A], prefix_search=True) # it finds a Proposition object
    print([bitvec_to_substates(ver, mod.N) for ver in red_prop['verifiers']])
    # prints ['b.c', 'a.b.c', 'b', 'a', 'c', 'a.c', 'a.b']
    # so moreover, that Proposition object (red_prop) has the same verifiers as the one printed by
    # the model before
