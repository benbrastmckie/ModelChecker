# TITLE: testabcd

"""

There are no 3-models of:

\neg (A vee neg A)

# unsatisfiable core constraints
1. And(Exists(f_x, And(f_x | w == w, falsify(f_x, A))),
    Exists(t_x, And(t_x | w == w, verify(t_x, A))))

2. ForAll([frame_x, frame_y],
       Exists(frame_z, frame_x | frame_y == frame_z))

"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)

# input sentences
premises = ['\\neg (A vee neg A)']
conclusions = ['(A vee neg A)']

# number of atomic states
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to save output
save_bool = False

# use constraints to find models in stead of premises and conclusions
use_constraints_bool = False

all_constraints = [ForAll([frame_x, frame_y],
       Implies(And(possible(frame_y),
                   frame_x | frame_y == frame_y),
               possible(frame_x))), ForAll([frame_x, frame_y],
       Exists(frame_z, frame_x | frame_y == frame_z)), And(possible(w),
    ForAll(max_x,
           Implies(possible(max_x | w), max_x | w == w))), Not(verify(0, A)), Not(falsify(0, A)), ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, A), verify(prop_y, A)),
               verify(prop_x | prop_y, A))), ForAll([prop_x, prop_y],
       Implies(And(falsify(prop_x, A), falsify(prop_y, A)),
               falsify(prop_x | prop_y, A))), ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, A), falsify(prop_y, A)),
               Not(possible(prop_x | prop_y)))), ForAll([prop_x, prop_y],
       Implies(And(possible(prop_x),
                   assign(prop_x, A) == prop_y),
               And(possible(prop_x | prop_y),
                   Or(verify(prop_y, A), falsify(prop_y, A))))), And(Exists(f_x, And(f_x | w == w, falsify(f_x, A))),
    Exists(t_x, And(t_x | w == w, verify(t_x, A))))]
