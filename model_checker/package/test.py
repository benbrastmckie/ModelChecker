# TITLE: test

"""
There is a 3-model of:

A

Possible states:
  #b000 = □ (possible)
  #b001 = a (possible)
  #b010 = b (world)
  #b100 = c (possible)
  #b101 = a.c (world)

The evaluation world is b:
  A  (true in b)

  |A| = < {b}, {a} >
  A-alternatives to b = {b}
    A is true in b

Run time: 0.0358 seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)

# input sentences
premises = ['A']
conclusions = []

# number of atomic states
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to save output
save_bool = False

