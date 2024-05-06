# TITLE: test

"""
There is a 3-model of:

\Diamond A
\Diamond B
\neg \Diamond (A \wedge B)

Possible states:
  #b000 = □
  #b001 = a (world)
  #b010 = b (world)
  #b100 = c (world)

The evaluation world is c:
  A  (True in c)
  B  (Not true in c)

1.  \Diamond A  (True in c)
    |A| = < {b, c}, {a} >  (False in a)
    |A| = < {b, c}, {a} >  (True in b)
    |A| = < {b, c}, {a} >  (True in c)

2.  \Diamond B  (True in c)
    |B| = < {a}, {b, c} >  (True in a)
    |B| = < {a}, {b, c} >  (False in b)
    |B| = < {a}, {b, c} >  (False in c)

3.  \neg \Diamond (A \wedge B)  (True in c)
    \Diamond (A \wedge B)  (False in c)
      (A \wedge B)  (False in a)
        |A| = < {b, c}, {a} >  (False in a)
        |B| = < {a}, {b, c} >  (True in a)
      (A \wedge B)  (False in b)
        |A| = < {b, c}, {a} >  (True in b)
        |B| = < {a}, {b, c} >  (False in b)
      (A \wedge B)  (False in c)
        |A| = < {b, c}, {a} >  (True in c)
        |B| = < {a}, {b, c} >  (False in c)

Run time: 0.1222 seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)

# input sentences
premises = ['\\Diamond A', '\\Diamond B', '\\neg \\Diamond (A \\wedge B)']
conclusions = ['\\Diamond (A \\wedge B)']

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


# satisfiable constraints
all_constraints = [ForAll([frame_dummy_x, frame_dummy_y],
       Implies(And(possible(frame_dummy_y),
                   frame_dummy_x | frame_dummy_y ==
                   frame_dummy_y),
               possible(frame_dummy_x))), ForAll([frame_dummy_x, frame_dummy_y],
       Exists(frame_dummy_z,
              frame_dummy_x | frame_dummy_y == frame_dummy_z)), And(possible(w),
    ForAll(max_dummy,
           Implies(possible(max_dummy | w),
                   max_dummy | w == w))), Not(verify(0, A)), Not(falsify(0, A)), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, A),
                   verify(prop_dummy_y, A)),
               verify(prop_dummy_x | prop_dummy_y, A))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(falsify(prop_dummy_x, A),
                   falsify(prop_dummy_y, A)),
               falsify(prop_dummy_x | prop_dummy_y, A))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, A),
                   falsify(prop_dummy_y, A)),
               Not(possible(prop_dummy_x | prop_dummy_y)))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(possible(prop_dummy_x),
                   assign(prop_dummy_x, A) == prop_dummy_y),
               And(possible(prop_dummy_x | prop_dummy_y),
                   Or(verify(prop_dummy_y, A),
                      falsify(prop_dummy_y, A))))), Not(verify(0, B)), Not(falsify(0, B)), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, B),
                   verify(prop_dummy_y, B)),
               verify(prop_dummy_x | prop_dummy_y, B))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(falsify(prop_dummy_x, B),
                   falsify(prop_dummy_y, B)),
               falsify(prop_dummy_x | prop_dummy_y, B))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, B),
                   falsify(prop_dummy_y, B)),
               Not(possible(prop_dummy_x | prop_dummy_y)))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(possible(prop_dummy_x),
                   assign(prop_dummy_x, B) == prop_dummy_y),
               And(possible(prop_dummy_x | prop_dummy_y),
                   Or(verify(prop_dummy_y, B),
                      falsify(prop_dummy_y, B))))), Exists(t_dummy_u,
       And(And(possible(t_dummy_u),
               ForAll(max_dummy,
                      Implies(possible(max_dummy | t_dummy_u),
                              max_dummy | t_dummy_u ==
                              t_dummy_u))),
           Exists(t_dummy_x,
                  And(t_dummy_x | t_dummy_u == t_dummy_u,
                      verify(t_dummy_x, A))))), Exists(t_dummy_u,
       And(And(possible(t_dummy_u),
               ForAll(max_dummy,
                      Implies(possible(max_dummy | t_dummy_u),
                              max_dummy | t_dummy_u ==
                              t_dummy_u))),
           Exists(t_dummy_x,
                  And(t_dummy_x | t_dummy_u == t_dummy_u,
                      verify(t_dummy_x, B))))), ForAll(f_dummy_u,
       Implies(And(possible(f_dummy_u),
                   ForAll(max_dummy,
                          Implies(possible(max_dummy |
                                        f_dummy_u),
                                  max_dummy | f_dummy_u ==
                                  f_dummy_u))),
               Or(Exists(f_dummy_x,
                         And(f_dummy_x | f_dummy_u ==
                             f_dummy_u,
                             falsify(f_dummy_x, A))),
                  Exists(f_dummy_x,
                         And(f_dummy_x | f_dummy_u ==
                             f_dummy_u,
                             falsify(f_dummy_x, B))))))]
