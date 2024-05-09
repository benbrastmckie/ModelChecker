# TITLE: test_output

"""
There is a 3-model of:

\neg A
(A boxright (B vee C))
\neg (A boxright B)
\neg (A boxright C)

Possible states:
  #b000 = □
  #b001 = a (world)
  #b010 = b (world)
  #b100 = c (world)

The evaluation world is a:
  A, B, C  (Not true in a)

1.  \neg A  (True in a)
    |A| = < {b, c}, {a} >  (False in a)

2.  (A boxright (B vee C))  (True in a)
    A-alternatives to a = {b, c}
    |A| = < {b, c}, {a} >  (False in a)
      (B vee C)  (True in b)
        |B| = < {c}, {a, b} >  (False in b)
        |C| = < {b}, {a, c} >  (True in b)
      (B vee C)  (True in c)
        |B| = < {c}, {a, b} >  (True in c)
        |C| = < {b}, {a, c} >  (False in c)

3.  \neg (A boxright B)  (False in a)
    (A boxright B)  (True in a)
      A-alternatives to a = {b, c}
      |A| = < {b, c}, {a} >  (False in a)
        |B| = < {c}, {a, b} >  (False in b)
        |B| = < {c}, {a, b} >  (True in c)

4.  \neg (A boxright C)  (False in a)
    (A boxright C)  (True in a)
      A-alternatives to a = {b, c}
      |A| = < {b, c}, {a} >  (False in a)
        |C| = < {b}, {a, c} >  (True in b)
        |C| = < {b}, {a, c} >  (False in c)

Run time: 0.5306 seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)

# input sentences
premises = ['\\neg A', '(A boxright (B vee C))', '\\neg (A boxright B)', '\\neg (A boxright C)']
conclusions = ['(A boxright B)', '(A boxright C)']

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
                   max_dummy | w == w))), Not(verify(0, C)), Not(falsify(0, C)), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, C),
                   verify(prop_dummy_y, C)),
               verify(prop_dummy_x | prop_dummy_y, C))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(falsify(prop_dummy_x, C),
                   falsify(prop_dummy_y, C)),
               falsify(prop_dummy_x | prop_dummy_y, C))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(verify(prop_dummy_x, C),
                   falsify(prop_dummy_y, C)),
               Not(possible(prop_dummy_x | prop_dummy_y)))), ForAll([prop_dummy_x, prop_dummy_y],
       Implies(And(possible(prop_dummy_x),
                   assign(prop_dummy_x, C) == prop_dummy_y),
               And(possible(prop_dummy_x | prop_dummy_y),
                   Or(verify(prop_dummy_y, C),
                      falsify(prop_dummy_y, C))))), Not(verify(0, A)), Not(falsify(0, A)), ForAll([prop_dummy_x, prop_dummy_y],
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
                      falsify(prop_dummy_y, B))))), Exists(f_dummy_x,
       And(f_dummy_x | w == w, falsify(f_dummy_x, A))), ForAll([t_dummy_x, t_dummy_u],
       Implies(And(verify(t_dummy_x, A),
                   And(And(possible(t_dummy_u),
                           ForAll(max_dummy,
                                  Implies(possible(max_dummy |
                                        t_dummy_u),
                                        max_dummy |
                                        t_dummy_u ==
                                        t_dummy_u))),
                       t_dummy_x | t_dummy_u == t_dummy_u,
                       Exists(alt_dummy,
                              And(alt_dummy | t_dummy_u ==
                                  t_dummy_u,
                                  And(alt_dummy | w == w,
                                      possible(alt_dummy |
                                        t_dummy_x),
                                      ForAll(max_part,
                                        Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        t_dummy_x),
                                        alt_dummy | max_part ==
                                        max_part),
                                        alt_dummy ==
                                        max_part))))))),
               Or(Exists(t_dummy_x,
                         And(t_dummy_x | t_dummy_u ==
                             t_dummy_u,
                             verify(t_dummy_x, B))),
                  Exists(t_dummy_x,
                         And(t_dummy_x | t_dummy_u ==
                             t_dummy_u,
                             verify(t_dummy_x, C)))))), Exists([f_dummy_x, f_dummy_u],
       And(verify(f_dummy_x, A),
           And(And(possible(f_dummy_u),
                   ForAll(max_dummy,
                          Implies(possible(max_dummy |
                                        f_dummy_u),
                                  max_dummy | f_dummy_u ==
                                  f_dummy_u))),
               f_dummy_x | f_dummy_u == f_dummy_u,
               Exists(alt_dummy,
                      And(alt_dummy | f_dummy_u == f_dummy_u,
                          And(alt_dummy | w == w,
                              possible(alt_dummy | f_dummy_x),
                              ForAll(max_part,
                                     Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        f_dummy_x),
                                        alt_dummy | max_part ==
                                        max_part),
                                        alt_dummy ==
                                        max_part)))))),
           Exists(f_dummy_x,
                  And(f_dummy_x | f_dummy_u == f_dummy_u,
                      falsify(f_dummy_x, B))))), Exists([f_dummy_x, f_dummy_u],
       And(verify(f_dummy_x, A),
           And(And(possible(f_dummy_u),
                   ForAll(max_dummy,
                          Implies(possible(max_dummy |
                                        f_dummy_u),
                                  max_dummy | f_dummy_u ==
                                  f_dummy_u))),
               f_dummy_x | f_dummy_u == f_dummy_u,
               Exists(alt_dummy,
                      And(alt_dummy | f_dummy_u == f_dummy_u,
                          And(alt_dummy | w == w,
                              possible(alt_dummy | f_dummy_x),
                              ForAll(max_part,
                                     Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        f_dummy_x),
                                        alt_dummy | max_part ==
                                        max_part),
                                        alt_dummy ==
                                        max_part)))))),
           Exists(f_dummy_x,
                  And(f_dummy_x | f_dummy_u == f_dummy_u,
                      falsify(f_dummy_x, C)))))]
