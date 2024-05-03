# TITLE: test

"""
There is a 3-model of:

\neg A
(A \boxright (B \vee C))
\neg (A \boxright B)
\neg (A \boxright C)

Possible states:
  #b000 = □
  #b001 = a (world)
  #b010 = b (world)
  #b100 = c (world)

The evaluation world is a:
  A, B, C  (not true in a)

  |\neg A| = < {a}, {b, c} >
  \neg A-alternatives to a = {a}
    \neg A is true in a
    (B \vee C), A, B, C are not true in a

  |A| = < {b, c}, {a} >
  A-alternatives to a = {b, c}
    (B \vee C), A, C are true in b
    B, \neg A are not true in b
    (B \vee C), A, B are true in c
    C, \neg A are not true in c

  |(B \vee C)| = < {b, c}, {a} >
  (B \vee C)-alternatives to a = {b, c}
    (B \vee C), A, C are true in b
    B, \neg A are not true in b
    (B \vee C), A, B are true in c
    C, \neg A are not true in c

  |B| = < {c}, {a, b} >
  B-alternatives to a = {c}
    (B \vee C), A, B are true in c
    C, \neg A are not true in c

  |C| = < {b}, {a, c} >
  C-alternatives to a = {b}
    (B \vee C), A, C are true in b
    B, \neg A are not true in b

\neg A is True in a because:
A is False in a

(A \boxright (B \vee C)) is True in a because:
A is False in a
A-alternatives to a = {'b', 'c'}
eval world is now b
(B \vee C) is True in b because:
B is False in b
C is True in b
eval world is now c
(B \vee C) is True in c because:
B is True in c
C is False in c
A is False in a
(B \vee C) is False in a because:
B is False in a
C is False in a

\neg (A \boxright B) is False in a because:
(A \boxright B) is True in a because:
A is False in a
A-alternatives to a = {'b', 'c'}
eval world is now b
B is False in b
eval world is now c
B is True in c
A is False in a
B is False in a

\neg (A \boxright C) is False in a because:
(A \boxright C) is True in a because:
A is False in a
A-alternatives to a = {'b', 'c'}
eval world is now b
C is True in b
eval world is now c
C is False in c
A is False in a
C is False in a

Run time: 0.5092 seconds
"""

# path to parent directory
import os
parent_directory = os.path.dirname(__file__)

# input sentences
premises = ['\\neg A', '(A \\boxright (B \\vee C))', '\\neg (A \\boxright B)', '\\neg (A \\boxright C)']
conclusions = ['(A \\boxright B)', '(A \\boxright C)']

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
                                      ForAll(max_part_dummy,
                                        Implies(And(max_part_dummy |
                                        w ==
                                        w,
                                        possible(max_part_dummy |
                                        t_dummy_x),
                                        alt_dummy |
                                        max_part_dummy ==
                                        max_part_dummy),
                                        alt_dummy ==
                                        max_part_dummy))))))),
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
                              ForAll(max_part_dummy,
                                     Implies(And(max_part_dummy |
                                        w ==
                                        w,
                                        possible(max_part_dummy |
                                        f_dummy_x),
                                        alt_dummy |
                                        max_part_dummy ==
                                        max_part_dummy),
                                        alt_dummy ==
                                        max_part_dummy)))))),
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
                              ForAll(max_part_dummy,
                                     Implies(And(max_part_dummy |
                                        w ==
                                        w,
                                        possible(max_part_dummy |
                                        f_dummy_x),
                                        alt_dummy |
                                        max_part_dummy ==
                                        max_part_dummy),
                                        alt_dummy ==
                                        max_part_dummy)))))),
           Exists(f_dummy_x,
                  And(f_dummy_x | f_dummy_u == f_dummy_u,
                      falsify(f_dummy_x, C)))))]
