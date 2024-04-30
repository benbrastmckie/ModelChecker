
There are no 3-models of:

\neg A
(A \boxright C)
\neg ((A \wedge B) \boxright C)

Unsatisfiable core constraints:

1. Exists(f_dummy_x,
       And(f_dummy_x | w == w, falsify(f_dummy_x, A)))

2. ForAll([t_dummy_x, t_dummy_u],
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
               Exists(t_dummy_x,
                      And(t_dummy_x | t_dummy_u == t_dummy_u,
                          verify(t_dummy_x, C)))))

3. Exists([f_dummy_x, f_dummy_u],
       And(Exists([ex_ver_dummy_y, ex_ver_dummy_z],
                  And(ex_ver_dummy_y | ex_ver_dummy_z ==
                      f_dummy_x,
                      verify(ex_ver_dummy_y, A),
                      verify(ex_ver_dummy_z, B))),
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
                      falsify(f_dummy_x, C)))))

Run time: 75.7474 seconds

