
There are no 3-models of:

\neg A
\neg B
(A \boxright B)
(B \boxright C)
\neg (A \boxright C)

Unsatisfiable core constraints:

1. Exists(f_dummy_x,
       And(f_dummy_x | w == w, falsify(f_dummy_x, A)))

2. Exists(f_dummy_x,
       And(f_dummy_x | w == w, falsify(f_dummy_x, B)))

3. ForAll([t_dummy_x, t_dummy_u],
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
                          verify(t_dummy_x, B)))))

4. ForAll([t_dummy_x, t_dummy_u],
       Implies(And(verify(t_dummy_x, B),
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

5. Exists([f_dummy_x, f_dummy_u],
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
                      falsify(f_dummy_x, C)))))

Run time: 126.3784 seconds

