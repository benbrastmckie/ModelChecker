```
There are no 3-models of:

Premises:
1. (A boxright C)
2. ((A boxright C) boxright (A boxright (B vee neg C)))

Conclusion:
3. (A boxright B)

Unsatisfiable core constraints:

1. Exists([f_x, f_u],
       And(verify(f_x, A),
           And(And(possible(f_u),
                   ForAll(max_x,
                          Implies(possible(max_x | f_u),
                                  max_x | f_u == f_u))),
               f_x | f_u == f_u,
               Exists(alt_z,
                      And(alt_z | f_u == f_u,
                          And(alt_z | w == w,
                              possible(alt_z | f_x),
                              ForAll(max_part,
                                     Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        f_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part)))))),
           Exists(f_x,
                  And(f_x | f_u == f_u, falsify(f_x, B)))))

2. ForAll([t_x, t_u],
       Implies(And(verify(t_x, A),
                   And(And(possible(t_u),
                           ForAll(max_x,
                                  Implies(possible(max_x |
                                        t_u),
                                        max_x | t_u == t_u))),
                       t_x | t_u == t_u,
                       Exists(alt_z,
                              And(alt_z | t_u == t_u,
                                  And(alt_z | w == w,
                                      possible(alt_z | t_x),
                                      ForAll(max_part,
                                        Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        t_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part))))))),
               Exists(t_x,
                      And(t_x | t_u == t_u, verify(t_x, C)))))

3. ForAll([t_x, t_u],
       Implies(And(ForAll([t_x, t_u],
                          Implies(And(verify(t_x, A),
                                      And(And(possible(t_u),
                                        ForAll(max_x,
                                        Implies(possible(max_x |
                                        t_u),
                                        max_x | t_u == t_u))),
                                        t_x | t_u == t_u,
                                        Exists(alt_z,
                                        And(alt_z | t_u ==
                                        t_u,
                                        And(alt_z | w == w,
                                        possible(alt_z | t_x),
                                        ForAll(max_part,
                                        Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        t_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part))))))),
                                  Exists(t_x,
                                        And(t_x | t_u == t_u,
                                        verify(t_x, C))))),
                   And(And(possible(t_u),
                           ForAll(max_x,
                                  Implies(possible(max_x |
                                        t_u),
                                        max_x | t_u == t_u))),
                       t_x | t_u == t_u,
                       Exists(alt_z,
                              And(alt_z | t_u == t_u,
                                  And(alt_z | w == w,
                                      possible(alt_z | t_x),
                                      ForAll(max_part,
                                        Implies(And(max_part |
                                        w ==
                                        w,
                                        possible(max_part |
                                        t_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part))))))),
               ForAll([t_x, t_u],
                      Implies(And(verify(t_x, A),
                                  And(And(possible(t_u),
                                        ForAll(max_x,
                                        Implies(possible(max_x |
                                        t_u),
                                        max_x | t_u == t_u))),
                                      t_x | t_u == t_u,
                                      Exists(alt_z,
                                        And(alt_z | t_u ==
                                        t_u,
                                        And(alt_z | t_u ==
                                        t_u,
                                        possible(alt_z | t_x),
                                        ForAll(max_part,
                                        Implies(And(max_part |
                                        t_u ==
                                        t_u,
                                        possible(max_part |
                                        t_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part))))))),
                              Or(Exists(t_x,
                                        And(t_x | t_u == t_u,
                                        verify(t_x, B))),
                                 Exists(f_x,
                                        And(f_x | t_u == t_u,
                                        falsify(f_x, C))))))))

Run time: 472.7449 seconds
```
