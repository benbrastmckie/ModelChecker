```
There are no 3-models of:

Premise:
1. A

Conclusion:
2. (top boxright neg (top boxright neg A))

Unsatisfiable core constraints:

1. Exists(t_x, And(t_x | w == w, verify(t_x, A)))

2. Exists([f_x, f_u],
       And(verify(f_x, top),
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
           ForAll([t_x, t_u],
                  Implies(And(verify(t_x, top),
                              And(And(possible(t_u),
                                      ForAll(max_x,
                                        Implies(possible(max_x |
                                        t_u),
                                        max_x | t_u == t_u))),
                                  t_x | t_u == t_u,
                                  Exists(alt_z,
                                        And(alt_z | t_u ==
                                        t_u,
                                        And(alt_z | f_u ==
                                        f_u,
                                        possible(alt_z | t_x),
                                        ForAll(max_part,
                                        Implies(And(max_part |
                                        f_u ==
                                        f_u,
                                        possible(max_part |
                                        t_x),
                                        alt_z | max_part ==
                                        max_part),
                                        alt_z == max_part))))))),
                          Exists(f_x,
                                 And(f_x | t_u == t_u,
                                     falsify(f_x, A)))))))

Run time: 1599.6635 seconds
```
