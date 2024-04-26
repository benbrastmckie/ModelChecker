
There are no 3-models of:

\neg B
(A \boxright B)
\neg (\neg B \boxright \neg A)

Unsatisfiable core constraints:

```
1. Exists(f_dummy_x,
       And(f_dummy_x | w == w, falsify(f_dummy_x, B)))

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
                          verify(t_dummy_x, B)))))

3. Exists([f_dummy_x, f_dummy_u],
       And(falsify(f_dummy_x, B),
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
           Exists(t_dummy_x,
                  And(t_dummy_x | f_dummy_u == f_dummy_u,
                      verify(t_dummy_x, A)))))

4. Exists(prop_dummy_y,
       And(And(Not(prop_dummy_y == 0),
               falsify(prop_dummy_y, A)),
           possible(prop_dummy_y)))

5. Exists(prop_dummy_x,
       And(And(Not(prop_dummy_x == 0),
               verify(prop_dummy_x, B)),
           possible(prop_dummy_x)))
```


There are no 3-models of:

\neg A
(A \boxright C)
\neg ((A \wedge B) \boxright C)

Unsatisfiable core constraints:

