```
There is a 3-model of:

Premises:
1. \not A
2. (\not A \boxright B)

Conclusion:
3. B

Possible states:
  #b000 = □
  #b001 = a (world)

The evaluation world is a:
  A, B  (False in a)

Interpreted premises:

1.  |\not A| = < {a}, ∅ >  (True in a)
    |A| = < ∅, {a} >  (False in a)

2.  |(\not A \boxright B)| = < ∅, {□} >  (False in a)
    |\not A| = < {a}, ∅ >  (True in a)
      |A| = < ∅, {a} >  (False in a)
    \not A-alternatives to a = {a}
      |B| = < ∅, {a} >  (False in a)

Interpreted conclusion:

3.  |B| = < ∅, {a} >  (False in a)

Satisfiable FRAME constraints:

1. ForAll([frame_x, frame_y],
       Implies(And(possible(frame_y),
                   frame_x | frame_y == frame_y),
               possible(frame_x)))

2. ForAll([frame_x, frame_y],
       Exists(frame_z, frame_x | frame_y == frame_z))

3. And(possible(w),
    ForAll(max_x,
           Implies(possible(max_x | w), max_x | w == w)))

Satisfiable PROPOSITION constraints:

1. Not(verify(0, A))

2. Not(falsify(0, A))

3. ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, A), verify(prop_y, A)),
               verify(prop_x | prop_y, A)))

4. ForAll([prop_x, prop_y],
       Implies(And(falsify(prop_x, A), falsify(prop_y, A)),
               falsify(prop_x | prop_y, A)))

5. ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, A), falsify(prop_y, A)),
               Not(possible(prop_x | prop_y))))

6. ForAll([prop_x, prop_y],
       Implies(And(possible(prop_x),
                   assign(prop_x, A) == prop_y),
               And(possible(prop_x | prop_y),
                   Or(verify(prop_y, A), falsify(prop_y, A)))))

7. Not(verify(0, B))

8. Not(falsify(0, B))

9. ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, B), verify(prop_y, B)),
               verify(prop_x | prop_y, B)))

10. ForAll([prop_x, prop_y],
       Implies(And(falsify(prop_x, B), falsify(prop_y, B)),
               falsify(prop_x | prop_y, B)))

11. ForAll([prop_x, prop_y],
       Implies(And(verify(prop_x, B), falsify(prop_y, B)),
               Not(possible(prop_x | prop_y))))

12. ForAll([prop_x, prop_y],
       Implies(And(possible(prop_x),
                   assign(prop_x, B) == prop_y),
               And(possible(prop_x | prop_y),
                   Or(verify(prop_y, B), falsify(prop_y, B)))))

Satisfiable PREMISE constraints:

1. Exists(f_x, And(f_x | w == w, falsify(f_x, A)))

2. ForAll([t_x, t_u],
       Implies(And(And(ForAll(exclud_fal_x,
                              Implies(exclud_fal_x | t_x ==
                                      t_x,
                                      Exists(exclud_fal_y,
                                        And(verify(exclud_fal_y,
                                        A),
                                        Not(possible(exclud_fal_x |
                                        exclud_fal_y)))))),
                       ForAll(exclud_fal_x,
                              Implies(verify(exclud_fal_x,
                                        A),
                                      Exists(exclud_fal_y,
                                        And(exclud_fal_y |
                                        t_x ==
                                        t_x,
                                        Not(possible(exclud_fal_x |
                                        exclud_fal_y))))))),
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
                      And(t_x | t_u == t_u, verify(t_x, B)))))

Satisfiable CONCLUSION constraints:

1. Exists(f_x, And(f_x | w == w, falsify(f_x, B)))

Run time: 0.0249 seconds

ForAll [t_x, t_u]:
    If:
        # EVERY PART OF T_X IS INCOMPATIBLE WITH A VERIFIER FOR A
        # EVERY VERIFIER S_Y FOR A THERE IS A PART OF T_X THAT IS INCOMPATIBLE WITH S_Y
        # T_U IS A T_X-ALTERNATIVE WORLD TO W
    Then:
        # B IS TRUE AT T_U

```
