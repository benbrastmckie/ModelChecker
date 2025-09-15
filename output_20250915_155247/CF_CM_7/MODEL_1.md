========================================

EXAMPLE CF_CM_7: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premise:
1. (A \boxright B)

Conclusion:
2. (\neg B \boxright \neg A)

Z3 Run Time: 0.0096 seconds

========================================

State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (world)
  #b0110 = b.c (impossible)
  #b0111 = a.b.c (impossible)
  #b1000 = d (world)
  #b1001 = a.d (impossible)
  #b1010 = b.d (impossible)
  #b1011 = a.b.d (impossible)
  #b1100 = c.d (impossible)
  #b1101 = a.c.d (impossible)
  #b1110 = b.c.d (impossible)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: a.b

INTERPRETED PREMISE:

1.  |(A \boxright B)| = < {a.b}, {a.c, d} >  (True in a.b)
      |A| = < {a, a.b}, {d} >  (True in a.b)
      |A|-alternatives to a.b = {a.b}
        |B| = < {a.b.c, a.b.c.d, a.b.d, b}, {c, c.d, d} >  (True in a.b)

INTERPRETED CONCLUSION:

2.  |(\neg B \boxright \neg A)| = < {}, {a.b, a.c, d} >  (False in a.b)
      |\neg B| = < {c, c.d, d}, {a.b.c, a.b.c.d, a.b.d, b} >  (False in a.b)
        |B| = < {a.b.c, a.b.c.d, a.b.d, b}, {c, c.d, d} >  (True in a.b)
      |\neg B|-alternatives to a.b = {a.c, d}
        |\neg A| = < {d}, {a, a.b} >  (True in d)
          |A| = < {a, a.b}, {d} >  (False in d)
        |\neg A| = < {d}, {a, a.b} >  (False in a.c)
          |A| = < {a, a.b}, {d} >  (True in a.c)


========================================