========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0146 seconds

========================================

State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (impossible)
  #b0110 = b.c (world)
  #b0111 = a.b.c (impossible)
  #b1000 = d
  #b1001 = a.d (world)
  #b1010 = b.d (world)
  #b1011 = a.b.d (impossible)
  #b1100 = c.d (world)
  #b1101 = a.c.d (impossible)
  #b1110 = b.c.d (impossible)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: a.b

INTERPRETED PREMISES:

1.  |\neg A| = < {a.b, a.b.c, b.c}, {a.b.c.d, d} >  (True in a.b)
      |A| = < {a.b.c.d, d}, {a.b, a.b.c, b.c} >  (False in a.b)

2.  |(A \boxright C)| = < {a.b, a.d, b.d}, {b.c, c.d} >  (True in a.b)
      |A| = < {a.b.c.d, d}, {a.b, a.b.c, b.c} >  (False in a.b)
      |A|-alternatives to a.b = {a.d, b.d}
        |C| = < {a, a.b.c, a.b.c.d, a.b.d, b.c, b.c.d, b.d}, {c.d} >  (True in b.d)
        |C| = < {a, a.b.c, a.b.c.d, a.b.d, b.c, b.c.d, b.d}, {c.d} >  (True in a.d)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < {}, {a.b, a.d, b.c, b.d, c.d} >  (False in a.b)
      |(A \wedge B)| = < {a.b.c.d, a.b.d, a.c.d, b.c.d, c.d}, {a.b, a.b.c, a.b.c.d, a.b.d, a.d, b.c, b.c.d, b.d} >  (False in a.b)
        |A| = < {a.b.c.d, d}, {a.b, a.b.c, b.c} >  (False in a.b)
        |B| = < {a.b, a.b.c, a.b.c.d, a.c.d, b.c.d, c, c.d}, {a.b.d, a.d, b.d} >  (True in a.b)
      |(A \wedge B)|-alternatives to a.b = {c.d}
        |C| = < {a, a.b.c, a.b.c.d, a.b.d, b.c, b.c.d, b.d}, {c.d} >  (False in c.d)


========================================