========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0288 seconds

========================================

State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (impossible)
  #b0100 = c
  #b0101 = a.c (world)
  #b0110 = b.c (world)
  #b0111 = a.b.c (impossible)
  #b1000 = d
  #b1001 = a.d (world)
  #b1010 = b.d (impossible)
  #b1011 = a.b.d (impossible)
  #b1100 = c.d (impossible)
  #b1101 = a.c.d (impossible)
  #b1110 = b.c.d (impossible)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: b.c

INTERPRETED PREMISES:

1.  |\neg A| = < {b.c}, {a, a.b.c.d} >  (True in b.c)
      |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)

2.  |(A \boxright C)| = < {a.c, b.c}, {a.d} >  (True in b.c)
      |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)
      |A|-alternatives to b.c = {a.c}
        |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (True in a.c)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < {}, {a.c, a.d, b.c} >  (False in b.c)
      |(A \wedge B)| = < {a.b, a.b.c, a.b.c.d, a.b.d, a.d}, {a.b.c, a.c, b.c} >  (False in b.c)
        |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)
        |B| = < {a.b, a.b.c, a.b.c.d, a.b.d, b, b.c.d, b.d, d}, {a.c} >  (True in b.c)
      |(A \wedge B)|-alternatives to b.c = {a.d}
        |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (False in a.d)


========================================