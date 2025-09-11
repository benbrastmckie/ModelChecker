========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.026 seconds

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

---

========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0257 seconds

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
  #b1010 = b.d (world)
  #b1011 = a.b.d (impossible)
  #b1100 = c.d (impossible)
  #b1101 = a.c.d (impossible)
  #b1110 = b.c.d (impossible)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: a.d

INTERPRETED PREMISES:

1.  |\neg A| = < {a}, {a.b.c.d, b, b.c.d} >  (True in a.d)
      |A| = < {a.b.c.d, b, b.c.d}, {a} >  (False in a.d)

2.  |(A \boxright C)| = < {a.d, b.d}, {a.c, b.c} >  (True in a.d)
      |A| = < {a.b.c.d, b, b.c.d}, {a} >  (False in a.d)
      |A|-alternatives to a.d = {b.d}
        |C| = < {d}, {a.b.c, a.c, b.c} >  (True in b.d)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < {}, {a.c, a.d, b.c, b.d} >  (False in a.d)
      |(A \wedge B)| = < {a.b, a.b.c, a.b.c.d, b.c, b.c.d}, {a, a.b.d, b.d} >  (False in a.d)
        |A| = < {a.b.c.d, b, b.c.d}, {a} >  (False in a.d)
        |B| = < {a, a.b.c, a.b.c.d, a.c, a.c.d, b.c, b.c.d, c}, {b.d} >  (True in a.d)
      |(A \wedge B)|-alternatives to a.d = {b.c}
        |C| = < {d}, {a.b.c, a.c, b.c} >  (False in b.c)


========================================

---

========================================

EXAMPLE CF_CM_7: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premise:
1. (A \boxright B)

Conclusion:
2. (\neg B \boxright \neg A)

Z3 Run Time: 0.009 seconds

========================================

State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b
  #b0100 = c
  #b0101 = a.c
  #b0110 = b.c
  #b0111 = a.b.c (world)
  #b1000 = d
  #b1001 = a.d
  #b1010 = b.d
  #b1011 = a.b.d (world)
  #b1100 = c.d
  #b1101 = a.c.d (world)
  #b1110 = b.c.d (world)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: a.b.c

INTERPRETED PREMISE:

1.  |(A \boxright B)| = < {a.b.c}, {a.b.d, a.c.d, b.c.d} >  (True in a.b.c)
      |A| = < {a.b.c, a.c, b.c}, {a.b.d} >  (True in a.b.c)
      |A|-alternatives to a.b.c = {a.b.c}
        |B| = < {a.b.c}, {a.b.c.d, a.c.d, b.c.d, c.d, d} >  (True in a.b.c)

INTERPRETED CONCLUSION:

2.  |(\neg B \boxright \neg A)| = < {}, {a.b.c, a.b.d, a.c.d, b.c.d} >  (False in a.b.c)
      |\neg B| = < {a.b.c.d, a.c.d, b.c.d, c.d, d}, {a.b.c} >  (False in a.b.c)
        |B| = < {a.b.c}, {a.b.c.d, a.c.d, b.c.d, c.d, d} >  (True in a.b.c)
      |\neg B|-alternatives to a.b.c = {a.b.d, a.c.d, b.c.d}
        |\neg A| = < {a.b.d}, {a.b.c, a.c, b.c} >  (False in b.c.d)
          |A| = < {a.b.c, a.c, b.c}, {a.b.d} >  (True in b.c.d)
        |\neg A| = < {a.b.d}, {a.b.c, a.c, b.c} >  (False in a.c.d)
          |A| = < {a.b.c, a.c, b.c}, {a.b.d} >  (True in a.c.d)
        |\neg A| = < {a.b.d}, {a.b.c, a.c, b.c} >  (True in a.b.d)
          |A| = < {a.b.c, a.c, b.c}, {a.b.d} >  (False in a.b.d)


========================================

---

========================================

EXAMPLE CF_TH_5: there is no countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premise:
1. ((A \vee B) \boxright C)

Conclusion:
2. (A \boxright C)

Z3 Run Time: 0.0314 seconds

========================================

---

========================================

EXAMPLE CF_TH_10: there is no countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. A
2. B

Conclusion:
3. (A \diamondright B)

Z3 Run Time: 0.0159 seconds

========================================