
There is a 3-model of:

\neg A
(A \boxright (B \vee C))
\neg (A \boxright B)
\neg (A \boxright C)

States:
  #b000 = □ (possible)
  #b001 = a (world)
  #b010 = b (world)
  #b100 = c (world)

The evaluation world is a:
  A, B, C  (not true in a)

  |\neg A| = < {a}, {b, c} >
  \neg A-alternatives to a = {a}
    \neg A is true in a
    (B \vee C), A, B, C are not true in a

  |A| = < {b, c}, {a} >
  A-alternatives to a = {b, c}
    A, B are true in b
    (B \vee C), C, \neg A are not true in b
    A, C are true in c
    (B \vee C), B, \neg A are not true in c

  |(B \vee C)| = < ∅, {a, b, c} >
  There are no (B \vee C)-alternatives to a

  |B| = < {b}, {c} >
  B-alternatives to a = {b}
    A, B are true in b
    (B \vee C), C, \neg A are not true in b

  |C| = < {c}, {a, b} >
  C-alternatives to a = {c}
    A, C are true in c
    (B \vee C), B, \neg A are not true in c

