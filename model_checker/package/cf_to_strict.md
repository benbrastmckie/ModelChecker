
There is a 3-model of:

1. (A \boxright B)
2. \neg \Box (A \rightarrow B)

Possible states:
  #b000 = □
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  #b100 = c
  #b101 = a.c (world)

The evaluation world is a.c:
  A, B  (True in a.c)

1.  (A \boxright B)  (True in a.c)
    |A| = < {a, a.c, c}, ∅ >  (True in a.c)
    A-alternatives to a.c = {a.c}
      |B| = < {a.c, c}, {a.b, b} >  (True in a.c)

2.  \neg \Box (A \rightarrow B)  (True in a.c)
    \Box (A \rightarrow B)  (False in a.c)
      (A \rightarrow B)  (True in a.c)
        |A| = < {a, a.c, c}, ∅ >  (True in a.c)
        |B| = < {a.c, c}, {a.b, b} >  (True in a.c)

Run time: 1179.5815 seconds

