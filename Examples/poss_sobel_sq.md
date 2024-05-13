```
There is a 4-model of:

Premises:
1. Diamond A
2. (A boxright X)
3. Diamond (A wedge B)
4. neg ((A wedge B) boxright X)

Possible states:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (world)
  #b0110 = b.c (world)
  #b1000 = d (world)

The evaluation world is b.c:
  A, B, X  (True in b.c)

Interpreted premises:

1.  |\Diamond A| = < {□}, ∅ >  (True in b.c)
    |A| = < {b, b.c, c, d}, ∅ >  (True in a.b)
    |A| = < {b, b.c, c, d}, ∅ >  (True in a.c)
    |A| = < {b, b.c, c, d}, ∅ >  (True in b.c)
    |A| = < {b, b.c, c, d}, ∅ >  (True in d)

2.  |(A boxright X)| = < {□}, ∅ >  (True in b.c)
    |A| = < {b, b.c, c, d}, ∅ >  (True in b.c)
    A-alternatives to b.c = {b.c, d}
      |X| = < {b.c, d}, {a, a.b} >  (True in b.c)
      |X| = < {b.c, d}, {a, a.b} >  (True in d)

3.  |\Diamond (A wedge B)| = < {□}, ∅ >  (True in b.c)
    |(A wedge B)| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in a.b)
      |A| = < {b, b.c, c, d}, ∅ >  (True in a.b)
      |B| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in a.b)
    |(A wedge B)| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in a.c)
      |A| = < {b, b.c, c, d}, ∅ >  (True in a.c)
      |B| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in a.c)
    |(A wedge B)| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in b.c)
      |A| = < {b, b.c, c, d}, ∅ >  (True in b.c)
      |B| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in b.c)
    |(A wedge B)| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in d)
      |A| = < {b, b.c, c, d}, ∅ >  (True in d)
      |B| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in d)

4.  |\neg ((A wedge B) boxright X)| = < {□}, ∅ >  (True in b.c)
    |((A wedge B) boxright X)| = < ∅, {□} >  (False in b.c)
      |(A wedge B)| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in b.c)
        |A| = < {b, b.c, c, d}, ∅ >  (True in b.c)
        |B| = < {a.b, a.c, b, b.c, c, d}, ∅ >  (True in b.c)
      (A wedge B)-alternatives to b.c = {a.b, a.c, b.c, d}
        |X| = < {b.c, d}, {a, a.b} >  (True in b.c)
        |X| = < {b.c, d}, {a, a.b} >  (True in d)
        |X| = < {b.c, d}, {a, a.b} >  (False in a.b)
        |X| = < {b.c, d}, {a, a.b} >  (False in a.c)

Run time: 157.7993 seconds
```
