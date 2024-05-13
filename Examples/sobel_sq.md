```
There is a 3-model of:

Premises:
1. (A boxright X)
2. neg ((A wedge B) boxright X)
3. (((A wedge B) wedge C) boxright X)
4. neg ((((A wedge B) wedge C) wedge D) boxright X)
5. (((((A wedge B) wedge C) wedge D) wedge E) boxright X)
6. neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)
7. (((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)

Possible states:
  #b000 = □
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  #b100 = c
  #b101 = a.c (world)
  #b110 = b.c (world)

The evaluation world is a.c:
  A, B, D, E, F, X  (True in a.c)
  C, G  (False in a.c)

Interpreted premises:

1.  |(A boxright X)| = < {□}, ∅ >  (True in a.c)
    |A| = < {a, a.c, c}, ∅ >  (True in a.c)
    A-alternatives to a.c = {a.c}
      |X| = < {a.c}, {b} >  (True in a.c)

2.  |\neg ((A wedge B) boxright X)| = < {□}, ∅ >  (True in a.c)
    |((A wedge B) boxright X)| = < ∅, {□} >  (False in a.c)
      |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
        |A| = < {a, a.c, c}, ∅ >  (True in a.c)
        |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
      (A wedge B)-alternatives to a.c = {a.b, a.c, b.c}
        |X| = < {a.c}, {b} >  (False in a.b)
        |X| = < {a.c}, {b} >  (False in b.c)
        |X| = < {a.c}, {b} >  (True in a.c)

3.  |(((A wedge B) wedge C) boxright X)| = < {□}, ∅ >  (True in a.c)
    |((A wedge B) wedge C)| = < ∅, {b, b.c, c} >  (False in a.c)
      |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
        |A| = < {a, a.c, c}, ∅ >  (True in a.c)
        |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
      |C| = < ∅, {b, b.c, c} >  (False in a.c)
    ((A wedge B) wedge C)-alternatives to a.c = {}

4.  |\neg ((((A wedge B) wedge C) wedge D) boxright X)| = < ∅, {□} >  (False in a.c)
    |((((A wedge B) wedge C) wedge D) boxright X)| = < {□}, ∅ >  (True in a.c)
      |(((A wedge B) wedge C) wedge D)| = < ∅, {b, b.c, c} >  (False in a.c)
        |((A wedge B) wedge C)| = < ∅, {b, b.c, c} >  (False in a.c)
          |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
            |A| = < {a, a.c, c}, ∅ >  (True in a.c)
            |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
          |C| = < ∅, {b, b.c, c} >  (False in a.c)
        |D| = < {a.c, b, b.c, c}, ∅ >  (True in a.c)
      (((A wedge B) wedge C) wedge D)-alternatives to a.c = {}

5.  |(((((A wedge B) wedge C) wedge D) wedge E) boxright X)| = < {□}, ∅ >  (True in a.c)
    |((((A wedge B) wedge C) wedge D) wedge E)| = < ∅, {b, b.c, c} >  (False in a.c)
      |(((A wedge B) wedge C) wedge D)| = < ∅, {b, b.c, c} >  (False in a.c)
        |((A wedge B) wedge C)| = < ∅, {b, b.c, c} >  (False in a.c)
          |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
            |A| = < {a, a.c, c}, ∅ >  (True in a.c)
            |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
          |C| = < ∅, {b, b.c, c} >  (False in a.c)
        |D| = < {a.c, b, b.c, c}, ∅ >  (True in a.c)
      |E| = < {a.c}, {b} >  (True in a.c)
    ((((A wedge B) wedge C) wedge D) wedge E)-alternatives to a.c = {}

6.  |\neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)| = < ∅, {□} >  (False in a.c)
    |((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)| = < {□}, ∅ >  (True in a.c)
      |(((((A wedge B) wedge C) wedge D) wedge E) wedge F)| = < ∅, {b, b.c, c} >  (False in a.c)
        |((((A wedge B) wedge C) wedge D) wedge E)| = < ∅, {b, b.c, c} >  (False in a.c)
          |(((A wedge B) wedge C) wedge D)| = < ∅, {b, b.c, c} >  (False in a.c)
            |((A wedge B) wedge C)| = < ∅, {b, b.c, c} >  (False in a.c)
              |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
                |A| = < {a, a.c, c}, ∅ >  (True in a.c)
                |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
              |C| = < ∅, {b, b.c, c} >  (False in a.c)
            |D| = < {a.c, b, b.c, c}, ∅ >  (True in a.c)
          |E| = < {a.c}, {b} >  (True in a.c)
        |F| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
      (((((A wedge B) wedge C) wedge D) wedge E) wedge F)-alternatives to a.c = {}

7.  |(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)| = < {□}, ∅ >  (True in a.c)
    |((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)| = < ∅, {a, a.b, a.c, b, b.c, c} >  (False in a.c)
      |(((((A wedge B) wedge C) wedge D) wedge E) wedge F)| = < ∅, {b, b.c, c} >  (False in a.c)
        |((((A wedge B) wedge C) wedge D) wedge E)| = < ∅, {b, b.c, c} >  (False in a.c)
          |(((A wedge B) wedge C) wedge D)| = < ∅, {b, b.c, c} >  (False in a.c)
            |((A wedge B) wedge C)| = < ∅, {b, b.c, c} >  (False in a.c)
              |(A wedge B)| = < {a, a.b, a.c, b.c, c}, ∅ >  (True in a.c)
                |A| = < {a, a.c, c}, ∅ >  (True in a.c)
                |B| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
              |C| = < ∅, {b, b.c, c} >  (False in a.c)
            |D| = < {a.c, b, b.c, c}, ∅ >  (True in a.c)
          |E| = < {a.c}, {b} >  (True in a.c)
        |F| = < {a, a.b, a.c, b, b.c, c}, ∅ >  (True in a.c)
      |G| = < ∅, {a, a.c, b.c, c} >  (False in a.c)
    ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)-alternatives to a.c = {}

Run time: 327.2193 seconds
```
