There is a 3-model of:

Premises:
1. A
2. (A \boxright B)

Conclusion:
3. (\neg B \wedge \neg D)

State Space:
  #b000 = □
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  #b100 = c
  #b101 = a.c (world)
  #b110 = b.c (world)
  #b111 = a.b.c (impossible)

The evaluation world is: a.c

INTERPRETED PREMISES:

1.  |A| = < {a, a.b, a.b.c, a.c, b, b.c, c}, ∅ >  (True in a.c)

2.  |(A \boxright B)| = < {□}, ∅ >  (True in a.c)
    |A| = < {a, a.b, a.b.c, a.c, b, b.c, c}, ∅ >  (True in a.c)
    |B| = < {a, a.b, a.b.c, a.c, b, b.c, c}, ∅ >  (True in a.c)

INTERPRETED CONCLUSION:

3.  |(\neg B \wedge \neg D)| = < ∅, {a, a.b, a.b.c, a.c, b, b.c, c} >  (False 
in a.c)
    |\neg B| = < ∅, {a, a.b, a.b.c, a.c, b, b.c, c} >  (False in a.c)
      |B| = < {a, a.b, a.b.c, a.c, b, b.c, c}, ∅ >  (True in a.c)
    |\neg D| = < ∅, {a, a.b, a.b.c, a.c, b, b.c, c} >  (False in a.c)
      |D| = < {a, a.b, a.b.c, a.c, b, b.c, c}, ∅ >  (True in a.c)

all worlds: {'a.c', 'b.c', 'a.b'}
A's verifiers: {'a', 'b.c', 'a.b', 'b', 'a.c', 'c', 'a.b.c'}
is b.c an a-alternative to the main world a.c?
False

is a.b an a-alternative to the main world a.c?
And(Extract(2, 2, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(Extract(2, 1, alt_z) == 3),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4),
    Or(Not(Extract(1, 1, alt_z) == 0), alt_z == 5))

is a.c an a-alternative to the main world a.c?
And(Extract(1, 1, alt_z) == 0,
    Not(Extract(2, 1, alt_z) == 3),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4),
    Or(Not(Extract(1, 1, alt_z) == 0), alt_z == 5))

is b.c an a.b.c-alternative to the main world a.c?
False

is a.b an a.b.c-alternative to the main world a.c?
False

is a.c an a.b.c-alternative to the main world a.c?
False

is b.c an c-alternative to the main world a.c?
And(Extract(0, 0, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(Extract(1, 0, alt_z) == 3),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4),
    Or(Not(Extract(1, 1, alt_z) == 0), alt_z == 5))

is a.b an c-alternative to the main world a.c?
False

is a.c an c-alternative to the main world a.c?
And(Extract(1, 1, alt_z) == 0,
    Not(Extract(1, 0, alt_z) == 3),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4),
    Or(Not(Extract(1, 1, alt_z) == 0), alt_z == 5))

is b.c an b.c-alternative to the main world a.c?
And(Extract(0, 0, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(Extract(0, 0, alt_z) == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4))

is a.b an b.c-alternative to the main world a.c?
False

is a.c an b.c-alternative to the main world a.c?
False

is b.c an a.b-alternative to the main world a.c?
False

is a.b an a.b-alternative to the main world a.c?
And(Extract(2, 2, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(Extract(2, 2, alt_z) == 1),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1))

is a.c an a.b-alternative to the main world a.c?
False

is b.c an b-alternative to the main world a.c?
And(Extract(0, 0, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(And(Extract(0, 0, alt_z) == 1,
            Extract(2, 2, alt_z) == 1)),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4))

is a.b an b-alternative to the main world a.c?
And(Extract(2, 2, alt_z) == 0,
    Extract(1, 1, alt_z) == 0,
    Not(And(Extract(0, 0, alt_z) == 1,
            Extract(2, 2, alt_z) == 1)),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4))

is a.c an b-alternative to the main world a.c?
False

is b.c an a.c-alternative to the main world a.c?
False

is a.b an a.c-alternative to the main world a.c?
False

is a.c an a.c-alternative to the main world a.c?
And(Extract(1, 1, alt_z) == 0,
    Not(Extract(1, 1, alt_z) == 1),
    Or(Not(Extract(2, 1, alt_z) == 0), alt_z == 1),
    Or(Not(Extract(1, 0, alt_z) == 0), alt_z == 4),
    Or(Not(Extract(1, 1, alt_z) == 0), alt_z == 5))
