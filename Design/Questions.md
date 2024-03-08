# Questions

Questions should be organized under a topic when possible.

## General

- What other tools are needed in addition to Z3, Python, and Git

## Input Parameters

- [ ] How should the user inputs be defined
  - [x] M: I think it may be easier to write up a semantics file and then make it pretty at the end (like make these variables easily accessible)
  - [x] B: That sounds good. I added some rough thoughts for what might go in that file in `Strategies.md`.

## Z3

### General

- [ ] Is it important to have bivectors with length not equal to a power of 2?
- [ ] It appears that even bound variables must be defined in Z3. Why is this?
- [ ] What is the BitVec class by itself good for?
- [x] What does sexpr() do?
  - [x] prints bitvector as a string of numbers if the length is not a power of 2
  - [x] if the bitvector has length with a power of 2, then it is in hexadecimal
  - [ ] is there a function that translates from hexadecimal to a string of numbers?
- Suppose Z3 finds that ${ A, B, C, ~D }$ is unsatisfiable.
  - How do we know how many models it tried and how big those models were?
  - Knowing this tells us about the strength of the evidence that ${ A, B, C }$ entails $D$.

### No Alternatives and Exhaustivity

Z3 finds a minimal countermodel for A, B \vdash A \boxright B by providing the following evaluation constraints:
```
    world(w),  # there is a world w

    is_part_of(s, w),  # s is a part of w
    verify(s, A),  # s verifies A

    is_part_of(t, w),  # t is part of w
    verify(t, B),  # t verifies B

    # CF CONSTRAINT      
    verify(y, A),
    is_alternative(u, y, w),
    Exists(b, And(is_part_of(b, u), falsify(b, B))),
```
This produces the output:
```
States:

#b000 = □ (possible)
#b001 = a (world)
#b010 = b (world)
#b011 = a.b (impossible)
#b100 = c (world)
#b101 = a.c (impossible)
#b110 = b.c (impossible)
#b111 = a.b.c (impossible)

Propositions:

|A| = < {'a', '□'}, ∅ >
A-alternatives to c = {'a'}

|B| = < {'c'}, {'a'} >
B-alternatives to c = ∅
```
By contrast, no A-alternatives worlds are found if the CF CONSTRAINT given above is replaced with the following:
```
    Exists([y,u],
        And(
          verify(y, A),
          is_alternative(u, y, w),
          Exists(b, And(is_part_of(b, u), falsify(b, B))),
        )
    )
```
I am not sure why this is. Additionally, consider the following alternative to the CF CONSTRAINT originally given:
```
    # CF ALT-CONSTRAINT      
    verify(y, A),
    is_alternative(u, y, w),
    ForAll(b, Implies(is_part_of(b, u), Not(verify(b, B)))),
```
These two constraints are equivalent modulo exhaustivity. Nevertheless, the CF ALT-CONSTRAINT above yields the following model:
```
States:

#b000 = □ (possible)
#b001 = a (world)
#b010 = b (world)
#b011 = a.b (impossible)

Propositions:

|A| = < {'b', '□'}, ∅ >
A-alternatives to a = {'b'}

|B| = < {'a'}, ∅ >
B-alternatives to a = ∅
```
This is an example of a truth-value gap: although `B` is not true in world `b`, there is no falsifier that is a part of `b` which makes `B` false, and so not true in `b`. This is OK since the simple model above still counts as a countermodel to the inference in question. Nevertheless, we may avoid these truth-value gaps by using CF CONSTRAINT instead which amounts to applying the exhaustivity condition by hand.

This suggests a different set of constraints for negated counterfactuals (as in this example) and true counterfactuals to get around the fact that exhaustivity has not been included.

### Interpretation

- what are the primitive types/sorts in Z3?
- _M_ seems that BitVecVal is a more useful type than BitVec.
  - It seems we'll need to initialize BitVec(Val)s as numbers (this adds another interesting meta-layer to the project, bc the states are effectively numbers, but we don't care about the facts they're numbers).
  - There seems to also be a difference betewen #b (prefix for binary bitvectors) and bvor types (prefix for or-constructions, put loosely).
  - I haven't been able to find where this is formalized in the documentation of Z3.
  - Also, you can only do | (or) on bitvectors of the same number of bits.
- can types/sorts be defined and what does this mean/entail?
  - _M_ How transparent do we want the model to be?
    - We can easily just make states bitvectors, but it'd be nice to actually vizualize states as bitvectors instead of seeing them as numbers (or the ugly format that Z3 .sexpr() gives)

### Optimization

- What size bitvector does it make sense to start with? M: not a power of 2 (those are represented in hexadecimal notation, for whatever reason). Based off our convo last Wednesday (2/12), 8 seems like a huge state space (and every other space) already, so maybe 5, 7, or 9? But I really don't know, defer to @B

## Python

- What do we want to do with Prefix notation? I have a version working with lists, but there's not much you can do with that (or, better said, we can turn it into something more powerful, functioning like a symbolic calculator, if need be).
- unfortunately the backslash character, as in Latex, is in Python a special character. I've made a infix-->prefix function that uses forward slashes. How much of a problem would that be?
