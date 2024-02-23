# Questions

Questions should be organized under a topic when possible.

## General

- What other tools are needed in addition to Z3, Python, and Git

## Input Parameters

- [ ] How should the user inputs be defined
  - M: I think it may be easier to write up a semantics file and then make it pretty at the end (like make these variables easily accessible)
  - B: That sounds good! I added some rough thoughts for what might go in that file in `Strategies.md`.

## Z3

General

- [ ] What is the BitVec class by itself good for?
- [:] What does sexpr() do?
  - [x] prints bitvector as a string of numbers if the length is not a power of 2
  - [x] if the bitvector has length with a power of 2, then it is in hexadecimal
  - [ ] is there a function that translates from hexadecimal to a string of numbers?
- Suppose Z3 finds that ${ A, B, C, ~D }$ is unsatisfiable.
  - How do we know how many models it tried and how big those models were?
  - Knowing this tells us about the strength of the evidence that ${ A, B, C }$ entails $D$.

Interpretation

- what are the primitive types/sorts in Z3?
- _M_ seems that BitVecVal is a more useful type than BitVec.
  - It seems we'll need to initialize BitVec(Val)s as numbers (this adds another interesting meta-layer to the project, bc the states are effectively numbers, but we don't care about the facts they're numbers).
  - There seems to also be a difference betewen #b (prefix for binary bitvectors) and bvor types (prefix for or-constructions, put loosely).
  - I haven't been able to find where this is formalized in the documentation of Z3.
  - Also, you can only do | (or) on bitvectors of the same number of bits.
- can types/sorts be defined and what does this mean/entail?
  - _M_ How transparent do we want the model to be?
    - We can easily just make states bitvectors, but it'd be nice to actually vizualize states as bitvectors instead of seeing them as numbers (or the ugly format that Z3 .sexpr() gives)

Optimization

- What size bitvector does it make sense to start with? M: not a power of 2 (those are represented in hexadecimal notation, for whatever reason). Based off our convo last Wednesday (2/12), 8 seems like a huge state space (and every other space) already, so maybe 5, 7, or 9? But I really don't know, defer to @B

## Python

- What do we want to do with Prefix notation? I have a version working with lists, but there's not much you can do with that (or, better said, we can turn it into something more powerful, functioning like a symbolic calculator, if need be).
- unfortunately the backslash character, as in Latex, is in Python a special character. I've made a infix-->prefix function that uses forward slashes. How much of a problem would that be?
