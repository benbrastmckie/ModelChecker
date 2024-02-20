# Questions

Questions should be organized under a topic when possible.

## General

- What other tools are needed in addition to Z3, Python, and Git

## Z3

General

- Suppose Z3 finds that ${ A, B, C, ~D }$ is unsatisfiable.
  - How do we know how many models it tried and how big those models were?
  - Knowing this tells us about the strength of the evidence that ${ A, B, C }$ entails $D$.

Interpretation

- what are the primitive types/sorts in Z3? M: seems that BitVecVal is a more useful type than BitVec. It seems we'll need to initialize BitVec(Val)s as numbers (this adds another interesting meta-layer to the project, bc the states are effectively numbers, but we don't care about the facts they're numbers). There seems to also be a difference betewen #b (prefix for binary bitvectors) and bvor types (prefix for or-constructions, put loosely). I haven't been able to find where this is formalized in the documentation of Z3. Also, you can only do | (or) on bitvectors of the same number of bits. 
- can types/sorts be defined and what does this mean/entail?

Optimization

- What size bitvector does it make sense to start with? M: not a power of 2 (those are represented in hexadecimal notation, for whatever reason). Based off our convo last Wednesday (2/12), 8 seems like a huge state space (and every other space) already, so maybe 5, 7, or 9? But I really don't know, defer to @B
