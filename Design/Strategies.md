# Strategies

Notes related to design problems and strategies.
Sections are ordered chronologically with respect to the total algorithm, i.e., from inputs to outputs.

## Pre-Processing: preparing inputs for Z3

These sections cover the functions needed to construct Z3 constraints from the inputs.

### Convention: input parameters

Variables to be specified by the user are to be included in a file with the following ingredients:

1. A value `N` for the maximum number of atomic states under consideration.
2. A list `input_sentences` of infix sentences to be evaluated.
3. Semantic clauses for each of the operators.
4. General model constraints.

### Function: prefix conversion

**Purpose:** In order to streamline the production of Z3 constraints corresponding to complex sentences, it will be convenient to have sentences represented in prefix form, e.g., `[Wedge, A, B]` and `[A]`, where the latter is a sentence letter.

- Given any prefix sentence, it is easy to check if it is a sentence letter by considering its length.
- A sentence letter will return constraints provided by the semantics which requires that sentence to express a proposition and to be true in the world of evaluation `w` where all sentences are being evaluated.
- Given a complex prefix sentence, it is easy to see which recursive clause of the semantics to use:
  - If the first entry is `Wedge`, then return the conjunction of the constraints for the following entries in the list.
  - If the first entry is `Vee`, then return the disjunction of the constraints for the following two arguments, etc.

**Description:** Translation function that converts from infix to prefix notation.

1. To avoid further translation, LaTeX commands are used for the operators though the slashes must be doubled `\\neg`, `\\wedge`, `\\vee`, `\\rightarrow`, `\\Box`, and `\\boxarrow`.
2. Given a sentence `X` in infix notation (e.g., `(A \\wedge B) \\boxright C`), the `Prefix(A)` function will output a unique sentences in prefix notation using lists (e.g., `[Boxright, [Wedge, A, B]]`).
3. A single sentence letter `A` should return a list `[A]` so that all prefix sentences are lists.
4. Although it is convenient to use LaTeX commands (or something near enough) as inputs, it does not matter what the output operators are, though it would simplify things if they were similar.
5. If it is easier, slashes could be dropped for the just the output, or for both the input and output.

### Function: model constraints

Given the prefix sentences from the inputs, we will need to know what sentence letters they contain.
These sentence letters will then be used to generate Z3 constraints which require each sentence letter to be assigned to a proposition where it is up to Z3 to satisfy all of these constraints.

- For any prefix sentence `X`, the function `sentence_letters(X)` returns a set of the sentence letters in contains.
- Let `Atoms` include all sentence letters in `sentence_letters(X)` for all `X` in `input_sentences`.
- Given any `X` in `Atoms`, the function `proposition(X)` yields the following Z3 constraints as outputs:

1. If `Verify(x,X)` or `Falsify(x,X)`, then `State(x)`.
2. If `Verify(x,X)` and `Verify(y,X)`, then `Verify(fusion(x,y),X)`.
3. If `Falsify(x,X)` and `Falsify(y,X)`, then `Falsify(fusion(x,y,X))`.
4. If `Verify(x,X)` and `Falsify(y,X)`, then not `Possible(fusion(x,y))`.
5. If `Possible(x)`, then `Possible(fusion(x,y))` where either `Verify(y,X)` or `Falsify(y,X)`.

The predicates `Verify`, `Falsify`, and `Possible`
The constraints above require `Verify` and `Falsify` to: (1) only relate states to `X`; (2/3) to be closed under fusion; (4) to be exclusive; and (5) to be exhaustive.
See the `Overview.pdf` for these constraints.

### Function: evaluation constraints

TODO: continue...

1. `Possible(w)`.
2. If `Possible(x)` and `Possible(fusion(x,w))`, then `fusion(x,w) = w`.
3. For each sentence `X` in `Gamma`, include the output of `Semantics(w,Prefix(X))`.

Whereas (1) assigns sentence letters to a propositions, (2) requires `w` to be a world, and (3) requires each sentence included in `Gamma` to be true at `w`.

### Frame Constraints

The following constraints only depend on `N` where `x`

1. If `State(x)`, then `BitVec(x,N)` i.e., 'x is a bitvector of length N'.
2. s.add( for all x if state(x), then x is a bitVec(x) )
3. If `State(x)` and `State(y)`, then `State(fusion(x,y))`.
4. If `Possible(x)`, then `State(x)`.
5. If `Possible(x)`, `State(y)`, and `fusion(x,y) = x`, then `Possible(y)`.

## Processing: finding models with Z3

Z3 looks for models that satisfy a set of specified constraints.

1. Input parameters determine constraints on frames, models, and worlds.
2. The semantics for the language will impose a number of further constraints.
3. Each sentence of the language being interpreted will determine an additional constraint on models and worlds.
4. Z3 models that satisfy the general constraints and sentence constraints may then be stored in an output file.

### Glossary

These definitions indicate the intended meanings of the elements employed below.

1. `State(x)` includes the predicate `State` whose extension is to be determined by Z3 given the constraints below.
2. `fusion(x,y)` indicates the bitwise operation which takes the greatest value for each index of the bit vectors `x` and `y`.
3. `Possible(x)` includes the predicate `Possible` whose extension is to be determined by Z3 given the constraints below.
4. `Proposition(X)` is a set of Z3 constraints that require `X` to be a proposition.
5. `Semantics(w,X)` is a set of Z3 constraints that require `X` to be true in `w`.
6. `Alternative(u,w,X)` is a set of constraints that require `u` to be a (perhaps non-unique) result of minimally changing `w` to include a verifier for `X`.
7. `Prefix(X)` and `Infix(X)` will translate between prefix and infix notations.

### World Alternatives

Given a world `w` and sentence `X`, the function `Alternatives(u,w,X)` yields the following Z3 constraints:

1. `State(x)` where `Verify(x,X)` and `fusion(x,u) = u`.
2. `State(y)` where `fusion(y,w) = w` and `fusion(y,u) = u`.
3. If `State(z)`, `fusion(z,w) = w`, `Possible(fusion(x,z))`, and `fusion(y,z) = z`, then `y = z`.

### Semantic Constraints

The function `Semantics(w,X)` may be defined recursively as follows:

1. If `X` is in `Atoms`, then `Semantics(w,X)` is: `Verify(x,X)` and `fusion(x,w)=w`.
2. If `X = [\neg,Y]`, then `Semantics(w,X)` is: not `Semantics(w,Y)`.
3. If `X = [\wedge,Y,Z]`, then `Semantics(w,X)` is: `Semantics(w,Y)` and `Semantics(w,Z)`.
4. If `X = [\vee,Y,Z]`, then `Semantics(w,X)` is: `Semantics(w,Y)` or `Semantics(w,Z)`.
<!-- 5. If `X = [\rightarrow,Y,Z]`, then `Semantics(w,X)` is: not `Semantics(w,Y)` or `Semantics(w,Z)`. -->
5. If `X = [\Box,Y]` and neither `\Box` nor `\boxright` occur in `Y`, then `Semantics(w,X)` is: `Semantics(u,Y)` whenever `World(u)`.
6. If `X = [\boxright,Y,Z]` and neither `\Box` nor `\boxright` occur in `Y`, then `Semantics(w,X)` is: `Semantics(u,Z)` whenever `Alternative(u,w,Y)` and `World(u)`.

### Model Builder

Represent Z3 models in a way that is easy to interpret.

Models will specify some number of states, saying which sentence letters are verified or falsified by each, and which states are possible.
Given this information, it is possible to construct a representation, complete with world states, which assigns each sentence letter to a proposition, i.e, to an ordered pair of sets of states.

**Example:** Say Z3 returns a model consisting of a bunch of bitvectors etc. Say `c = b#10001`. Having it written out this way is better than some kind of hex code, but it is still not that salient what is going on. But here we can see that `c` is the fusion of two atomic states, call them `a = b#00001` and `b = b#10000`. So a better representation would look like `c = a.b`. Honestly it doesn't matter that, thought of as numbers, `a < b`. All we care about is that they are both atomic and that `c` is their fusion.

Given that there is a nice way to identify which states are atomic, it actually doesn't matter whether states are represented in hexadecimal or not since either way it would be nice to represent them in some cleaner way. Maybe you have thoughts about how to do this, but here is a rough idea:

- given some number of states as inputs (these are outputs of the Z3 model), find all atomic states.
- name all input and atomic states in some nice way (more thoughts in `Strategies`).
- then identify each input state with a fusion of atomic states using their new names.

There will probably be some other natural pieces to add, but getting these identities is a good start. The thought is that eventually, the model representation could include things like `|A| = < { a, b, a.b}, {f.g} >` for each sentence letter which would make it clear what proposition each sentence letter is being assigned to. Knowing what the fusion relations are and getting nice conventions for naming states will be a key step.

1. The python representation of a Z3 model should specify the states, possible states, worlds, and the propositions assigned to the sentence letters in question where further visualization can be added later.
2. A function should specify the propositions assigned to all subsentences of the sentences under evaluation.
3. These details may then be stored in an output file, prompting the user whether to search for another model to add to the file.

FROM ABOVE

These conditions may be extended to complex sentences by way of the following general constraints:

1. If `Verify(z,[\neg, X])`, then `Falsify(z,X)`.
2. If `Falsify(z,[\neg, X])`, then `Verify(z,X)`.
3. If `Verify(z,[\wedge, X,Y])`, then `z = fusion(x,y)` where `Verify(x,X)` and `Verify(y,Y)`.
4. If `Falsify(z,[\wedge, X,Y])`, then `Falsify(z,X)` or `Falsify(z,Y)` (or both).
5. If `Verify(z,[\vee, X,Y])`, then `Verify(z,X)` or `Verify(z,Y)` (or both).
6. If `Falsify(z,[\vee, X,Y])`, then `z  =  fusion(x,y)` where `Falsify(x,X)` and `Falsify(y,Y)`.
7. If `Verify(z,[\rightarrow, X,Y])`, then `Falsify(z,X)` or `Verify(z,Y)` (or both).
8. If `Falsify(z,[\rightarrow, X,Y])`, then `z  =  fusion(x,y)` where `Verify(x,X)` and `Falsify(y,Y)`.
