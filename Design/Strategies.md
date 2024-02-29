# Strategies

Notes related to overall design strategy for the model checker algorithm.
Sections are ordered chronologically from user inputs to the representation of the model output.

## Pre-Processing: preparing inputs for Z3

These sections cover the functions needed to construct Z3 constraints from the inputs.

### Convention: input parameters

Variables to be specified by the user are to be included in a file with the following ingredients:

1. A value `N` for the maximum number of atomic states under consideration.
2. A list `input_sentences` of infix sentences to be evaluated.
3. Semantic clauses for each of the operators.
4. General model constraints.

### Function: prefix conversion

1. Given a sentence `X` in infix notation (e.g., `(A \wedge B) \boxright C`), the function `Prefix(X)` will output a unique sentences in prefix notation using lists (e.g., `[Boxright, [Wedge, A, B]]`).
2. A single sentence letter `A` should return a list `[A]` so that all prefix sentences are lists.
3. Converting the sentences in `input_sentences` to prefix notation will streamline the application of the semantic clauses below in producing Z3 constraints.
4. To avoid further translation, LaTeX commands will be used for the operators `\neg`, `\wedge`, `\vee`, `\rightarrow`, and `\boxright`.

### Function: sentence letters

Given a list of prefix sentences `input_sentences`, we will need a separate sorted list of the sentence letters that they contain.

1. Let the list of sentence letters be called `sentence_letters`.
2. There should not be any repeated entries in `sentence_letters`.
3. The list should be sorted.

### Declarations

Given the number of atomic states `N` as input, we may make the following declarations:

1. Declare variables `x = BitVec("x", N)`, `y = BitVec("y", N)`, etc., as needed.
2. Declare sort for sentence letters `AtomSort = DeclareSort('AtomSort')`.
3. Declare constants for the sentence letters `A, B = Consts('A B', AtomSort)` that occur in `sentence_letters`.
4. Declare variables for sentence letters `X, Y = Vars('X Y', AtomSort)` of the sentence letter sort.
5. Declare `possible = Function("possible", BitVecSort(N), BoolSort())` as a property of states.
6. Declare `verify = Function("verify", BitVecSort(N), AtomSort(), BoolSort())` as a relation between states and sentence letters.
7. Declare `falsify = Function("falsify", BitVecSort(N), AtomSort(), BoolSort())` as a relation between states and sentence letters.

### Frame Definitions

Drawing on the declarations above and the operators already included in Z3 libraries, we may define the following:

1. `fusion(x,y)` returns a bitvector `z` where `z_i` is `max{x_i,y_i}` for each index `i` that is less than or equal to `N`.
2. `is_part_of(x,y)` returns a true iff `fusion(x,y) == y`.
3. `is_atomic(x)` returns a true iff `x_i == 1` for exactly one index `i` less than or equal to `N`.
4. `compatible(x,y)` returns true iff `possible(fusion(x,y))` is true.
5. `maximal(w)` returns a true iff for every `x`, if `compatible(x,w)`, then `is part_of(x,w)`.
6. `is_world(w)` returns a true iff `possible(w)` and `maximal(w)`.
7. `compatible_part(x,w,y)` returns true iff `is_part_of(x,w)`, `compatible(x,y)`, and for any `z`, if `is_part_of(z,w)`, `compatible(z,y)`, and `is_part_of(x,z)`, then `x == z`.
8. `alternative(w,y,u)` returns a true iff `world(u)`, `is_part_of(y,u)`, and there is some `x` where `is_part_of(x,u)` and `compatible_part(x,w,y)`.

Whereas every impossible state is maximal since nothing is compatible with it, a state that is both maximal and possible is a world state.
Given any world state `w` and state `y`, `compatible_part()` identifies when a state `x` is a biggest part of `w` that is compatible with `y`.
Given a world state `u` and state `x`, `alternative()` identifies when a world state `w` includes `x` and a biggest part of `u` that is compatible with `x`.

### Frame Constraints

The following constraints hold independent of the sentences being evaluated.

1. For every `x` and `y`, if `possible(y)` and `is_part_of(x,y)`, then `possible(x)`.
2. For every `x`, if `possible(x)`, then there is some `y` where `world(y)` and `is_part_of(x,w)`.

### Model Constraints

Assuming it is possible to take `X` to be a bound variable of `AtomSort`, we may include the following constraints:

1. For all `x`, `y`, `X`, if `verify(x,X)` and `verify(y,X)`, then `verify(fusion(x,y),X)`.
2. For all `x`, `y`, `X`, if `falsify(x,X)` and `falsify(y,X)`, then `falsify(fusion(x,y,X))`.
3. For all `x`, `y`, `X`, if `verify(x,X)` and `falsify(y,X)`, then `Not(possible(fusion(x,y)))`.
4. For all `x` and `X`, if `possible(x)`, then there is some `y` where `possible(fusion(x,y))` and: `verify(y,X)` or `falsify(y,X)`.

The constraints above require `X` to be a proposition by requiring `Verify` and `Falsify` to be: (1-2) closed under fusion; (3) exclusive; and (4) exhaustive.
These constraints set limits on what verification and falsification relations can hold.
If it is not possible to take `X` to be a bound variable as above, then copies of the following constraints could be included for each `X` in `sentence_letters`:

1. For all `x`, `y`, if `verify(x,X)` and `verify(y,X)`, then `verify(fusion(x,y),X)`.
2. For all `x` and `y`, if `falsify(x,X)` and `falsify(y,X)`, then `falsify(fusion(x,y,X))`.
3. For all `x` and `y`, if `verify(x,X)` and `falsify(y,X)`, then `Not(possible(fusion(x,y)))`.
4. For all `x`, if `possible(x)`, then there is some `y` where `possible(fusion(x,y))` and: `verify(y,X)` or `falsify(y,X)`.

If the latter strategy is required, then it may be worth defining a function `proposition(X)` which outputs the constraints above for any `X`.

### Functions: extensional constraints

For extensional sentences in prefix notation, the `extended_verify` and `extended_falsify` functions return recursively defined constraints:

1. If `X = [X]` where `X` is a sentence letter, then `extended_verify(x,X)` returns the constraint: `verify(x,X)`.
2. If `X = [X]` where `X` is a sentence letter, then `extended_falsify(x,X)` returns the constraint: `falsify(x,X)`.
3. If `X = [\neg Y]`, then `extended_verify(x,X)` returns the constraint: `extended_falsify(x,Y)`.
4. If `X = [\neg Y]`, then `extended_falsify(x,X)` returns the constraint: `extended_verify(x,Y)`.
5. If `X = [\wedge, Y, Z]`, then `extended_verify(x,X)` returns the constraint: there is some `y` and `z` where `x = fusion(y,z)`, `extended_verify(y,Y)`, and `extended_verify(z,Z)`.
6. If `X = [\wedge, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: `extended_falsify(x,Y)`, `extended_falsify(x,Z)`, or `extended_falsify(x,[\vee, Y, Z])`.
7. If `X = [\vee, Y, Z]`, then `extended_verify(x,X)` returns the constraint: `extended_verify(x,Y)`, `extended_verify(x,Z)`, or `extended_verify(x,[\wedge, Y, Z])`.
8. If `X = [\vee, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: there is some `y` and `z` where `x = fusion(y,z)`, `extended_falsify(y,Y)`, and `extended_falsify(z,Z)`.
9. If `X = [\rightarrow, Y, Z]`, `X = [\leftrightarrow, Y, Z]`, or `X = [\boxright, Y, Z]`, then return error message.

Only extensional sentences including `\neg`, `\vee`, `\wedge` may occur in the antecedent of a counterfactual, returning an error otherwise.
The functions `extended_verify(x,X)` and `extended_falsify(x,X)` return constraints which will be used to identify the states that exactly verify/falsify the antecedent of a counterfactual.

### Function: truth constraints

The truth of a sentence `X` at a designated world `w` may be defined recursively as follows:

1. If `X = [A]` where `A` is a sentence letter, then `true(w,X)` returns the constraint: there is some `x` where `is_part_of(x,w)` and `verify(x,A)`.
2. If `X = [\neg Y]`, then `true(w,X)` returns the constraint: `Not(true(w,Y))`.
3. If `X = [\wedge, Y, Z]`, then `true(w,X)` returns the constraint: `And(true(w,Y), true(w,Z))`.
4. If `X = [\vee, Y, Z]`, then `true(w,X)` returns the constraint: `Or(true(w,Y), true(w,Z))`.
5. If `X = [\rightarrow, Y, Z]`, then `true(w,X)` returns the constraint: `Or(Not(true(w,Y)), true(w,Z))`.
6. If `X = [\leftrightarrow, Y, Z]`, then `true(w,X)` returns the constraint: `Or(And(true(w,Y), true(w,Z)), And(Not(true(w,Y)), Not(true(w,Z))))`.
7. If `X = [\boxright, Y, Z]`, then `true(w,X)` returns the constraint: for all `x` and `u`, if `extended_verify(x,Y)` and `alternative(w,x,u)`, then `true(u,Z)`.

### Function: evaluation constraints

For every `X` in `input_sentences`, we may require the following to be true at the designated world state `w`:

1. There is some `w` where `world(w)` and `true(w,prefix(X))`.

## Processing: finding models with Z3

Define a Z3 solver and add the frame constraints, model constraints, and evaluation constraints corresponding to the `input_sentences`.
If the solver is satisfiable, store and print the model.
It remains to represent this model in a readable manner, storing the output in an associated file.

TODO: CONTINUE

### Model Builder

Represent Z3 models in a way that is easy to interpret.

Models will specify some number of states, saying which sentence letters are verified or falsified by each, and which states are possible.
Given this information, it is possible to construct a representation, complete with world states, which assigns each sentence letter to a proposition, i.e, to an ordered pair of sets of states.

**Example:** 
Say Z3 returns a model consisting of a bunch of bitvectors etc. Say `c = b#10001`.
Having it written out this way is better than some kind of hex code, but it is still not that salient what is going on.
But here we can see that `c` is the fusion of two atomic states, call them `a = b#00001` and `b = b#10000`.
So a better representation would look like `c = a.b`.
Honestly it doesn't matter that, thought of as numbers, `a < b`.
All we care about is that they are both atomic and that `c` is their fusion.

Given that there is a nice way to identify which states are atomic, it actually doesn't matter whether states are represented in hexadecimal or not since either way it would be nice to represent them in some cleaner way. Maybe you have thoughts about how to do this, but here is a rough idea:

- given some number of states as inputs (these are outputs of the Z3 model), find all atomic states.
- name all input and atomic states in some nice way (more thoughts in `Strategies`).
- then identify each input state with a fusion of atomic states using their new names.

There will probably be some other natural pieces to add, but getting these identities is a good start.
The thought is that eventually, the model representation could include things like `|A| = < { a, b, a.b}, {f.g} >` for each sentence letter which would make it clear what proposition each sentence letter is being assigned to.
Knowing what the fusion relations are and getting nice conventions for naming states will be a key step.

1. The python representation of a Z3 model should specify the states, possible states, worlds, and the propositions assigned to the sentence letters in question where further visualization can be added later.
2. A function should specify the propositions assigned to all subsentences of the sentences under evaluation.
3. These details may then be stored in an output file, prompting the user whether to search for another model to add to the file.

