# Strategies

Notes related to overall design strategy for the model checker algorithm.
Sections are ordered chronologically from user inputs to the representation of the model output.

## Pre-Processing: preparing inputs for Z3

These sections cover the functions needed to construct Z3 constraints from the inputs.

### Overview: inputs, outputs, and modules

1. `user_inputs` is an executable file that contains:
  - `premises` and `conslutions`
  - bitvector length `N` for models
  - settings for `print_constraints` and `print_unsat_core`
  - `output` file name
2. `definitions` includes all basic definitions
3. `utils` contains all helper functions
4. `convert_syntax` includes all syntactic functions
5. `semantics` contains all semantic functions that generate Z3 constraints
6. `model` functions for building a data structure
7. `model_structure` classes for sentences, model, and propositions
  - finds sentences and constraints, runs solver, and stores all data including propositions
8. `print` contains functions that operate on a data structure to print
9. `test_complete` builds data structures from `user_input`, stores the result in an `output` file, and prints results

### Function: prefix conversion

1. Given a sentence `X` in infix notation (e.g., `(A \wedge B) \boxright C`), the function `Prefix(X)` will output a unique sentences in prefix notation using lists (e.g., `[Boxright, [Wedge, A, B]]`).
2. A single sentence letter `A` should return a list `[A]` so that all prefix sentences are lists.
3. Converting the sentences in `input_sentences` to a list `prefix_sentences` in prefix notation will streamline the application of the semantic clauses below in producing Z3 constraints.
4. To avoid further translation, LaTeX commands will be used for the operators `\neg`, `\wedge`, `\vee`, `\rightarrow`, and `\boxright`.

### Function: sentence letters

Given `prefix_sentences`, we will need a separate sorted list of the sentence letters that they contain.

1. Define the sorted list `sentence_letters` with no repeated entries.

### Function: simplification

Given `prefix_sentences` define a list `simple_sentences` which will simplify the generation of Z3 constraints.
The following can likely be extended and improved.

1. Conjunctions of the form `(A \wedge B)` in `prefix_sentences` will be stored as separate entries `A, B` in `simple_sentences`.
2. Negated conjunctions of the form `\neg(A \vee B)` in `prefix_sentences` will be stored as separate entries `\neg A, \neg B` in `simple_sentences`.
3. Negated conditionals of the form `\neg(A \rightarrow B)` in `prefix_sentences` will be stored as separate entries `A, \neg B` in `simple_sentences`.
4. Biconditionals of the form `(A \leftrightarrow B)` in `prefix_sentences` will be stored as separate entries `(A \rightarrow B), (B \rightarrow A)` in `simple_sentences`.

### Declarations

Given the number of atomic states `N` as input, we may make the following declarations:

1. Declare variables `x = BitVec("x", N)`, `y = BitVec("y", N)`, etc., as needed.
2. Declare sort for sentence letters `AtomSort = DeclareSort('AtomSort')`.
3. Declare constants for the sentence letters `A, B = Consts('A B', AtomSort)` that occur in `sentence_letters`.
4. Declare variables for sentence letters `X, Y = Vars('X Y', AtomSort)` of the sentence letter sort.
5. Declare `possible = Function("possible", BitVecSort(N), BoolSort())` as a property of states.
6. Declare `verify = Function("verify", BitVecSort(N), AtomSort(), BoolSort())` as a relation between states and sentence letters.
7. Declare `falsify = Function("falsify", BitVecSort(N), AtomSort(), BoolSort())` as a relation between states and sentence letters.

These declarations may occur in the same file in which the semantics and frame constraints are stored.

### Frame Definitions

Drawing on the declarations above and the operators already included in Z3 libraries, we may define the following:

1. `fusion(x,y)` returns a bitvector `z` where `z_i` is `max{x_i,y_i}` for each index `i` that is less than or equal to `N`.
2. `is_part_of(x,y)` returns a true iff `fusion(x,y) == y`.
3. `is_atomic(x)` returns a true iff `x_i == 1` for exactly one index `i` less than or equal to `N`.
4. `is_compatible(x,y)` returns true iff `possible(fusion(x,y))` is true.
5. `is_maximal(w)` returns a true iff for every `x`, if `compatible(x,w)`, then `is part_of(x,w)`.
6. `is_world(w)` returns a true iff `possible(w)` and `maximal(w)`.
7. `is_max_compatible_part(x,w,y)` returns true iff `is_part_of(x,w)`, `compatible(x,y)`, and for any `z`, if `is_part_of(z,w)`, `compatible(z,y)`, and `is_part_of(x,z)`, then `x == z`.
8. `is_alternative(u,y,w)` returns a true iff `world(u)`, `is_part_of(y,u)`, and there is some `x` where `is_part_of(x,u)` and `compatible_part(x,w,y)`.

Whereas every impossible state is maximal since nothing is compatible with it, a state that is both maximal and possible is a world state.
Given any world state `w` and state `y`, `compatible_part()` identifies when a state `x` is a biggest part of `w` that is compatible with `y`.
Given a world state `u` and state `x`, `alternative()` identifies when a world state `w` includes `x` and a biggest part of `u` that is compatible with `x`.

### Frame Constraints

The following constraints hold independent of the sentences being evaluated.

1. For every `x` and `y`, if `possible(y)` and `is_part_of(x,y)`, then `possible(x)`.
2. `is_world(w)` holds for the designated world `w`.

### Definition: propositions

Given a constant of `AtomSort`, we may define what it is for `X` to be a proposition.
In particular, `proposition(X)` holds iff:

1. For all `x`, and `y`, if `verify(x,X)` and `verify(y,X)`, then `verify(fusion(x,y),X)`.
2. For all `x`, and `y` if `falsify(x,X)` and `falsify(y,X)`, then `falsify(fusion(x,y,X))`.
3. For all `x`, and `y` if `verify(x,X)` and `falsify(y,X)`, then `Not(possible(fusion(x,y)))`.
4. For all `x`, if `possible(x)`, then there is some `y` where `possible(fusion(x,y))` and: `verify(y,X)` or `falsify(y,X)`.

NOTE: the last condition cannot easily be met by Z3, and so has been left absent.

### Model Constraints

Assuming the definition of `proposition(X)` has been provided and works for concrete cases, we may require:

1. `ForAll(X, proposition(X))` where `X` is of sort `AtomSort`.

Alternatively, `proposition(X)` may be required to hold for all `X` in `sentence_letters`.

### Functions: extensional constraints

For extensional sentences in prefix notation, the `extended_verify` and `extended_falsify` functions return recursively defined constraints:

1. If `X = [X]` where `X` is a sentence letter, then `extended_verify(x,X)` returns the constraint: `verify(x,X)`.
2. If `X = [X]` where `X` is a sentence letter, then `extended_falsify(x,X)` returns the constraint: `falsify(x,X)`.
3. If `X = [\neg Y]`, then `extended_verify(x,X)` returns the constraint: `extended_falsify(x,Y)`.
4. If `X = [\neg Y]`, then `extended_falsify(x,X)` returns the constraint: `extended_verify(x,Y)`.
5. If `X = [\wedge, Y, Z]`, then `extended_verify(x,X)` returns the constraint: `Exists` some `y` and `z` where `x = fusion(y,z)`, `extended_verify(y,Y)`, and `extended_verify(z,Z)`.
6. If `X = [\wedge, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: `extended_falsify(x,Y)`, `extended_falsify(x,Z)`, or `extended_falsify(x,[\vee, Y, Z])`.
7. If `X = [\vee, Y, Z]`, then `extended_verify(x,X)` returns the constraint: `extended_verify(x,Y)`, `extended_verify(x,Z)`, or `extended_verify(x,[\wedge, Y, Z])`.
8. If `X = [\vee, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: `Exists` some `y` and `z` where `x = fusion(y,z)`, `extended_falsify(y,Y)`, and `extended_falsify(z,Z)`.
9. If `X = [\rightarrow, Y, Z]`, then `extended_verify(x,X)` returns the constraint: `extended_falsify(x,Y)`, `extended_verify(x,Z)`, or `extended_verify(x,[\wedge, [\neg, Y], Z])`.
10. If `X = [\rightarrow, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: `Exists` some `y` and `z` where `x = fusion(y,z)`, `extended_verify(y,Y)`, and `extended_falsify(z,Z)`.
11. If `X = [\leftrightarrow, Y, Z]`, then `extended_verify(x,X)` returns the constraint: `extended_verify(x,[\wedge, Y, Z])` or `extended_falsify(x,[\vee, Y, Z])`.
12. If `X = [\leftrightarrow, Y, Z]`, then `extended_falsify(x,X)` returns the constraint: `extended_verify(x,[\wedge, Y, [\neg, Z]])` or `extended_falsify(x,[\vee, [\neg Y], Z])`.

Only extensional sentences including `\neg`, `\vee`, `\wedge`, `\rightarrow`, and `\leftrightarrow` may occur in the antecedent of a counterfactual, returning an error otherwise.
The functions `extended_verify(x,X)` and `extended_falsify(x,X)` return constraints which will be used to identify the states that exactly verify/falsify the antecedent of a counterfactual.

### Function: truth constraints

The truth or falsity of a sentence `X` at a designated world `w` may be defined recursively as follows:

1. If `X = [A]` where `A` is a sentence letter, then `true(w,X)` returns the constraint: there is some `x` where `is_part_of(x,w)` and `verify(x,A)`.
2. If `X = [A]` where `A` is a sentence letter, then `false(w,X)` returns the constraint: there is some `x` where `is_part_of(x,w)` and `falsify(x,A)`.
3. If `X = [\neg Y]`, then `true(w,X)` returns the constraint: `false(w,Y)`.
4. If `X = [\neg Y]`, then `false(w,X)` returns the constraint: `true(w,Y)`.
5. If `X = [\wedge, Y, Z]`, then `true(w,X)` returns the constraint: `And(true(w,Y), true(w,Z))`.
6. If `X = [\wedge, Y, Z]`, then `false(w,X)` returns the constraint: `Or(false(w,Y), false(w,Z))`.
7. If `X = [\vee, Y, Z]`, then `true(w,X)` returns the constraint: `Or(true(w,Y), true(w,Z))`.
8. If `X = [\vee, Y, Z]`, then `false(w,X)` returns the constraint: `And(false(w,Y), false(w,Z))`.
9. If `X = [\rightarrow, Y, Z]`, then `true(w,X)` returns the constraint: `Or(false(w,Y), true(w,Z))`.
10. If `X = [\rightarrow, Y, Z]`, then `false(w,X)` returns the constraint: `And(true(w,Y), false(w,Z))`.
11. If `X = [\leftrightarrow, Y, Z]`, then `true(w,X)` returns the constraint: `Or(And(true(w,Y), true(w,Z)), And(Not(true(w,Y)), Not(true(w,Z))))`.
12. If `X = [\leftrightarrow, Y, Z]`, then `false(w,X)` returns the constraint: `Or(And(true(w,Y), false(w,Z)), And(false(w,Y), true(w,Z)))`.
13. If `X = [\boxright, Y, Z]`, then `true(w,X)` returns the constraint: for all `x` and `u`, if `extended_verify(x,Y)` and `alternative(w,x,u)`, then `true(u,Z)`.
14. If `X = [\boxright, Y, Z]`, then `false(w,X)` returns the constraint: there is some `x` and `u` where `extended_verify(x,Y)` and `alternative(w,x,u)` and `false(u,Z)`.

### Function: evaluation constraints

We may now require the `simple_sentences` to be true at the designated world state `w`:

1. `true(w,prefix(X))` for all sentences `X` in `simple_sentences`.

## Post-Processing: representing Z3 models

These sections cover the functions needed to represent Z3 models.

### Function: frame representation

Z3 models are represented by assigning each state to a fusion of named atomic states.
Each state is labeled as either a world, possible, or impossible.

1. Assign lowercase letters to all atomic states that occur in the stored model.
2. Represent all states in the model as fusions of atomic states, e.g., `a.b.c` where `.` is used for fusion.
3. Label states as either worlds, possible, or impossible.

<!-- ### Function: sub-sentences -->
<!---->
<!-- Generate a set of all sub-sentences from the input sentences. -->
<!-- These sentences may then be interpreted by assigning them to propositions. -->
<!-- This will help to read each model. -->
<!---->
<!-- 1. Given any sentence in prefix form, we may store a list of all `sub_sentences` for that sentence. -->
<!-- 2. Store those `sub_sentences` that only include `\wedge`, `\vee`, `\not`, `\rightarrow`, and `\leftrightarrow` as a list of `extensional_sentences`. -->
<!-- 3. Store those counterfactual `sub_sentences` of the form `A \boxright B` in a list `counterfactual_sentences`. -->

<!-- ### Function: model representation -->
<!---->
<!-- 1. For each sentence `X` in `extensional_sentences`, represent a set of `extended_verifier` states for `X` and a set of `extended_falsifier` states for `X`. -->
<!-- 2. For each sentence `X \boxright Y` in `counterfactual_sentences`, represent all `alternative` states that result from imposing an `extended_verifier` for the `X` on `w`. -->
<!-- 3. For each world state `w`, represent which of the sentences in `sub_sentences` are true/false at that world state. -->

<!-- ### Convention: input file -->
<!---->
<!-- Define a convention for presenting the `input_sentences`, semantics, and frame constraints in an input file. -->
<!---->
<!-- 1. Definitions that will not be changed may be included in a definitions file. -->
<!-- 2. The `input_sentences`, semantics, and frame constraints should be presented in a standardized form. -->
<!-- 3. Documentation will be included here indicating how to tweak constraints. -->

## Processing: solving, storing, printing

This section outlines the overall structure of the algorithm.

### Data Class

Store classes that include all relevant information for: 
  1. Sentences:
    - `premises`
    - `conclusions`
    - `input_sentences`
    - `prefix_sentences`
    - `prefix_sub_sentences`
    - `infix_sub_sentences`
    - `sentence_letters`
    - `constraints`
  2. Model:
    - `z3_model`
    - `model_status`
    - `model_run_time`
    - `all_bits`
    - `poss_bits`
    - `world_bits`
    - `eval_world_bit`
  3. Propositions:
    - `props_dict` associates each `prefix_sub_sentences` with:  
      - `extensional(prefix_sub_sentences)` is a Boolean
      - `infix(prefix_sub_sentences)` for the purposes of printing
      - `proposition(prefix_sub_sentences)`
        - if `extensional(prefix_sub_sentences)` = true, then this is a `<V,F>`
        - else, this is a set of worlds where `prefix_sub_sentences` is true
    - `true_in_world_dict` associates each world `u` with the `prefix_sub_sentences` true in `u`
    - `alt_worlds_dict` associates the antecedent of any counterfactuals with the alternatives to the world of evaluation


### Algorithm: print

Define an algorithm which draws on the data class to print the model in a readable way if any.

- def `print_sort(A,w)`:
    - if `A` in `ext_sentences`:
      - print: `infix(A)` = `prop(A)` is `truth_value(A,w)` in `w`
    - else:
      - print: `infix(A)` is `truth_value(A,w)` in `w` because:
      - if `A` is `[\neg, [B]]`:
        - `print_sort(B,w)`
      - if `A` is `[\wedge, [B, C]]`:
        - `print_sort(B,w)`
        - `print_sort(B,w)`
      - if `A` is `[\vee, [B, C]]`:
        - `print_sort(B,w)`
        - `print_sort(B,w)`
      - if `A` is `[\rightarrow, [B, C]]`:
        - `print_sort(B,w)`
        - `print_sort(B,w)`
      - if `A` is `[\leftrightarrow, [B, C]]`:
        - `print_sort(B,w)`
        - `print_sort(B,w)`
      - if `A` is `[\boxright, [B, C]]` then:
        - assert `B` is in `ext_sentences`
        - `print_sort(B,w)`
        - print: `infix(B)`-alternatives to `w` = `alt_world(B,w)`
        - for `u` in `alt_world(B,w)`:
          - print atomic sentences that are true in `u`
          - print `print_sort(C,u)`
- def `print_all(prefix_input_sentences, w)`
  - for `A` in `prefix_input_sentences`:
    - `print_sort(A,w)`
