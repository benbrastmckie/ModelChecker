# Class Semantics

<!-- describe object oriented approach to defining compositional semantic clauses in Z3 -->

## Overview

The _functional syntax_ translates sentences in infix form into sentence in prefix form by recursively applying syntactic functions.
The _functional semantics_ translates prefix sentences into sets of Z3 constraints by recursively applying semantic functions.
The _functional representation_ draws on a Z3 model in order to represent the propositions expressed by the premises and conclusions by recursively applying the print functions.
Since the syntactic, semantic, and print functions all include conditions for every primitive of the language, adding new primitives to the language requires adding new clauses to each of these functions.

By contrast, the _class semantics_ aims to define a class for each primitive of the language which includes methods for processing the syntax, semantics, and printing representations.
Here is the imagined procedure for finding and printing models for extensional sentences:
  - Let `premises = ['((A \vee B) \wedge \neg C)']` and `conclusions = []`.
  - These values are stored as attributes in a `model_setup` class.
  - A function will then identify the main connective `\wedge`, looking up the syntactic method for that operator...
    - NOTE: is it possible to translate into prefix form without appealing to the primitive operators included in the language?
    - If so, we could run that translation immediately.
  - Once the `premises` have been converted to prefix form, the result is stored in the `model_setup` class as `prefix_premises`.
  - Similar for the `conclusions` which we have taken to be empty for simplicity here.
  - The sentence letters that occur in the `premises` and `conclusions` are also stored in the `model_setup` under `sentence_letters`.
  - The premise is then converted to a Z3 constraint by requiring the premise `[\wedge, [\vee, A, B], [\neg, C]]` to be true in the `main_world`.
    - Since `\wedge` is the main connective in `[\wedge, [\vee, A, B], [\neg, C]]`, we look up the `true_at` semantic method for `\wedge`.
    - The `true_at` semantic method for `\wedge` returns a Z3 constraint which takes the conjunction of the result of applying the `true_at` semantic method to `[\vee, A, B]` and `[\neg, C]` for the `main_world`.
    - The `true_at` semantic method for `\vee` returns a Z3 constraint which takes the disjunction of the result of applying the `true_at` semantic method to `A` and `B` for the `main_world`.
    - The `true_at` semantic method for `\neg` returns a Z3 constraint which is the result of applying the `false_at` semantic method to `C` for the `main_world`.
    - Since `A`, `B`, and `C` are sentence letters, we get the following results:
      - `true_at(A, main_world)` introduces a new variable for a bitvector `x = BitVec("t_atom_x", N)` and returns `Exists(x, And(is_part_of(x, main_world), verify(x, A)))`.
      - `true_at(B, main_world)` introduces a new variable for a bitvector `y = BitVec("t_atom_y", N)` and returns `Exists(y, And(is_part_of(y, main_world), verify(y, B)))`.
      - `false_at(C, main_world)` introduces a new variable for a bitvector `z = BitVec("t_atom_z", N)` and returns `Exists(z, And(is_part_of(z, main_world), falsify(z, C)))`.
    - Thus requiring the original sentence to be `true_at` the `main_world` returns the following Z3 constraint:
      - `And(Or(Exists(x, And(is_part_of(x, main_world), verify(x, A))), Exists(y, And(is_part_of(y, main_world), verify(y, B)))), Exists(z, And(is_part_of(z, main_world), falsify(z, C))))`.
    - This constraint is then stored in the `model_setup` class.
  - Having stored Z3 constraints for all of the `premises` and `conclusions`, global constraints are generated and stored.
  - Z3 is then called to find a model, storing the result in a new `model_structure` class.
  - In order to store and print the proposition for `[\wedge, [\vee, A, B], [\neg, C]]` at `main_world`, the `proposition` method for each operator is called as follows:
    - The `proposition` method for `\wedge` takes any fusion of verifiers for `[\vee, A, B]` and `[\neg, C]` to be a verifier for `[\wedge, [\vee, A, B], [\neg, C]]`.
    - The `proposition` method for `\wedge` takes any falsifier for `[\vee, A, B]`, `[\neg, C]`, or `[\vee, [\vee, A, B], [\neg, C]]` to be a falsifier for `[\wedge, [\vee, A, B], [\neg, C]]`.
    - The `proposition` method for `\vee` takes any verifier for `A`, `B`, or `[\wedge, A, B]` to be a verifier for `[\vee, A, B]`.
    - The `proposition` method for `\vee` takes any fusion of falsifiers for `A` and `B` to be a falsifier for `[\vee, A, B]`.
    - The `proposition` method for `\neg` takes any falsifier for `C` to be a verifier for `[\neg, C]`.
    - The `proposition` method for `\neg` takes any verifier for `C` to be a falsifier for `[\neg, C]`.
  - In this way we may identify the verifiers and falsifiers for `[\wedge, [\vee, A, B], [\neg, C]]`, storing the result alongside the prefix sentence in the `model_structure` class.
  - We may the proceed to print 
