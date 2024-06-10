# Semantics

<!-- INCLUDE INTRO WITH THE FOLLOWING -->
<!-- Once converted, the prefix premises and conclusions are stored in a ModelSetup object. -->
<!-- It is inside ModelSetup that the `define_N_semantics` from the `semantics` module is defined, where this includes the following primitives:  -->
<!--   - `verify` and `falsify` are relations between states and atomic sentences. -->
<!--   - `possible` a property of states. -->
<!--   - `assign` is a function from state-sentence pairs to states and is used to Skolemize the exhaustivity constraint brought out below. -->
<!--   - `w` is the designated world at which sentences are evaluated. -->
<!-- The prefix premises and conclusions are then converted into Z3 constraints by requiring each premise to be `true_at` the world `w` and each conclusion to be `false_at` the world `w`. -->
<!-- The `true_at` and `false_at` functions include the semantic clauses for the operators in the language and is discussed in greater detail in [Semantics](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/semantics.md). -->

The semantics is divided into two levels where sentences are assigned verifier and falsifier _states_ in addition to be evaluated for truth and falsity at _world states_.
Whereas every sentence is required to be either true or false but not both at each world state, the same constraints do not apply to the verifiers and falsifiers for sentences.
Rather, a sentence may be verified by some states, falsified by other states, possibly both verified and falsified by certain states, and neither verified nor falsified by the rest of the states in the space.
The reason for this difference is that states are required to be _wholly relevant_ to the sentences that they verify or falsify.
In order to encode relevance, states are taken to have mereological structure, bearing parthood relations to each other.
This section will provide a brief overview of the implementation of the semantics developed in the accompanying [paper](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).

States are modeled by BitVectors of a user-specified length `N` where a BitVector is a binary representation of an integer preceded by '#b'.
For instance, 5 is represented by the BitVector `#b101` of length `N = 3`, as well as by the BitVector `#b0000101` of length `N = 7`.
Any two states `s` and `t` will have a _state fusion_ `s | t` where `|` is the bitwise OR-operator and already provided by Z3.
For instance, `#b101 | #b010 = #b111` since `#b111` is the result of taking the max value in each position of `#b101` and `#b010`.
Holding the length `N` of states fixed, the _atomic states_ are represented by bitvectors with exactly one occurrence of 1 and the _null state_ is represented by the state with no occurrences of 1.
Accordingly, `N` specifies the number of atomic states in the space, where every state is decomposable into a fusion of atomic states.

Given the primitives declared by `define_N_semantics`, the `semantics` module begins by defining a number of basic functions by calling on the Z3 logical primitives `ForAll`, `Exists`, `Implies`, and `And`:
- `fusion(s, t)` returns `s | t`.
- `is_part_of(s, t)` returns `True` _if_ `s | t = t`, and `False` otherwise.
- `compatible(s, t)` returns `possible(fusion(s, t))`.
- `maximal(s)` returns `ForAll(x, Implies(compatible(x, bit_w), is_part_of(x, bit_w)))` where `x = BitVec("max_x", N)` declares the _sort_ (i.e., type) of the variable.
- `is_world(s)` returns `And(possible(s), maximal(s))`.
The final definition declares what it is to be a world state within a given model in close accordance with the definitions first presented by [Fine 2012](https://www.pdcnet.org/jphil/content/jphil_2012_0109_0003_0221_0246).
Building on Fine's framework, the following definitions articulate what it is for one world state to be an `s`-_alternative_ of another world state where `s` is any state:
  - `max_compatible_part(t, w, s)` returns `And(is_part_of(t, w), compatible(t, s), ForAll(z, Implies(And(is_part_of(z, w), compatible(z, s), is_part_of(t, z)), t == z)))` where `z = BitVec("max_part", N)`.
  - `is_alternative(u, s, w)` returns `And(is_world(u), is_part_of(s, u), Exists(z, And(is_part_of(z, u), max_compatible_part(z, w, s))))` where `z = BitVec("alt_z", N)`.
These definitions provide the resources need to articulate a semantics for a language which includes counterfactual conditionals, circumstantial modals, and constitutive explanatory operators.

Instead of assigning abstract truth-conditions to sentences, the semantics converts sentences in prefix form into Z3 constraints.

Since all relations in the manuscript are defined on the basis of the fusions of states—which states are compatible, possible, alternatives to others—this function basically allows for this project to use Z3 to solve constraints (i.e. this project is possible basically because of this function).
BitVectors are used throughout the entire program _right until_ the moment of translation into a readable output—quite literally right until: whenever you see a function referring to states in the code, _never_ does it work with a printable/readable version of the state (e.g., 101 as 'a.c') (unless of course that function is going to print the state).
Most notably, the notions of "possible" and "verify" and other similar ones now thus have a natural understanding as a mathematical (i.e., not a python function—I will use mathematical to refer to this sense of the word function; otherwise function will refer to the python sense unless context is obvious) function from numbers (viz. BitVectors i.e. states) to truth values (e.g. which ones verify others, which ones are possible).
The constraints are thus definitions which determine _which states_ are map to True and which ones to False for each of these notions.
With that in mind, a philosopher looking at the `semantics` module should be able to understand the functions `true_at`, `extended_verify`, `is_world`, `is_alternative`, etc without any coding background: just substitute any instance of BitVectors with states in your head, and the rest is right from the manuscript.
Unfortunately the entirety of the module is not that simple because a sneaky programming trick had to be employed.
Many of these functions depend on `N`, which is the total number of atomic states in the model that is desired.
Because of this, they must have `N` as an input.
However, since many of the functions are recursive and there are just so many functions overall adding `N` as an input proves tedious.
So, instead, the semantics is defined inside the scope of another function, which takes `N` as an input.
(It also takes `possible`, `verify`, and those other similar ones as input, since those also depend on `N` on the Z3 side of things) This means that no function (like e.g. `extended_verify`) needs to have `N` passed into it even though it needs it: the function simply would look to the next frame where the variable `N` is defined, which is the frame of the outer function so to speak (same goes for `possible`, `verify`, etc).
This seems weird, but kind of has an intuitive reading: to define "all" of the states, we need to know how many states we're talking about, so in order to define the semantics, `N` has to be known.
Fittingly, the outer function—the one _in which_ the semantics are literally defined and under this intuitive reading are conceptually defined—is called `define_N_semantics`.

_**Now back to the main story:**_ when the premises, conclusions, and `N` are passed into `define_N_semantics`, constraints following the semantics in the manuscript are made. This are saved to the ModelSetup object. At this point, the first step is done: the sentences have been translated into a lower level form, and what we have to work with is now a set of constraints on a whole bunch of integers as to which are "possible," "verify" others, etc. 
