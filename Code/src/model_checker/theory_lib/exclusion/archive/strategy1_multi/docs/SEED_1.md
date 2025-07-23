# SEED

The definition of preclusion quantifies over functions:

(28) Champollion-Bernard Preclusion
"An event e Champollion-Bernard precludes a set of events S just in case there is a function h from events to events such that e = {h( f_i ) | f_i ∈ S} and for all events f_i ∈ S, h( f_i ) excludes some part of f_i."

Is this the quantification over functions you're referring to? It's not essential to the theory. Here is a version without it, inspired by an analogous definition in Fine 2017 JPL, p. 658 bottom:

(28') Fine Preclusion
"An event e Fine-precludes a set of events S just in case e is the fusion of a set of events T such that both of the following are true:
(i) for all events s ∈ S, for some event t ∈ T,  t excludes some part of s;
(ii) for all events t ∈ T, for some event s ∈ S,  t excludes some part of s;

The two definitions are not equivalent, but both work for the purposes of the paper since: 

CLAIM_1: Every CB-precluder of S is a Fine-precluder of S, and every Fine-precluder of S has a part (which may or may not be proper) that is a CB-precluder of S.

I want to verify this claim by:

1. Implementing a Fine-precludes version of the semantics give in `.../exclusion/strategy1_multi/`, adding a new FineUniNegation operator that is comparable to ExclusionOperator defined in `.../exclusion/strategy1_multi/operators.py`
2. Run all previous examples given in `.../exclusion/strategy1_multi/examples.py` with FineUniNegation to compare the accounts using `dev_cli.py`.
3. Setup explicit tests to verify CLAIM_1.

After running these tests, evaluate:

QUESTION_1: Is finding Fine precluders are more computationally tractable than finding CB precluders?
