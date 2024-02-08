# Design Strategies

Notes related to design problems and strategies. These should be labeled by topic.

## Z3

Motivation

- It seems that Z3 permits one to issue constraints where Z3 looks to satisfy those constraints. For instance, we will have constraints on what counts as a model and what counts as a world. Together, these yield constraints on what counts as a model-world pair. Each sentence $A$ of the object language corresponds to a further constraint on model-world pairs of the form: $A$ is true at $w$ in $M$.
