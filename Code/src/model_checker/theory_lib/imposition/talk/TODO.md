# TODO

- [x] Print Imposition Relation
- Change '\\imposition' to '\\boxright'
- Change '\\could' to '\\diamondright'
- Change '\\unineg' to '\\neg', etc.

## `IM_CM_24_example`

Why is `|(A \imposition B)| = < {□}, ∅ >  (True in b)`?

```consol
2.  |\Box (A \imposition B)| = < ∅, {□} >  (False in c)
      |(A \imposition B)| = < {□}, ∅ >  (True in b)
        |A| = < {b}, {c} >  (True in b)
          |A|-alternatives to b = {b}
            |B| = < ∅, {b, b.c, c} >  (False in b)
      |(A \imposition B)| = < {□}, ∅ >  (True in c)
        |A| = < {b}, {c} >  (False in c)
          |A|-alternatives to c = ∅
```

## Define `find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point)`

- A state verifies a counterfactual iff imposing any verifier for the leftarg results in outcome worlds that make rightarg true
- A state falsifies a counterfactual iff imposing some verifier for the leftarg results in outcome worlds that makes rightarg false
