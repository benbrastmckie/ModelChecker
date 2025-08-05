# State Semantics for Counterfactuals

The examples given below compare the following semantic theories: the semantics truthmaker semantics with the primitive imposition relation

1. Imposition is a primitive relation
2. Imposition is defined in mereological and modal terms

## Primitive Imposition

Here are the Z3 constraints on the primitive imposition relation:

```python
def _define_imposition_operation(self):
    """Define the imposition operation as a Z3 function."""
    # Define the imposition function for Fine's semantics
    self.imposition = z3.Function(
        "imposition",
        z3.BitVecSort(self.N),  # state imposed
        z3.BitVecSort(self.N),  # world being imposed on
        z3.BitVecSort(self.N),  # outcome world
        z3.BoolSort()           # truth-value
    )

    # Define the frame constraints
    x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
    possibility_downard_closure = ForAll(
        [x, y],
        z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
    )

    inclusion = ForAll(
        [x, y, z],
        z3.Implies(
            self.imposition(x, y, z),
            self.is_part_of(x, z)
        )
    )

    actuality = ForAll(
        [x, y],
        z3.Implies(
            z3.And(
                self.is_part_of(x, y),
                self.is_world(y)
            ),
            Exists(
                z,
                z3.And(
                    self.is_part_of(z, y),
                    self.imposition(x, y, z),
                )
            )
        )
    )

    incorporation = ForAll(
        [x, y, z, u],
        z3.Implies(
            z3.And(
                self.imposition(x, y, z),
                self.is_part_of(u, z)
            ),
            self.imposition(self.fusion(x, u), y, z)
        )
    )

    completeness = ForAll(
        [x, y, z],
        z3.Implies(
            self.imposition(x, y, z),
            self.is_world(z)
        )
    )

    # Set frame constraints
    self.frame_constraints = [
        possibility_downard_closure,
        inclusion,
        actuality,
        incorporation,
        completeness,
    ]
```

## Alternative Worlds

Instead of taking imposition to be defined, `is_alternative` can be defined so that analogues of the frame constraints on imposition can be derived:

```python
def compatible(self, state_x, state_y):
    """Determines if the fusion of two states is possible."""
    return self.possible(self.fusion(state_x, state_y))

def maximal(self, state_w):
    """Determines if a state is maximal with respect to compatibility."""
    x = z3.BitVec("max_x", self.N)
    return ForAll(
        x,
        z3.Implies(
            self.compatible(x, state_w),
            self.is_part_of(x, state_w),
        ),
    )

def is_world(self, state_w):
    """Determines if a state represents a possible world in the model."""
    return z3.And(
        self.possible(state_w),
        self.maximal(state_w),
    )

def max_compatible_part(self, state_x, state_w, state_y):
    """Determines if state_x is the maximal part of state_w compatible with
    state_y."""
    z = z3.BitVec("max_part", self.N)
    return z3.And(
        self.is_part_of(state_x, state_w),
        self.compatible(state_x, state_y),
        ForAll(
            z,
            z3.Implies(
                z3.And(
                    self.is_part_of(z, state_w),
                    self.compatible(z, state_y),
                    self.is_part_of(state_x, z),
                ),
                state_x == z,
            ),
        ),
    )

def is_alternative(self, state_u, state_y, state_w):
    """Determines if a state represents an alternative world resulting from
    imposing one state on another."""
    z = z3.BitVec("alt_z", self.N)
    return z3.And(
        self.is_world(state_u),
        self.is_part_of(state_y, state_u),
        Exists(
            [z],
            z3.And(
                self.is_part_of(z, state_u),
                self.max_compatible_part(z, state_w, state_y)
            )
        )
    )
```

## Semantics

Since `is_alternative` is the defined analogue of the primitive `imposition` relation, the semantic clause for the counterfactual conditional is the same in both theories, where the only difference is that `imposition` is used in one and `is_alternative` is used in the other:

### Counterfactual Conditional

```python
class ImpositionOperator(syntactic.Operator):
    """Implementation of the counterfactual conditional.
    
    This operator represents the counterfactual conditional 'if A were the case, 
    then B would be the case'. The semantics involves evaluating the consequent 
    in the outcome possible worlds that result from imposing verifier states for
    the antecedent on the world of evaluation."""

    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_imp_x", N)
        u = z3.BitVec("t_imp_u", N)
        eval_world = eval_point["world"]
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.imposition(x, eval_world, u)
                ),
                semantics.true_at(rightarg, {"world": u}),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_imp_x", N)
        u = z3.BitVec("f_imp_u", N)
        eval_world = eval_point["world"]
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.imposition(x, eval_world, u),
                sem.false_at(rightarg, {"world": u})),
            )

class CounterfactualOperator(syntactic.Operator):
    """Implementation of the counterfactual conditional.
    
    This operator represents the counterfactual conditional 'if A were the case, 
    then B would be the case'. The semantics involves evaluating the consequent 
    in the alternative possible worlds that contain a verifier for the antecedent
    together with a maximal part of the world of evaluation that is compatible
    with that verifier for the antecedent."""

    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for counterfactual conditional at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_cf_x", N)
        u = z3.BitVec("t_cf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.is_alternative(u, x, eval_point["world"])
                ),
                semantics.true_at(rightarg, {"world": u}),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for counterfactual conditional at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("f_cf_x", N)
        u = z3.BitVec("f_cf_u", N)
        return Exists(
            [x, u],
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"]),
                semantics.false_at(rightarg, {"world": u})),
        )
```

### Metaphysical Modal

Both the Imposition semantics and the Logos semantics make use of the following clause for the metaphysical modal:

```python
class NecessityOperator(syntactic.Operator):
    """Implementation of the necessity/universal modality (□).
    
    This operator represents the modal necessity 'it is necessarily the case that',
    often written as □A. The semantics involves quantifying over all possible worlds
    in the model without restriction, checking that A is true in all of them.
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for necessity at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, {"world": u}),
            ),
        )
    
    def false_at(self, argument, eval_point):
        """Defines falsity conditions for necessity at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.false_at(argument, {"world": u}),
            ),
        )
```

## Validity

That analogues of the frame constraints on `imposition` can be derived for `is_alternative` shows that the logic is at least as strong. We can provide evidence for this by showing that the axioms and rules of the counterfactual logic do not have countermodels for `N > 3` for both semantic theories:

```consol
========================================

EXAMPLE IM_TH_5: there is no countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. ((A \vee B) \boxright C)

Conclusion:
2. (A \boxright C)

Z3 Run Time: 0.523 seconds

========================================
```
Although the imposition theory times out when `N = 5`, the logos theory is able to rule out countermodels easily:
```consol
========================================

EXAMPLE IM_TH_5: there is no countermodel.

Atomic States: 5

Semantic Theory: Brast-McKie

Premise:
1. ((A \vee B) \boxright C)

Conclusion:
2. (A \boxright C)

Z3 Run Time: 1.092 seconds

========================================
```

## Countermodels

We now proceed to consider countermodels on each semantic theory beginning with a vivid case:

### Imposition Theory

```consol
========================================

EXAMPLE IM_CM_0: there is a countermodel.

Atomic States: 4

Semantic Theory: Fine

Premises:
1. \neg A
2. (A \diamondright C)
3. (A \boxright C)

Conclusion:
4. ((A \wedge B) \boxright C)

Z3 Run Time: 0.1374 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a (world)
  #b0010 = b
  #b0100 = c
  #b0110 = b.c (world)
  #b1000 = d
  #b1010 = b.d (world)

Imposition Relation:
  a →_□ a
  a →_a a
  a →_b.c b.c
  a →_b.d b.d
  b.c →_□ b.c
  b.c →_b b.c
  b.c →_c b.c
  b.c →_b.c b.c
  b.d →_□ b.d
  b.d →_b b.d
  b.d →_d b.d
  b.d →_b.d b.d

The evaluation world is: a

INTERPRETED PREMISES:

1.  |\neg A| = < {a}, {b.d, c} >  (True in a)
      |A| = < {b.d, c}, {a} >  (False in a)

2.  |(A \diamondright C)| = < {a, b.d}, {b.c} >  (True in a)
      |A| = < {b.d, c}, {a} >  (False in a)
      |A|-alternatives to a = {b.d}
        |C| = < {a, d}, {b.c} >  (True in b.d)

3.  |(A \boxright C)| = < {a, b.d}, {b.c} >  (True in a)
      |A| = < {b.d, c}, {a} >  (False in a)
      |A|-alternatives to a = {b.d}
        |C| = < {a, d}, {b.c} >  (True in b.d)

INTERPRETED CONCLUSION:

4.  |((A \wedge B) \boxright C)| = < {b.d}, {a, b.c} >  (False in a)
      |(A \wedge B)| = < {b.c}, {a, d} >  (False in a)
        |A| = < {b.d, c}, {a} >  (False in a)
        |B| = < {a, b.c}, {d} >  (True in a)
      |(A \wedge B)|-alternatives to a = {b.c}
        |C| = < {a, d}, {b.c} >  (False in b.c)


========================================
```
The example above is _non-vacuous_ insofar as there are `|A|-alternatives` to the world of evaluation `a` in the case of both counterfactual premises. The non-vacuous of the present case was contrived by including `(A \diamondright C)` among the premises despite the fact that the inference is valid even without this additional premise.

### Logos Theory

```consol
========================================

EXAMPLE IM_CM_0: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \diamondright C)
3. (A \boxright C)

Conclusion:
4. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0201 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (world)
  #b1000 = d
  #b1010 = b.d (world)
  #b1100 = c.d (world)

The evaluation world is: a.c

INTERPRETED PREMISES:

1.  |\neg A| = < {c}, {b} >  (True in a.c)
      |A| = < {b}, {c} >  (False in a.c)

2.  |(A \diamondright C)| = < {a.b, a.c}, {b.d, c.d} >  (True in a.c)
      |A| = < {b}, {c} >  (False in a.c)
      |A|-alternatives to a.c = {a.b}
        |C| = < {a.b}, {a.c, b.d, c.d} >  (True in a.b)

3.  |(A \boxright C)| = < {a.b, a.c}, {b.d, c.d} >  (True in a.c)
      |A| = < {b}, {c} >  (False in a.c)
      |A|-alternatives to a.c = {a.b}
        |C| = < {a.b}, {a.c, b.d, c.d} >  (True in a.b)

INTERPRETED CONCLUSION:

4.  |((A \wedge B) \boxright C)| = < ∅, {a.b, a.c, b.d, c.d} >  (False in a.c)
      |(A \wedge B)| = < {b.d}, {a, a.c, c} >  (False in a.c)
        |A| = < {b}, {c} >  (False in a.c)
        |B| = < {b.d, d}, {a} >  (False in a.c)
      |(A \wedge B)|-alternatives to a.c = {b.d}
        |C| = < {a.b}, {a.c, b.d, c.d} >  (False in b.d)


========================================
```
The example above is also _non-vacuous_ on account of their being `|A|-alternatives` for both counterfactual premises. We find something different in `(A \diamondright C)` is omitted from the example.

## Vacuous Countermodels

The following example is similar to `IM_CM_1` except that `(A \diamondright C)` has been omitted:

### Imposition Semantics

```consol
========================================

EXAMPLE IM_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Fine

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.1477 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a (world)
  #b0100 = c
  #b1000 = d
  #b1100 = c.d (world)

Imposition Relation:
  a →_□ a
  a →_a a
  a →_c.d c.d
  c.d →_□ c.d
  c.d →_c c.d
  c.d →_d c.d
  c.d →_c.d c.d

The evaluation world is: a

INTERPRETED PREMISES:

1.  |\neg A| = < {a}, {d} >  (True in a)
      |A| = < {d}, {a} >  (False in a)

2.  |(A \boxright C)| = < {a}, {c.d} >  (True in a)
      |A| = < {d}, {a} >  (False in a)
      |A|-alternatives to a = ∅

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < ∅, {a, c.d} >  (False in a)
      |(A \wedge B)| = < {c.d}, {a} >  (False in a)
        |A| = < {d}, {a} >  (False in a)
        |B| = < {c, c.d}, {a} >  (False in a)
      |(A \wedge B)|-alternatives to a = {c.d}
        |C| = < {a}, {d} >  (False in c.d)


========================================
```
Here we see that there are no `|A|-alternatives` to the evaluation world `a`, and so `(A \diamondright C)` is vacuously true. This follows from the fact that the frame constraints on the `imposition` relation are relatively weak, and so easy to satisfy.

### Logos Semantics

```consol
========================================

EXAMPLE IM_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0271 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (world)
  #b1000 = d
  #b1010 = b.d (world)

The evaluation world is: b.d

INTERPRETED PREMISES:

1.  |\neg A| = < {d}, {a} >  (True in b.d)
      |A| = < {a}, {d} >  (False in b.d)

2.  |(A \boxright C)| = < {a.b, b.d}, {a.c} >  (True in b.d)
      |A| = < {a}, {d} >  (False in b.d)
      |A|-alternatives to b.d = {a.b}
        |C| = < {a.b}, {a.c, b.d} >  (True in a.b)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < ∅, {a.b, a.c, b.d} >  (False in b.d)
      |(A \wedge B)| = < {a.c}, {a.b, b.d, d} >  (False in b.d)
        |A| = < {a}, {d} >  (False in b.d)
        |B| = < {c}, {a.b, b.d} >  (False in b.d)
      |(A \wedge B)|-alternatives to b.d = {a.c}
        |C| = < {a.b}, {a.c, b.d} >  (False in a.c)


========================================
```
Although the example is the same, this time there are `|A|-alternatives` to the evaluation world `a`, and so the premises are both non-vacuous.

## Metaphysical Modality Defined

The vacuous countermodels hold significance for the definitions of the metaphysical modal in terms of the counterfactual conditional `\Box A := \neg A \boxright \bot` and `\Box A := \top \boxright A`. Beginning with the former, consider the following theorem and vacuous countermodel:

### Imposition Semantics

```consol
========================================

EXAMPLE IM_CM_29: there is no countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. \Box A

Conclusion:
2. (\neg A \boxright \bot)

Z3 Run Time: 0.154 seconds

========================================
========================================

EXAMPLE IM_CM_28: there is a countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. (\neg A \boxright \bot)

Conclusion:
2. \Box A

Z3 Run Time: 0.0837 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a (world)
  #b0010 = b (world)
  #b0100 = c (world)
  #b1000 = d (world)

Imposition Relation:
  a →_□ a
  a →_a a
  b →_□ b
  b →_b b
  c →_□ c
  c →_c c
  d →_□ d
  d →_d d

The evaluation world is: d

INTERPRETED PREMISE:

1.  |(\neg A \boxright \bot)| = < {d}, {a, b, c} >  (True in d)
      |\neg A| = < {a, b, c}, {d} >  (False in d)
        |A| = < {d}, {a, b, c} >  (True in d)
      |\neg A|-alternatives to d = ∅

INTERPRETED CONCLUSION:

2.  |\Box A| = < ∅, {□} >  (False in d)
      |A| = < {d}, {a, b, c} >  (False in a)
      |A| = < {d}, {a, b, c} >  (False in b)
      |A| = < {d}, {a, b, c} >  (False in c)
      |A| = < {d}, {a, b, c} >  (True in d)


========================================
```
Although the _left-to-right_ direction of `\Box A := \neg A \boxright \bot` is valid on the Imposition semantics for `N = 4`, greater values of `N > 4` timeout. Additionally, the _right-to-left_ direction is invalid since `(\neg A \boxright \bot)` is vacuously true. This follows from the fact that the frame constraints on `imposition` are easy to satisfy.

That there exist countermodels to the inference above entail that `\boxright` is not strong enough to define `\Box` on the imposition semantics. We do not find countermodels if `is_alternative` is used in place of `imposition`:

### Logos Semantics

The following provide evidence that `\Box A := \neg A \boxright \bot` is valid on the Logos semantics, and indeed this can be proven by hand:
```consol
========================================

EXAMPLE IM_CM_29: there is no countermodel.

Atomic States: 6

Semantic Theory: Brast-McKie

Premise:
1. \Box A

Conclusion:
2. (\neg A \boxright \bot)

Z3 Run Time: 2.579 seconds

========================================
========================================

EXAMPLE IM_CM_28: there is no countermodel.

Atomic States: 6

Semantic Theory: Brast-McKie

Premise:
1. (\neg A \boxright \bot)

Conclusion:
2. \Box A

Z3 Run Time: 7.1427 seconds

========================================
```
Even with `N = 6`, generating state spaces with 64 states, there are no countermodels to the definition `\Box A := \neg A \boxright \bot` on the Logos semantics. This establishes that the counterfactual conditional is strictly stronger on the Logos semantics than it is on the Imposition semantics. Since neither theory finds countermodels to the converse inference, 

## Non-Vacuous Countermodels

Similar effects are found to undermine the definition `\Box A := \top \boxright A` on the Imposition semantics but not on the Logos semantics.

### Imposition Semantics

```consol
========================================

EXAMPLE IM_TH_11: there is no countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. \Box A

Conclusion:
2. (\top \boxright A)

Z3 Run Time: 0.1693 seconds

========================================
========================================

EXAMPLE IM_CM_22: there is a countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. (\top \boxright A)

Conclusion:
2. \Box A

Z3 Run Time: 0.0714 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a
  #b0100 = c
  #b0101 = a.c (world)
  #b1000 = d
  #b1001 = a.d (world)

Imposition Relation:
  a.c →_□ a.c
  a.c →_a a.c
  a.c →_c a.c
  a.c →_a.c a.c
  a.d →_□ a.d
  a.d →_a a.d
  a.d →_d a.d
  a.d →_a.d a.d

The evaluation world is: a.c

INTERPRETED PREMISE:

1.  |(\top \boxright A)| = < {a.c}, {a.d} >  (True in a.c)
      |\top| = < {a, a.c, a.d, c, d, □}, ∅ >  (True in a.c)
      |\top|-alternatives to a.c = {a.c}
        |A| = < {a.c}, {d} >  (True in a.c)

INTERPRETED CONCLUSION:

2.  |\Box A| = < ∅, {□} >  (False in a.c)
      |A| = < {a.c}, {d} >  (True in a.c)
      |A| = < {a.c}, {d} >  (False in a.d)


========================================
```
In contrast to the examples given above, the Imposition semantics now finds non-vacuous countermodels to the definition `\Box A := \top \boxright A` since there are `|\top|-alternatives` which nevertheless make the premise true even. We find something different for the Logos semantics.

### Logos Semantics

As before, there are no countermodels to `\Box A := \top \boxright A` on the Logos semantics for `N = 6`:
```consol
========================================

EXAMPLE IM_TH_11: there is no countermodel.

Atomic States: 6

Semantic Theory: Brast-McKie

Premise:
1. \Box A

Conclusion:
2. (\top \boxright A)

Z3 Run Time: 5.3883 seconds

========================================
========================================

EXAMPLE IM_CM_22: there is no countermodel.

Atomic States: 6

Semantic Theory: Brast-McKie

Premise:
1. (\top \boxright A)

Conclusion:
2. \Box A

Z3 Run Time: 1.6948 seconds

========================================
```

## Implications

The examples above compare the Imposition semantics and Logos semantics by evaluating the definitions of metaphysical modality `\Box A := \neg A \boxright \bot` and `\Box A := \top \boxright A`. We now proceed to compare the strength of the two semantic theories directly by taking `\boxrightlogos` to be have the Logos semantics and reserve `\boxright` for the Imposition semantics.

### 
