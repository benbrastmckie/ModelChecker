# State Semantics for Counterfactuals: A Programmatic Comparison

## Introduction

This report presents a comparison of two approaches to counterfactual semantics within the ModelChecker framework: Kit Fine's imposition-based semantics and Benjamin Brast-McKie's alternative-worlds semantics. Both theories employ state-based truthmaker semantics, but they differ in how they determine the worlds relevant for evaluating counterfactual conditionals.

The methodology employed here follows the framework's standard approach for theory comparison, detailed in the [Theory Comparison Guide](../../../../../Docs/usage/COMPARE_THEORIES.md). This involves implementing both semantic theories with identical logical vocabulary, running parallel tests on shared examples, and analyzing where they diverge. For a comprehensive introduction to the ModelChecker workflow, see the [Workflow Guide](../../../../../Docs/usage/WORKFLOW.md). The underlying methodological principles are explained in the [Methodology Documentation](../../../../../Docs/methodology/README.md).

## Semantic Implementations

Both theories share a common foundation in truthmaker semantics. The key difference lies in how each theory handles counterfactuals:

1. **Fine's Imposition Semantics**: Uses a primitive three-place imposition relation that specifies which worlds result from imposing a state on a given world
2. **Brast-McKie's Hyperintensional Semantics**: Defines alternative worlds constructively using compatibility and maximal compatible parts

### Primitive Imposition

In Fine's approach, the imposition relation is taken as primitive and governed by frame constraints. The Z3 implementation specifies that imposition is a three-place relation `imposition(x, w, u)` meaning "imposing state x on world w can result in world u". This relation must satisfy several intuitive constraints that capture the logic of minimal change:

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

The key constraints are:
- **Inclusion**: The imposed state must be part of any resulting world
- **Actuality**: Every state that is part of a world can be successfully imposed on that world
- **Incorporation**: The imposition relation respects state fusion
- **Completeness**: The outcome of imposition must always be a complete possible world

These constraints ensure that imposition behaves reasonably but, as we'll see, they permit more alternative worlds than might be intuitively expected.

### Alternative Worlds Definition

In Brast-McKie's approach, the relation between imposed states and resulting worlds is defined constructively rather than taken as primitive. The key insight is that an alternative world should contain both the imposed state and a maximal compatible part of the original world:

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
  □ -->_a a
  a -->_a a
  b.c -->_a b.c
  b.d -->_a b.d
  □ -->_b.c b.c
  b -->_b.c b.c
  c -->_b.c b.c
  b.c -->_b.c b.c
  □ -->_b.d b.d
  b -->_b.d b.d
  d -->_b.d b.d
  b.d -->_b.d b.d

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
The example above is _non-vacuous_ insofar as there are `|A|-alternatives` to the world of evaluation `a` in the case of both counterfactual premises. The non-vacuous of the present case was contrived by including `A \diamondright C` among the premises despite the fact that the inference is valid even without this additional premise.

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
The example above is also _non-vacuous_ on account of their being `|A|-alternatives` for both counterfactual premises. We find something different if `A \diamondright C` is omitted from the example.

## Vacuous Countermodels

The following example is similar to `IM_CM_1` except that `A \diamondright C` has been omitted:

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
  □ -->_a a
  a -->_a a
  c.d -->_a c.d
  □ -->_c.d c.d
  c -->_c.d c.d
  d -->_c.d c.d
  c.d -->_c.d c.d

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
Here we see that there are no `|A|-alternatives` to the evaluation world `a`, and so `A \diamondright C` is vacuously true. This follows from the fact that the frame constraints on the `imposition` relation are relatively weak, and so easy to satisfy.

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
```consol
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
  □ -->_a a
  a -->_a a
  □ -->_b b
  b -->_b b
  □ -->_c c
  c -->_c c
  □ -->_d d
  d -->_d d

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

[View JSON data for IM_CM_28](data/IM_CM_28.json)

Although the _left-to-right_ direction of `\Box A := \neg A \boxright \bot` is valid on the Imposition semantics for `N = 4`, greater values of `N > 4` timeout. Additionally, the _right-to-left_ direction is invalid since `\neg A \boxright \bot` is vacuously true. This follows from the fact that the frame constraints on `imposition` are easy to satisfy.

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
```consol
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
  □ -->_a.c a.c
  a -->_a.c a.c
  c -->_a.c a.c
  a.c -->_a.c a.c
  □ -->_a.d a.d
  a -->_a.d a.d
  d -->_a.d a.d
  a.d -->_a.d a.d

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

[View JSON data for IM_CM_22](data/IM_CM_22.json)

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

## Direct Theory Comparison

The examples above compare the Imposition semantics and Logos semantics by evaluating the definitions of metaphysical modality `\Box A := \neg A \boxright \bot` and `\Box A := \top \boxright A`. We now proceed to compare the strength of the two semantic theories directly by taking `\boxrightlogos` to have the Logos semantics and reserve `\boxright` for the Imposition semantics.

### IM_CM_26: When Imposition Does Not Entail Logos

This example tests whether Fine's imposition counterfactual entails Brast-McKie's:

```console
========================================

EXAMPLE IM_CM_26: there is a countermodel.

Atomic States: 4

Semantic Theory: Fine

Premise:
1. (A \boxright B)

Conclusion:
2. (A \boxrightlogos B)

Z3 Run Time: 0.155 seconds

========================================
State Space:
  #b0000 = □
  #b0100 = c (world)
  #b1000 = d (world)

Imposition Relation:
  □ -->_c c
  c -->_c c
  □ -->_d d
  d -->_d d

The evaluation world is: d

INTERPRETED PREMISE:

1.  |(A \boxright B)| = < {d}, {c} >  (True in d)
      |A| = < {c}, {d} >  (False in d)
      |A|-alternatives to d = ∅

INTERPRETED CONCLUSION:

2.  |(A \boxrightlogos B)| = < ∅, {c, d} >  (False in d)
      |A| = < {c}, {d} >  (False in d)
      |A|-alternatives to d = {c}
        |B| = < ∅, {c, d} >  (False in c)
========================================
```

[View JSON data for IM_CM_26](data/IM_CM_26.json)

#### Analysis

This countermodel reveals a fundamental divergence between the two theories:

1. **Vacuous Truth in Imposition**: The imposition counterfactual (A \boxright B) is **vacuously true** at world d because there are no |A|-alternatives. The imposition relation only allows c -->_d d, but since c is not part of d, no genuine alternatives exist.

2. **Non-Vacuous Falsehood in Logos**: The logos counterfactual (A \boxrightlogos B) is **non-vacuously false** because:
   - The logos semantics finds world c as an |A|-alternative to d
   - B is false at this alternative world c
   - Therefore, the counterfactual fails

3. **Key Insight**: The imposition semantics can make counterfactuals true by failing to generate alternatives, while the logos semantics ensures alternatives exist whenever they should theoretically exist.

### IM_CM_27: When Logos Does Not Entail Imposition

Testing the converse direction yields the minimal countermodel analyzed in detail in the [null alternatives report](../../../../../../logos/subtheories/counterfactual/report/null_alts.md):

```console
========================================

EXAMPLE IM_CM_27: there is a countermodel.

Atomic States: 2

Semantic Theory: Fine

Premise:
1. (A \boxrightlogos B)

Conclusion:
2. (A \boxright B)

Z3 Run Time: 0.0029 seconds

========================================
State Space:
  #b00 = □
  #b01 = a (world)
  #b10 = b (world)

Imposition Relation:
  □ -->_a a
  □ -->_a b
  a -->_a a
  b -->_a b
  □ -->_b b
  b -->_b b

The evaluation world is: a

INTERPRETED PREMISE:

1.  |(A \boxrightlogos B)| = < {a}, {b} >  (True in a)
      |A| = < {□}, ∅ >  (True in a)
      |A|-alternatives to a = {a}
        |B| = < {a}, {b} >  (True in a)

INTERPRETED CONCLUSION:

2.  |(A \boxright B)| = < ∅, {a, b} >  (False in a)
      |A| = < {□}, ∅ >  (True in a)
      |A|-alternatives to a = {a, b}
        |B| = < {a}, {b} >  (True in a)
        |B| = < {a}, {b} >  (False in b)
========================================
```

[View JSON data for IM_CM_27](data/IM_CM_27.json)

This shows the imposition relation □ -->_a b allows "jumping" to unrelated worlds when imposing compatible states.

## Implications and Conclusions

This comparison reveals that the two counterfactual theories are **logically incomparable**:

1. **Neither Theory Entails the Other**: 
   - IM_CM_26 shows (A \boxright B) ⊬ (A \boxrightlogos B)
   - IM_CM_27 shows (A \boxrightlogos B) ⊬ (A \boxright B)

2. **Different Failure Modes**:
   - Imposition fails by permitting vacuous truth through lack of alternatives
   - Logos fails by being too restrictive about null state imposition

3. **Philosophical Divergence**: The theories embody different intuitions about counterfactual evaluation:
   - Imposition: More permissive, allowing varied outcomes from primitive relation
   - Logos: More constrained, enforcing maximal preservation of content

4. **Practical Consequences**: For automated reasoning and philosophical analysis, the choice between theories affects:
   - Which counterfactuals are judged valid
   - Computational efficiency (logos generally performs better)
   - Ability to define other modalities

For detailed analysis of specific countermodels and their philosophical significance, see:
- The [null alternatives analysis](frame_constraints.md) for the minimal distinguishing case
- Individual JSON data files in the [data directory](data/) for each example

## Further Reading

- For hands-on exploration of these theories, consult the [Workflow Guide](../../../../../Docs/usage/WORKFLOW.md)
- For systematic theory comparison methodology, see [Compare Theories](../../../../../Docs/usage/COMPARE_THEORIES.md)
- For the philosophical foundations of programmatic semantics, review the [Methodology Documentation](../../../../../Docs/methodology/README.md)
