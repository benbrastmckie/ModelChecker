# Frame Constraints and Counterfactual Independence: A Technical Analysis

## Introduction

This report demonstrates that while the constructive definition `is_alternative` in the logos semantics automatically satisfies all frame constraints imposed on Fine's primitive imposition relation, the two theories generate logically independent counterfactual logics. The analysis reveals how primitive relations can "jump" to unrelated worlds in ways that violate minimal change intuitions.

## Part 1: Deriving Frame Constraint Analogs

### The Frame Constraints on Imposition

Fine's imposition semantics imposes four frame constraints on the primitive relation `imposition(x, w, u)` meaning "u is a result of imposing state x on world w":

1. **Inclusion**: `imposition(x, w, u) => part(x, u)`  
   The imposed state must be part of the outcome world

2. **Actuality**: `part(x, w) ∧ world(w) => ∃u[part(u, w) ∧ imposition(x, w, u)]`  
   Every part of a world can be successfully imposed on that world

3. **Incorporation**: `imposition(x, w, u) ∧ part(v, u) => imposition(x⊔v, w, u)`  
   If we can impose x to get u, we can also impose the fusion of x with any part of u

4. **Completeness**: `imposition(x, w, u) => world(u)`  
   The outcome must be a complete possible world

### The Alternative Relation Analog

The logos semantics defines `alt_imposition` as a reordering of the constructive `is_alternative`:

```python
def alt_imposition(self, state_y, state_w, state_u):
    """Determines if state_u is an alternative world resulting from
    imposing state_y on state_w.
    
    This method permutes the arguments to provide an exact analog of the 
    primitive imposition relation."""
    
    return self.is_alternative(state_u, state_y, state_w)
```

Where `is_alternative` is defined constructively:

```python
def is_alternative(self, state_u, state_y, state_w):
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

### Testing Constraint Satisfaction with `derive_imposition = True`

The ModelChecker provides a sophisticated test mechanism through the `derive_imposition` setting:

```python
def _derive_imposition(self):
    """Given the definition of `is_alternative`, we may derive analogs
    of the frame constraints for imposition."""
    
    # Define the frame constraints using alt_imposition
    x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
    
    alt_inclusion = ForAll(
        [x, y, z],
        z3.Implies(
            self.alt_imposition(x, y, z),
            self.is_part_of(x, z)
        )
    )
    
    alt_actuality = ForAll(
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
                    self.alt_imposition(x, y, z),
                )
            )
        )
    )
    
    alt_incorporation = ForAll(
        [x, y, z, u],
        z3.Implies(
            z3.And(
                self.alt_imposition(x, y, z),
                self.is_part_of(u, z)
            ),
            self.alt_imposition(self.fusion(x, u), y, z)
        )
    )
    
    alt_completeness = ForAll(
        [x, y, z],
        z3.Implies(
            self.alt_imposition(x, y, z),
            self.is_world(z)
        )
    )
    
    # Return the disjunction of negated constraints
    neg_alt_constraints = z3.Or(
        z3.Not(alt_inclusion),
        z3.Not(alt_actuality),
        z3.Not(alt_incorporation),
        z3.Not(alt_completeness),
    )
    
    return [neg_alt_constraints]
```

When `derive_imposition=True`, the system:
1. Replaces normal imposition constraints with the negation of at least one analog constraint
2. Makes premise and conclusion behaviors trivially true: `lambda x: z3.BoolVal(True)`
3. Searches for a model satisfying base semantics but violating at least one analog

### The Result

```
EXAMPLE IM_TR_0: there is no countermodel.
Atomic States: 4
Semantic Theory: Fine
Z3 Run Time: 0.0304 seconds
```

**Interpretation**: No model can violate any of the analog constraints while satisfying the base semantics. This proves that `is_alternative` automatically satisfies all four frame constraints without needing to impose them explicitly. The constructive definition inherently has the right structural properties.

## Part 2: Logical Independence of the Counterfactual Theories

Despite sharing the same structural constraints, the two theories generate logically independent counterfactual logics, as demonstrated by two key counterexamples:

### IM_CM_26: Imposition Does Not Entail Logos

```
EXAMPLE IM_CM_26: there is a countermodel.

State Space: □, c (world), d (world)
Imposition Relation:
  □ -->_c c, c -->_c c
  □ -->_d d, d -->_d d
Evaluation world: d

INTERPRETED PREMISE:
1. |(A \boxright B)| = < {d}, {c} >  (True in d)
   |A| = < {c}, {d} >  (False in d)
   |A|-alternatives to d = ∅

INTERPRETED CONCLUSION:
2. |(A \boxrightlogos B)| = < ∅, {c, d} >  (False in d)
   |A| = < {c}, {d} >  (False in d)
   |A|-alternatives to d = {c}
     |B| = < ∅, {c, d} >  (False in c)
```

[View JSON data for IM_CM_26](data/IM_CM_26.json)

**Analysis**: The imposition counterfactual is vacuously true because the primitive relation generates no alternatives (no relation where c results from imposing c on d exists). However, the logos counterfactual correctly identifies c as an alternative and finds B false there.

### IM_CM_27: Logos Does Not Entail Imposition

```
EXAMPLE IM_CM_27: there is a countermodel.

State Space: □, a (world), b (world)
Imposition Relation:
  □ -->_a a, □ -->_a b, a -->_a a, b -->_a b
  □ -->_b b, b -->_b b
Evaluation world: a

INTERPRETED PREMISE:
1. |(A \boxrightlogos B)| = < {a}, {b} >  (True in a)
   |A| = < {□}, ∅ >  (True in a)
   |A|-alternatives to a = {a}
     |B| = < {a}, {b} >  (True in a)

INTERPRETED CONCLUSION:
2. |(A \boxright B)| = < ∅, {a, b} >  (False in a)
   |A| = < {□}, ∅ >  (True in a)
   |A|-alternatives to a = {a, b}
     |B| = < {a}, {b} >  (True in a)
     |B| = < {a}, {b} >  (False in b)
```

[View JSON data for IM_CM_27](data/IM_CM_27.json)

**Analysis**: The logos counterfactual is true because it only considers a as an alternative (preserving maximal compatibility). The imposition counterfactual fails because the primitive relation includes both a and b as alternatives.

## Part 3: The "Jump" Phenomenon

### Understanding Imposition Jumps

The key difference between the theories emerges when imposing compatible states. The imposition relation can "jump" to unrelated worlds that satisfy the frame constraints but violate minimal change intuitions.

### Case Study: The Null State Jump (IM_CM_27)

In the countermodel for IM_CM_27, we see the clearest example of an imposition jump:

**The Setup**:
- World a and world b are distinct (neither is part of the other)
- We impose the null state □ on world a
- Since □ is part of all states, it's compatible with everything

**Expected Behavior** (Logos):
- The maximal part of a compatible with □ is a itself
- Therefore, the only alternative should be a

**Actual Behavior** (Imposition):
- The relation includes □ -->_a b (b is the result of imposing □ on a)
- This allows "jumping" to b as an outcome when imposing □ on a
- World b satisfies all frame constraints:
  - Inclusion: □ ⊆ b ✓
  - Actuality: Satisfied by construction ✓
  - Incorporation: No additional constraints violated ✓
  - Completeness: b is a world ✓

### Why the Jump is Problematic

The jump from a to b when imposing □ violates the minimal change principle because:

1. **No Preservation**: World b doesn't contain any part of a (except the null state)
2. **Arbitrary Selection**: Nothing about the imposition of □ suggests b over any other world
3. **Lost Information**: All content from the original world a is discarded

### Contrast with Constructive Alternatives

The logos semantics prevents such jumps by requiring:
```
∃z[part(z, u) ∧ max_compatible_part(z, w, y)]
```

This ensures the alternative world u contains a maximal part of the original world w that's compatible with the imposed state y. When y is compatible with all of w (as with the null state), this forces u to contain all of w, preventing jumps to unrelated worlds.

## Conclusion

This analysis reveals three key insights:

1. **Structural Equivalence**: The constructive `is_alternative` automatically satisfies all frame constraints imposed on primitive imposition, demonstrating these constraints capture necessary properties of any reasonable alternative-selection mechanism.

2. **Logical Independence**: Despite structural equivalence, the theories generate incomparable logics. Neither (A \boxright B) ⊢ (A \boxrightlogos B) nor (A \boxrightlogos B) ⊢ (A \boxright B) holds in general.

3. **The Jump Problem**: The primitive imposition relation can "jump" to unrelated worlds when imposing compatible states, particularly evident with null state imposition. These jumps satisfy all frame constraints but violate the philosophical principle of minimal change that motivates counterfactual reasoning.

The frame constraints ensure basic structural coherence but underdetermine the counterfactual logic. The logos semantics adds content beyond these minimal requirements by enforcing maximal preservation through its constructive definition, thereby preventing the problematic jumps that plague the primitive imposition approach.
