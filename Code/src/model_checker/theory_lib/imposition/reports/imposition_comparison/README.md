# Imposition Comparison Reports: Counterfactual Semantics Analysis

[← Back to Imposition Reports](../README.md) | [Frame Constraints →](frame_constraints.md) | [Modals Defined →](modals_defined.md)

## Directory Structure

```
imposition_comparison/
├── README.md                       # This file - comparison reports hub
├── frame_constraints.md            # Frame constraint satisfaction analysis
├── modals_defined.md               # Modal definability investigation
└── data/                           # JSON countermodel data
    ├── IM_CM_22.json               # Countermodel for ⊤ \boxright A
    ├── IM_CM_26.json               # Imposition ⊬ Logos example
    ├── IM_CM_27.json               # Logos ⊬ Imposition example
    └── IM_CM_28.json               # Countermodel for ¬A \boxright ⊥
```

## Overview

This directory contains analyses comparing Kit Fine's imposition-based semantics with Benjamin Brast-McKie's Logos semantics for counterfactuals. The reports reveal fundamental differences in how these theories handle alternative world selection despite their shared foundation in state-based truthmaker semantics.

While both theories satisfy the same frame constraints, they generate distinct logics. These finding help to illuminate questions about the relationship between formal constraints and semantic behavior as well as demonstrating a programmatic methodology in semantics.

## Reports

### 1. [Frame Constraints and Logical Independence](frame_constraints.md)

**Research Question**: Does the definition of alternatives in logos semantics automatically satisfy Fine's frame constraints? And if so, do the theories generate the same logic?

**Key Findings**:

- The `is_alternative` relation automatically satisfies all four frame constraints (inclusion, actuality, incorporation, completeness)
- This is proven using ModelChecker's constraint testing methodology with `derive_imposition=True`
- Despite structural equivalence, the theories are logically independent: neither `(A \boxright B) ⊢ (A \boxrightlogos B)` nor `(A \boxrightlogos B) ⊢ (A \boxright B)` holds
- The primitive imposition relation permits "jumps" to unrelated worlds that satisfy constraints but violate minimal change intuitions

**Methodology Highlight**: The report demonstrates how to prove constraint satisfaction by searching for violations - if no countermodel exists to the negated constraints, the properties must hold. This technique transforms theorem proving into model finding.

### 2. [Modal Definability via Counterfactuals](modals_defined.md)

**Research Question**: Can metaphysical necessity (□) be defined using counterfactual conditionals in each semantic framework?

**Key Findings**:

- The imposition semantics cannot define `\Box A` via either `\neg A \boxright \bot` or `\top \boxright A`
- Countermodels exist because the imposition relation can generate vacuous counterfactuals
- The logos semantics validates both definitions up to `N = 6` with no countermodels found
- The difference stems from how each theory handles alternative world generation - logos ensures alternatives exist when they should theoretically exist

**Technical Insight**: The report includes detailed countermodel analyses showing exactly how vacuous truth in imposition semantics undermines modal definability.

## Key Examples

### The Minimal Distinguishing Case (IM_CM_27)

The smallest countermodel distinguishing the theories has just 2 atomic states:

```
State Space: □, a (world), b (world)

Imposition Relation:
  a -->_□ a    # Expected: a is the result of imposing □ on a
  a -->_□ b    # Unexpected: b is the result of imposing □ on a!
  a -->_a a
  a -->_b b
  b -->_□ b
  b -->_b b
```

When imposing the null state □ on world a:

- **Logos**: Only a is an alternative (maximal preservation)
- **Imposition**: Both a and b are alternatives (the "jump" phenomenon)

This minimal example crystallizes the fundamental difference between the approaches.

### Vacuous Truth Problem (IM_CM_26)

```
State Space: □, c (world), d (world)

Evaluation world: d
|A| = < {c}, {d} >  (False in d)

Imposition: No |A|-alternatives to d (vacuously true)
Logos: World c is an |A|-alternative to d (non-vacuously false)
```

The imposition semantics makes counterfactuals true by failing to generate alternatives, while logos ensures alternatives exist when they should theoretically exist.

## Theoretical Implications

### The Jump Problem

The primitive imposition relation exhibits problematic behavior:

- Can "jump" to unrelated worlds when imposing compatible states
- These jumps satisfy all frame constraints technically
- But violate the philosophical principle of minimal change
- Most evident with null state imposition: `a -->\_□ b`

## Methodology

### Constraint Testing

The reports demonstrate a powerful technique for proving semantic properties:

```python
# Traditional: Prove the following by element tracing or proof by contradiction
constraints.append(ForAll([x, y], property(x, y)))

# ModelChecker: Search for violations
test_constraints = [Exists([x, y], Not(property(x, y)))]
# No model found => property always holds
```

This approach leverages Z3's efficient search to establish results that would be tedious to prove by hand.

### Comparative Analysis

The reports establish patterns for systematic theory comparison:

1. Implement both theories with identical vocabulary
2. Test shared principles and divergence points
3. Analyze minimal distinguishing countermodels
4. Extract philosophical insights from technical results

## Related Resources

### Documentation Guides

- [ModelChecker Workflow Guide](../../../../../Docs/usage/WORKFLOW.md) - Introduction to using the framework
- [Theory Comparison Guide](../../../../../Docs/usage/COMPARE_THEORIES.md) - Methodology for comparing semantic theories
- [Constraint Testing Guide](../../../../../Docs/usage/CONSTRAINTS.md) - Testing semantic constraints through countermodel search
- [Methodology Documentation](../../../../../Docs/methodology/README.md) - Philosophical foundations of programmatic semantics

### Theory Implementation

- [Imposition Theory](../../README.md) - Kit Fine's imposition semantics implementation
- [Logos Theory](../../../../logos/README.md) - Brast-McKie's hyperintensional semantics
- [Counterfactual Subtheory](../../../../logos/subtheories/counterfactual/README.md) - Logos counterfactual operators

### Source Code

- [Imposition Semantics](../../semantic.py) - Implementation of `derive_imposition` testing
- [Imposition Operators](../../operators.py) - Implementation of `derive_imposition` testing
- [Logos Counterfactual Operators](../../../../logos/subtheories/counterfactual/operators.py) - Comparative operator definitions

### Data Files

- [data/](data/) - JSON files containing detailed countermodel structures
  - `IM_CM_22.json` - Modal definability counterexample
  - `IM_CM_26.json` - Imposition does not entail Logos
  - `IM_CM_27.json` - Logos does not entail Imposition (minimal case)
  - `IM_CM_28.json` - Vacuous counterfactual example

## Future Directions

- Can additional constraints force convergence between the theories?
- Investigate probabilistic or graded notions of alternatives

---

[← Back to Imposition Reports](../README.md) | [Frame Constraints →](frame_constraints.md) | [Modals Defined →](modals_defined.md)
