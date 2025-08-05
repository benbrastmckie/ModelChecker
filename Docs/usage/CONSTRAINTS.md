# Testing Semantic Constraints: Proving Properties Through Countermodel Search

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Compare Theories →](COMPARE_THEORIES.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Core Methodology](#core-methodology)
   - [The Constraint Testing Pattern](#the-constraint-testing-pattern)
   - [Proof by Absence](#proof-by-absence)
3. [Implementation Techniques](#implementation-techniques)
   - [Theory-Specific Settings](#theory-specific-settings)
   - [Constraint Negation](#constraint-negation)
   - [Result Interpretation](#result-interpretation)
4. [Practical Examples](#practical-examples)
   - [Frame Constraints in Imposition Theory](#frame-constraints-in-imposition-theory)
   - [Testing Your Own Constraints](#testing-your-own-constraints)
5. [Advanced Applications](#advanced-applications)
   - [Discovering Minimal Axioms](#discovering-minimal-axioms)
   - [Comparing Constraint Systems](#comparing-constraint-systems)
6. [Troubleshooting](#troubleshooting)
7. [References](#references)

## Introduction

ModelChecker provides a methods for easily deriving semantic constraints, or establishing implications between constraints. Instead of manually proving theorems, you can use the framework to search for countermodels - if none exist, the constraint is proven to hold for at least those models that it has surveyed.

This guide explains how to use ModelChecker's constraint testing features to verify semantic properties, discover minimal axiom sets, and understand the relationships between different constraint systems. The techniques shown here are particularly valuable for researchers developing new semantic theories or investigating the foundations of existing ones.

## Core Methodology

### The Constraint Testing Pattern

The fundamental insight is to **search for violations rather than prove validity**. Given a semantic definition and a proposed constraint:

1. **Negate the constraint** - Add its negation to the model
2. **Search for models** - Use Z3 to find satisfying assignments
3. **Interpret absence** - No model means the constraint always holds

```python
# Traditional approach: Add constraint and hope it's satisfied
constraints.append(ForAll([x, y], property(x, y)))

# Constraint testing: Search for violations
test_constraints = [Exists([x, y], Not(property(x, y)))]
# If no model found => property always holds
```

This approach transforms theorem proving into model finding, leveraging Z3's efficient search capabilities.

### Proof by Absence

When ModelChecker reports "there is no countermodel" for a negated constraint, this constitutes a proof that the original constraint is entailed by the base semantics modulo the size of the models checked. The proof is constructive in the sense that Z3 has exhaustively searched the finite model space without finding violations.

Key insights:
- **Finite models suffice** - For most logical properties, small models (N=3-5) provide adequate test cases
- **Systematic search** - Z3 explores all possible assignments efficiently
- **Unsat cores** - When no model exists, Z3 can identify which constraints conflict

### Complementing Traditional Proofs

ModelChecker is not intended to replace pen-and-paper semantic proofs. Rather, it serves as a powerful companion tool that streamlines the research process:

**Rapid Exploration**: Quickly test conjectures and explore logical implications before investing time in formal proofs. What might take hours to work through by hand can be checked in seconds.

**Error Prevention**: Catch small mistakes early - a missing case, an incorrect assumption about parthood relations, or an overlooked interaction between constraints. These errors are easy to make in complex proofs but immediately revealed by countermodels.

**Hypothesis Generation**: Use countermodels to understand why certain properties fail, guiding the development of stronger or more refined principles. The concrete examples help build intuition about abstract relationships.

**Proof Validation**: After completing a pen-and-paper proof, use ModelChecker to verify the result holds in finite models. While not a complete verification, this provides valuable confidence in the proof's correctness.

The tool excels at the exploratory phase of research, where you're developing theories and testing relationships. Once you've used ModelChecker to map the logical terrain and avoid pitfalls, traditional proof methods remain essential for establishing results with full mathematical rigor.

## Implementation Techniques

### Theory-Specific Settings

ModelChecker supports theory-specific settings that modify constraint generation. The pattern for implementing constraint testing:

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_GENERAL_SETTINGS = {
        "test_constraint": False,  # Theory-specific setting
    }
    
    def __init__(self, combined_settings):
        self.test_constraint = combined_settings.get('test_constraint', False)
        
        if self.test_constraint:
            # Replace normal constraints with test constraints
            self.constraints = self._generate_test_constraints()
        else:
            # Normal semantic constraints
            self.constraints = self._generate_normal_constraints()
```

### Constraint Negation

The key technique is replacing normal constraints with their negations:

```python
def _generate_test_constraints(self):
    """Generate constraints that test whether properties hold."""
    
    # Define the properties you want to test
    property1 = ForAll([x, y], 
        Implies(self.relation(x, y), self.desired_property(x, y))
    )
    
    property2 = ForAll([x],
        Implies(self.condition(x), self.expected_result(x))
    )
    
    # Return disjunction of negations
    # This searches for ANY violation
    return [Or(
        Not(property1),
        Not(property2)
    )]
```

The disjunction means we're looking for a model that violates *at least one* property, making the search more efficient than testing properties individually.

### Result Interpretation

Results from constraint testing:

- **"No countermodel"** - All tested properties are satisfied by the base semantics
- **"Countermodel found"** - At least one property can be violated
- **Specific violations** - The countermodel shows exactly which property fails and how

## Practical Examples

### Frame Constraints in Imposition Theory

The imposition theory provides an excellent example of constraint testing in action. Fine's imposition semantics requires four frame constraints on the primitive relation, but the logos semantics defines alternatives constructively. To test whether the constructive definition automatically satisfies these constraints:

```python
# In imposition/semantic.py
if self.derive_imposition:
    # Test whether is_alternative satisfies frame constraints
    constraints = self._derive_imposition()
    
def _derive_imposition(self):
    # Define frame constraint analogs
    inclusion = ForAll([x, y, z],
        Implies(alt_imposition(x, y, z), part(x, z))
    )
    
    actuality = ForAll([x, y],
        Implies(And(part(x, y), world(y)),
            Exists([z], And(part(z, y), alt_imposition(x, y, z)))
        )
    )
    
    # Return negation to search for violations
    return [Or(Not(inclusion), Not(actuality), ...)]
```

Running with `derive_imposition=True`:
```bash
# Test frame constraints
model-checker imposition/examples.py IM_TR_0_example --derive_imposition

# Result: "there is no countermodel"
# Proves: is_alternative automatically satisfies all frame constraints
```

This proves that the constructive definition inherently has the right structural properties without needing explicit constraints.

### Testing Your Own Constraints

To test constraints in your own semantic theory:

1. **Add a theory setting**:
```python
DEFAULT_GENERAL_SETTINGS = {
    "test_fusion_closure": False,
}
```

2. **Implement constraint generation**:
```python
def _test_fusion_closure(self):
    # Property: if s1 and s2 verify A, their fusion must too
    x, y = BitVecs('x y', self.N)
    
    fusion_closure = ForAll([x, y],
        Implies(
            And(self.verify(x, self.A), self.verify(y, self.A)),
            self.verify(self.fusion(x, y), self.A)
        )
    )
    
    # Search for violations
    return [Not(fusion_closure)]
```

3. **Run the test**:
```bash
model-checker your_theory/test.py --test_fusion_closure
```

## Advanced Applications

### Discovering Minimal Axioms

Use constraint testing to find minimal axiom sets:

1. **Start with all constraints active**
2. **Systematically remove constraints**
3. **Test if remaining constraints entail the removed one**
4. **Identify dependencies and redundancies**

```python
# Test if constraint C is entailed by constraints A and B
constraints = [A, B, Not(C)]
# If no model exists, then A ∧ B ⊢ C
```

This technique helps identify the logical core of a semantic theory.

### Comparing Constraint Systems

Compare how different constraint systems relate:

```python
# Do Fine's constraints entail Brast-McKie's?
def test_constraint_entailment():
    # Add Fine's constraints
    fine_constraints = [inclusion, actuality, incorporation, completeness]
    
    # Test if they entail a Brast-McKie property
    bm_property = ForAll([u, y, w],
        Implies(
            is_alternative(u, y, w),
            Exists([z], And(
                part(z, u),
                max_compatible_part(z, w, y)
            ))
        )
    )
    
    return fine_constraints + [Not(bm_property)]
```

This reveals logical relationships between different semantic frameworks.

## Troubleshooting

### Common Issues

**Timeouts with large N**:
- Start with N=3 or N=4 for initial tests
- Increase gradually only if no countermodel found
- Remember: small countermodels often suffice

**Unclear which constraint fails**:
- Test constraints individually first
- Use `--print-constraints` to see generated formulas
- Check `--print-z3` for raw solver output

**Settings not recognized**:
- Ensure setting is in `DEFAULT_GENERAL_SETTINGS`
- Check setting name matches exactly
- Verify theory initialization handles the setting

### Debugging Techniques

```bash
# See what constraints are generated
model-checker test.py --test_constraint --print-constraints

# Get detailed Z3 output
model-checker test.py --test_constraint --print-z3

# Try smaller state spaces
model-checker test.py --test_constraint --N=3
```

## References

### Implementation Examples
- **[Imposition Semantics](../../Code/src/model_checker/theory_lib/imposition/semantic.py)** - Complete `derive_imposition` implementation
- **[Frame Constraints Report](../../Code/src/model_checker/theory_lib/imposition/reports/imposition_comparison/frame_constraints.md)** - Detailed analysis of the methodology

### Related Documentation
- **[Theory Development](WORKFLOW.md#theory-development-workflow)** - Creating new theories
- **[Settings Guide](../../Code/src/model_checker/settings/README.md)** - Settings system details
- **[Z3 Integration](../../Code/src/model_checker/solver/README.md)** - Solver interface

### Theoretical Background
- **[Methodology](../methodology/README.md)** - ModelChecker's approach
- **[Semantic Properties](../methodology/SEMANTICS.md)** - Constraint types
- **[Model Theory](../methodology/MODELS.md)** - Finite model construction

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Theory Library →](../../Code/src/model_checker/theory_lib/README.md)
