# Relevance Logic Notebooks

Interactive Jupyter notebooks demonstrating relevance logic and its relationship with constitutive operators within the Logos semantic framework.

## Overview

This directory contains notebooks that explore **relevance logic** - the study of genuine connections between propositions that avoids the paradoxes of material and strict implication. These notebooks provide hands-on examples showing how relevance relates to grounding, essence, and identity through model checking.

## Available Notebooks

### relevance_examples.ipynb
**Comprehensive introduction to the relevance operator** with interactive examples demonstrating:
- Antecedent strengthening failure (countermodel)
- Relevance to ground connection through conjunction (theorem)
- Strict implication vs relevance (countermodel)
- Grounding implies relevance (theorem)

## Key Concepts

### Relevance and Related Operators
- **Relevance (≼)**: `\\preceq` - When propositions are genuinely connected
- **Ground (≤)**: `\\leq` - When one proposition makes another true
- **Essence (⊑)**: `\\sqsubseteq` - When one proposition is part of another's nature
- **Identity (≡)**: `\\equiv` - Constitutive sameness of content

### LaTeX Notation Reference
All formulas in code cells use LaTeX notation:
- `\\preceq` for ≼ (relevance)
- `\\leq` for ≤ (ground)
- `\\sqsubseteq` for ⊑ (essence)
- `\\equiv` for ≡ (identity)
- `\\Box` for □ (necessity)
- `\\rightarrow` for → (implication)
- `\\wedge` for ∧ (conjunction)
- `\\vee` for ∨ (disjunction)
- `\\neg` for ¬ (negation)

## Running the Notebooks

### Quick Start
```bash
# From project root
./run_jupyter.sh

# Navigate to:
src/model_checker/theory_lib/logos/subtheories/relevance/notebooks/

# Open relevance_examples.ipynb
```

### Interactive Usage
1. Run all cells to load the theory and see examples
2. Modify parameters to explore different model constraints
3. Create your own test cases to test relevance principles
4. Examine countermodels to understand why certain implications fail

## Learning Path

### For Beginners
1. Start with the overview to understand relevance logic motivation
2. Run the antecedent strengthening example to see non-monotonicity
3. Explore how relevance connects to grounding
4. Compare relevance with strict implication

### For Advanced Users
1. Examine the detailed countermodel structures
2. Explore the hierarchy: grounding → relevance
3. Test complex formulas involving multiple operators
4. Investigate connections with relevant implication

## Key Insights

### Invalid Principles (Countermodels)
- **Antecedent Strengthening**: Adding conjuncts can destroy relevance
- **Strict Implication**: Necessary connection doesn't ensure relevance
- **Transitivity Issues**: Relevance may fail transitivity

### Valid Principles (Theorems)
- **Relevance to Ground**: Relevance plus conjunction yields grounding
- **Hierarchy**: Grounding implies relevance (but not vice versa)
- **Identity Connection**: Identity implies relevance

## Related Resources

- [Relevance Examples Module](../examples.py) - Source code for all examples
- [Main Relevance README](../README.md) - Theoretical background
- [Constitutive Notebooks](../../constitutive/notebooks/) - Related operators
- [Logos Theory Overview](../../README.md) - Complete framework documentation

## Technical Notes

- All examples use the Logos semantic framework with Z3 constraint solving
- The relevance operator requires careful model construction to avoid trivial satisfaction
- Countermodels reveal why classical implication paradoxes fail with relevance
- Parameters can be adjusted to explore different model sizes and constraints

## Applications

Relevance logic principles demonstrated here are crucial for:
- Avoiding explosion in inconsistent theories
- Ensuring genuine premise-conclusion connections
- Modeling information flow and dependence
- Building relevant entailment systems