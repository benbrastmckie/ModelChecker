# Imposition Comparison Reports

This directory contains technical analyses comparing Kit Fine's imposition-based semantics with Benjamin Brast-McKie's logos semantics for counterfactuals. The reports reveal fundamental differences in how these theories handle alternative world selection despite their shared foundation in state-based truthmaker semantics.

## Reports

### 1. Frame Constraints and Logical Independence

**Summary**: While the constructive definition `is_alternative` in the logos semantics automatically satisfies all frame constraints imposed on Fine's primitive imposition relation, the two theories generate logically independent counterfactual logics. The analysis reveals how primitive relations can "jump" to unrelated worlds in ways that violate minimal change intuitions.

**Key Findings**:

- The `is_alternative` relation automatically satisfies inclusion, actuality, incorporation, and completeness constraints
- Despite satisfying identical constraints, neither `(A □→ B) ⊢ (A □→_logos B)` nor `(A □→_logos B) ⊢ (A □→ B)` holds
- The primitive imposition relation permits "jumps" to unrelated worlds that satisfy constraints but violate minimal change

**Full Report**: [frame_constraints.md](frame_constraints.md)

### 2. Modal Definability via Counterfactuals

**Summary**: This analysis examines whether metaphysical necessity can be defined using counterfactual conditionals in each semantic framework. The results show that only the logos semantics supports such definitions, while the imposition semantics fails due to vacuous counterfactuals.

**Key Findings**:

- The imposition semantics cannot define □A via either ¬A □→ ⊥ or ⊤ □→ A due to vacuous truth
- The logos semantics validates both definitions up to N=6 with no countermodels
- The difference stems from how each theory handles alternative world generation

**Full Report**: [modals_defined.md](modals_defined.md)

## Related Resources

### Documentation

- [ModelChecker Workflow Guide](../../../../../Docs/usage/WORKFLOW.md) - Introduction to using the framework
- [Theory Comparison Guide](../../../../../Docs/usage/COMPARE_THEORIES.md) - Methodology for comparing semantic theories
- [Methodology Documentation](../../../../../Docs/methodology/README.md) - Philosophical foundations of programmatic semantics

### Theory Documentation

- [Imposition Theory](../../README.md) - Kit Fine's imposition semantics implementation
- [Logos Theory](../../../../logos/README.md) - Brast-McKie's hyperintensional semantics
- [Counterfactual Subtheory](../../../../logos/subtheories/counterfactual/README.md) - Logos counterfactual operators

### Data Files

- [imposition_comparison.json](imposition_comparison.json) - Complete test results and model structures

## Overview

These reports demonstrate that while Fine's imposition semantics and Brast-McKie's logos semantics share a common foundation in state-based truthmaker semantics, they embody fundamentally different approaches to counterfactual reasoning:

- **Imposition**: Treats frame constraints as complete specification, allowing any compliant relation
- **Logos**: Uses constraints as minimal requirements, adding philosophical content through constructive definition

The analyses reveal how structural equivalence at the constraint level can coexist with logical incomparability at the operational level, illuminating deep questions about the relationship between formal constraints and semantic behavior.
