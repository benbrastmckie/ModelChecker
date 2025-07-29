# Theory Documentation Audit Report

This report identifies issues found in theory documentation files across the ModelChecker framework.

## 1. Formula Formatting Issues (Lowercase Letters)

### Logos Theory (`src/model_checker/theory_lib/logos/README.md`)

Found lowercase letters in formulas where capital letters should be used:

- **Line 57**: `["\\Box p"],` should be `["\\Box P"],`
- **Line 58**: `["p"]` should be `["P"]`
- **Line 61**: `["\\Diamond p"],` should be `["\\Diamond P"],`
- **Line 62**: `["\\Box p"]` should be `["\\Box P"]`
- **Line 65**: `["p \\leftrightarrow q"],` should be `["P \\leftrightarrow Q"],`
- **Line 66**: `["p \\equiv q"]` should be `["P \\equiv Q"]`
- **Line 215**: `p ∧ q` vs `q ∧ p` should be `P ∧ Q` vs `Q ∧ P`
- **Line 216**: `□p` vs `¬◇¬p` should be `□P` vs `¬◇¬P`
- **Line 217**: `p` vs `p ∨ (q ∧ ¬q)` should be `P` vs `P ∨ (Q ∧ ¬Q)`
- **Line 260**: `formula = "p \\rightarrow (q \\rightarrow p)"` should be `formula = "P \\rightarrow (Q \\rightarrow P)"`

### Bimodal Theory (`src/model_checker/theory_lib/bimodal/README.md`)

The bimodal theory correctly uses capital letters A, B, C in all documented formulas.

### Imposition Theory (`src/model_checker/theory_lib/imposition/README.md`)

The imposition theory correctly uses capital letters A, B, C in all documented formulas.

### Exclusion Theory (`src/model_checker/theory_lib/exclusion/README.md`)

The exclusion theory correctly uses capital letters A, B, C in all documented formulas.

## 2. Operator Count Discrepancies

### Logos Theory

Documentation claims **19 operators** across 5 subtheories:
- Primitive: 7 operators
- Defined: 12 operators

However, the operator count breakdown in the directory structure comment shows potential discrepancies that need verification against actual operator files.

### Imposition Theory

Documentation states **11 operators** total:
- Imposition-specific: 2 operators
- Inherited from Logos: 9 operators (7 extensional + 2 modal)

This needs verification against the actual operators.py file.

### Exclusion Theory

Documentation lists **4 operators**:
- Unilateral Negation (¬)
- Conjunction (∧)
- Disjunction (∨)
- Identity (≡)

This is consistent throughout the documentation.

### Bimodal Theory

The bimodal theory documentation does not provide a clear operator count summary in the overview section, which is inconsistent with other theories.

## 3. Example Count Discrepancies

### Logos Theory

Documentation claims **118 examples** total:
- Extensional: 14 examples
- Modal: 18 examples
- Constitutive: 33 examples
- Counterfactual: 33 examples
- Relevance: 20 examples

The examples.py file structure needs verification as direct grep patterns didn't find the expected structure.

### Imposition Theory

Documentation states **32 comprehensive test examples**:
- 21 Countermodels
- 11 Theorems

**ACTUAL COUNT FOUND**: 86 examples total
- 62 Countermodels (IM_CM_*)
- 24 Theorems (IM_TH_*)

This is a significant discrepancy - the documentation understates the actual examples by 54.

### Exclusion Theory

Documentation states **38 examples**:
- 22 Countermodels
- 16 Theorems

This needs verification against examples.py.

### Bimodal Theory

The bimodal theory documentation mentions examples but doesn't provide a clear count in the overview section.

## 4. Settings Documentation Issues

### Potential Issues to Verify:

1. **Imposition Theory**: Documents settings like 'contingent', 'non_empty', 'disjoint' - need to verify these are actually used in semantic.py

2. **Bimodal Theory**: Has unique settings 'M' and 'align_vertically' - these appear properly documented

3. **Settings references**: Some theories reference docs/SETTINGS.md files that need to be verified to exist

## 5. Academic Reference Issues

### Imposition Theory

References lack complete citation information:
- Line 193: "Fine, K. (2012). "Counterfactuals without Possible Worlds"" - missing publication details
- Line 194: "Fine, K. (2017). "Truthmaker Semantics"" - missing publication details

### Logos Theory

References are properly formatted with URLs and publication details.

### Exclusion Theory

References to Bernard and Champollion's work are mentioned but not formally cited in a references section.

## Summary of Findings

### Critical Issues Found:

1. **Formula Formatting**: Logos theory uses lowercase letters (p, q, r) in 10+ locations where capital letters (A, B, C) should be used according to ModelChecker standards.

2. **Example Count Discrepancy**: Imposition theory documentation claims 32 examples but actually has 86 examples (62 countermodels + 24 theorems).

3. **Incomplete References**: Imposition theory has incomplete academic citations for Fine's works.

4. **Operator Documentation**: Need to verify actual operator counts match documentation for all theories.

## Recommendations

1. **Immediate Fix - Formula Notation**: Update all lowercase letters (p, q, r) to capital letters (A, B, C) in the Logos theory documentation (lines 57, 58, 61, 62, 65, 66, 215, 216, 217, 260).

2. **Update Example Counts**: Update imposition theory README to reflect actual 86 examples (62 CM + 24 TH).

3. **Complete Citations**: Add full publication details for Fine (2012) and Fine (2017) references in imposition theory.

4. **Verify Operator Counts**: Audit actual operator implementations against documented counts for all theories.

5. **Standardize Documentation**: Ensure all theories have consistent overview sections with operator and example counts.

6. **Cross-Reference Validation**: Verify all docs/SETTINGS.md references exist and match implementation.