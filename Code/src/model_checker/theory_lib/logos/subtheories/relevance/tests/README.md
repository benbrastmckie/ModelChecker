# Relevance Subtheory Tests

This directory contains comprehensive tests for the Relevance Subtheory of the Logos theory, which extends the constitutive operators with relevance-sensitive logical principles and refined content relationships.

## Test Files

### test_relevance_examples.py
**Purpose**: Integration tests that validate relevance-sensitive operators and their interactions with constitutive logic

**Coverage**: 20 comprehensive examples testing relevance-based reasoning
- **10 Countermodel Examples** (REL_CM_*): Invalid arguments showing limits of relevance logic
- **10 Theorem Examples** (REL_TH_*): Valid arguments confirming relevance principles

**Test Framework**: Uses parametrized testing with pytest to run all examples systematically

## Running Tests

### Basic Execution
```bash
# Run all relevance tests
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py
```

### Specific Example Testing
```bash
# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM_1"

# Run all countermodel examples
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM"

# Run all theorem examples  
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_TH"
```

### Integration with Project Testing
```bash
# Run via project test runner
python test_theories.py --theories logos --relevance --examples

# Run specific relevance examples via project runner
python test_theories.py --theories logos --examples REL_CM_1 REL_TH_5
```

## Test Categories

### Countermodel Examples (REL_CM_*)
These tests validate that certain relevance principles are **invalid** or have counterexamples:

| Example | Description | Tests |
|---------|-------------|-------|
| REL_CM_1 | Irrelevant Antecedent | Relevance doesn't allow irrelevant premises |
| REL_CM_2 | Paradoxes of Material Implication | Material conditional paradoxes |
| REL_CM_3 | Explosion (Ex Falso) | From contradiction, anything doesn't follow |
| REL_CM_4 | Disjunctive Syllogism Failure | DS fails with irrelevant disjuncts |
| REL_CM_5 | Addition (Disjunction Intro) Failure | Addition fails with irrelevant disjuncts |
| REL_CM_6 | Weakening Failure | Cannot add irrelevant premises |
| REL_CM_7 | Contraction Issues | Relevance restrictions on contraction |
| REL_CM_8-10 | Complex Relevance Failures | Multi-operator relevance violations |

### Theorem Examples (REL_TH_*)
These tests validate that relevance-respecting principles are **valid**:

| Example | Description | Tests |
|---------|-------------|-------|
| REL_TH_1 | Relevant Modus Ponens | MP with content connection |
| REL_TH_2 | Relevant Conjunction | Conjunction with shared content |
| REL_TH_3 | Relevant Disjunction | Disjunction with content overlap |
| REL_TH_4 | Relevant Implication | Implication with content connection |
| REL_TH_5 | Content Transitivity | Relevance transitivity properties |
| REL_TH_6-7 | Relevance-Essence Interaction | How relevance relates to essence |
| REL_TH_8-9 | Relevance-Ground Interaction | How relevance relates to ground |
| REL_TH_10 | Complex Relevance Validity | Multi-operator relevant reasoning |

## Test Structure

Each test follows the standard ModelChecker format:

```python
# Example: REL_TH_1 - Relevant Modus Ponens
REL_TH_1_premises = ['(A \\preceq (A \\rightarrow B))', '(A \\rightarrow B)', 'A']
REL_TH_1_conclusions = ['B']
REL_TH_1_settings = {
    'N': 3,                    # Number of atomic states
    'M': 3,                    # Additional constraint parameter
    'contingent': True,        # Require contingent propositions
    'disjoint': False,         # Allow overlapping content
    'max_time': 3,            # Solver timeout (seconds)
    'expectation': False,      # Expected result (False = valid)
}
```

### Settings Explanation
- **N**: Controls model size (relevance logic often needs moderate to larger values)
- **M**: Additional parameter for content relationship constraints
- **contingent**: Whether atomic propositions must be contingent
- **disjoint**: Whether propositions must have disjoint subject matters
- **expectation**: Expected result (False for valid arguments, True for invalid)

## Test Dependencies

The relevance tests load all subtheories for comprehensive relevance testing:

```python
# Comprehensive dependency loading in test setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional', 'modal', 'constitutive', 'relevance'])
```

**Dependencies**:
- **Extensional**: Required for basic logical operators
- **Modal**: Required for necessity/possibility interactions
- **Constitutive**: Required for ground, essence, identity operators
- **Relevance**: The relevance operators and principles being tested

## Relevance Semantics

These tests validate the relevance-sensitive semantics:

### Relevance Relation (A ⪯ B)
**True** when: A is relevant to B (shares content or subject matter)

### Relevance-Sensitive Logical Principles

#### Relevant Implication
Implication requires content connection between antecedent and consequent

#### Content Overlap
Logical operations must respect content relationships

#### Anti-Explosion
From a contradiction, only relevant consequences follow

### Integration with Constitutive Operators

#### Relevance as Weakest Relation
- Ground implies relevance: A ≤ B → A ⪯ B
- Essence implies relevance: A ⊑ B → A ⪯ B
- Identity implies relevance: A ≡ B → A ⪯ B

## Key Logical Properties Tested

### Valid Relevance Principles
- **Reflexivity**: A ⪯ A
- **Variable Sharing**: If A and B share propositional variables, then A ⪯ B
- **Content Transitivity**: Relevance transitivity under content conditions
- **Constitutive Implication**: Ground/essence/identity imply relevance

### Invalid Classical Principles (In Relevance Logic)
- **Ex Falso Quodlibet**: ⊥ ⊢ A (not valid for irrelevant A)
- **Paradoxes of Material Implication**: A ⊢ (B → A) fails for irrelevant B
- **Weakening**: A ⊢ (B → A) fails for irrelevant B
- **Disjunctive Syllogism**: (A ∨ B) ∧ ¬A ⊢ B fails for irrelevant A, B

### Relevance-Restricted Valid Principles
- **Relevant Modus Ponens**: If A ⪯ (A → B), then (A → B) ∧ A ⊢ B
- **Relevant Addition**: If A ⪯ B, then A ⊢ (A ∨ B)
- **Relevant Conjunction**: If A ⪯ B, then A ∧ B follows relevant principles

## Content-Based Reasoning

The relevance subtheory enforces content-based constraints:

### Topic Preservation
- Premises and conclusions must share content
- No derivation of completely unrelated conclusions
- Content connection through relevance relation

### Subject Matter Constraints
- Logical operations respect subject matter boundaries
- Invalid to mix unrelated content domains
- Relevance mediates between different topics

### Hyperintensional Content
- Relevance distinguishes content-equivalent but topic-distinct formulas
- More fine-grained than classical logical equivalence
- Sensitive to propositional aboutness and topicality

## Debugging Failed Tests

When tests fail, check:

1. **Content Relationships**: Verify relevance connections are properly established
2. **Model Size**: Relevance logic often needs larger N values for complex content structures
3. **Operator Dependencies**: Ensure all constitutive operators are available
4. **Relevance Constraints**: Check if content overlap conditions are met
5. **Variable Sharing**: Confirm propositional variable relationships

### Common Issues

- **Content Isolation**: Some examples require careful content separation
- **Relevance Transitivity**: Complex relevance chains may need larger models
- **Operator Interactions**: Ensure constitutive and modal operators work with relevance
- **Subject Matter**: Disjoint vs. overlapping content affects relevance validity

## Philosophical Motivation

The relevance subtheory addresses key problems in classical logic:

### Paradoxes of Material Implication
- "If the moon is made of cheese, then 2+2=4" is classically valid but intuitively wrong
- Relevance logic requires content connection for valid implication

### Ex Falso Quodlibet
- "From a contradiction, anything follows" is classically valid but problematic
- Relevance logic restricts explosion to relevant consequences

### Weakening and Irrelevance
- Classical logic allows adding irrelevant premises
- Relevance logic maintains content discipline

## Integration with Logos Theory

These tests are part of the comprehensive Logos theory testing framework:

- **Advanced Layer**: Builds on extensional, modal, and constitutive foundations
- **Unit Tests**: Located in `logos/tests/` for implementation testing
- **Integration Tests**: These subtheory tests validate end-to-end functionality
- **Cross-Theory Tests**: Located in `logos/tests/test_logos_examples.py`

For more information about relevance logic and testing strategy, see:
- [Logos Theory README](../../README.md)
- [Logos Unit Testing Policy](../../UNIT_TESTS.md)
- [Relevance Subtheory README](../README.md)
- [Constitutive Subtheory README](../constitutive/README.md)