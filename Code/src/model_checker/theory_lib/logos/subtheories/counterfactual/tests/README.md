# Counterfactual Subtheory Tests

This directory contains comprehensive tests for the Counterfactual Subtheory of the Logos theory, covering all four counterfactual operators: counterfactual conditional (`\\boxright`), might counterfactual (`\\diamondright`), imposition (`\\imposition`), and might imposition (`\\could`).

## Test Files

### test_counterfactual_examples.py
**Purpose**: Integration tests that validate counterfactual operators using realistic hypothetical reasoning examples

**Coverage**: 33 comprehensive examples testing counterfactual reasoning
- **14 Countermodel Examples** (CF_CM_*): Invalid arguments showing limitations of counterfactual logic
- **19 Theorem Examples** (CF_TH_*): Valid arguments confirming counterfactual principles

**Test Framework**: Uses parametrized testing with pytest to run all examples systematically

## Running Tests

### Basic Execution
```bash
# Run all counterfactual tests
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py
```

### Specific Example Testing
```bash
# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_CM_1"

# Run all countermodel examples
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_CM"

# Run all theorem examples  
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_TH"
```

### Integration with Project Testing
```bash
# Run via project test runner
python test_theories.py --theories logos --counterfactual --examples

# Run specific counterfactual examples via project runner
python test_theories.py --theories logos --examples CF_CM_1 CF_TH_7
```

## Test Categories

### Countermodel Examples (CF_CM_*)
These tests validate that certain intuitive counterfactual principles are **invalid**:

| Example | Description | Tests |
|---------|-------------|-------|
| CF_CM_1 | Counterfactual Excluded Middle | `(A □→ B) ∨ (A □→ ¬B)` is invalid |
| CF_CM_2 | Antecedent Strengthening | `(A □→ C) → ((A ∧ B) □→ C)` is invalid |
| CF_CM_3 | Contraposition | `(A □→ B) → (¬B □→ ¬A)` is invalid |
| CF_CM_4 | Simplification of Disjunctive Consequent | Invalid simplification |
| CF_CM_5 | Hypothetical Syllogism | `(A □→ B) ∧ (B □→ C) → (A □→ C)` is invalid |
| CF_CM_6 | Import-Export | Counterfactuals don't satisfy import-export |
| CF_CM_7 | Agglomeration | Counterfactuals don't agglomerate |
| CF_CM_8-9 | Factivity | Counterfactuals are not factive |
| CF_CM_10-14 | Complex Interaction Failures | Various compound failures |

### Theorem Examples (CF_TH_*)
These tests validate that key counterfactual principles are **valid**:

| Example | Description | Tests |
|---------|-------------|-------|
| CF_TH_1 | Counterfactual Modus Ponens | `A ∧ (A □→ B) ⊢ B` |
| CF_TH_2 | Reflexivity | `A □→ A` is valid |
| CF_TH_3-4 | Operator Interactions | How □→ and ◇→ relate |
| CF_TH_5 | Conjunction in Consequent | Valid conjunction principles |
| CF_TH_6-7 | Imposition Relations | Valid imposition principles |
| CF_TH_8-9 | Necessity Interactions | How counterfactuals interact with □ |
| CF_TH_10-15 | Semantic Principles | Core counterfactual validities |
| CF_TH_16-19 | Complex Validities | Multi-operator valid patterns |

## Test Structure

Each test follows the standard ModelChecker format:

```python
# Example: CF_TH_1 - Counterfactual Modus Ponens
CF_TH_1_premises = ['A', '(A \\boxright B)']
CF_TH_1_conclusions = ['B']
CF_TH_1_settings = {
    'N': 3,                    # Number of atomic states
    'M': 3,                    # Additional constraint parameter
    'contingent': True,        # Require contingent propositions
    'disjoint': False,         # Allow overlapping content
    'max_time': 3,            # Solver timeout (seconds)
    'expectation': False,      # Expected result (False = valid)
}
```

### Settings Explanation
- **N**: Controls model size (counterfactuals often need larger values)
- **M**: Additional parameter for alternative world constraints
- **contingent**: Whether atomic propositions must be contingent
- **disjoint**: Whether propositions must have disjoint subject matters
- **expectation**: Expected result (False for valid arguments, True for invalid)

## Test Dependencies

The counterfactual tests automatically load required operator dependencies:

```python
# Automatic dependency loading in test setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
```

**Dependencies**:
- **Extensional**: Required for basic logical operators (conjunction, negation, etc.)
- **Modal**: Required for necessity/possibility operators that interact with counterfactuals
- **Counterfactual**: The operators being tested

## Counterfactual Semantics

These tests validate the verification semantics for counterfactuals:

### Counterfactual Conditional (A □→ B)
**True** when: For all A-verifiers x and alternative worlds u to x, B is true at u

### Might Counterfactual (A ◇→ B)  
**True** when: For some A-verifier x and alternative world u to x, B is true at u

### Imposition (A ⇒ B)
**True** when: A imposes B according to Fine's semantics

### Might Imposition (A ⋄⇒ B)
**True** when: A could impose B in some circumstances

## Key Logical Properties Tested

### Valid Principles
- **Reflexivity**: A □→ A
- **Modus Ponens**: A ∧ (A □→ B) ⊢ B  
- **Operator Duality**: ¬(A ◇→ B) ↔ (A □→ ¬B)
- **Necessity Interaction**: □A → (B □→ A)

### Invalid Principles
- **Antecedent Strengthening**: (A □→ C) → ((A ∧ B) □→ C)
- **Contraposition**: (A □→ B) → (¬B □→ ¬A)
- **Hypothetical Syllogism**: (A □→ B) ∧ (B □→ C) → (A □→ C)
- **Excluded Middle**: (A □→ B) ∨ (A □→ ¬B)

## Debugging Failed Tests

When tests fail, check:

1. **Model Size**: Counterfactuals often need larger N/M values than other operators
2. **Timeout**: Complex counterfactual reasoning may need longer timeouts
3. **Alternative Worlds**: Ensure sufficient alternative world structure
4. **Dependencies**: Verify modal operators are loaded for interaction tests
5. **Contingency**: Some examples require contingent vs. non-contingent propositions

### Common Issues

- **Timeout Errors**: Counterfactuals are computationally expensive; increase `max_time`
- **Model Complexity**: Use N=4 or higher for complex counterfactual examples
- **Alternative Worlds**: Some countermodels need specific alternative world structures
- **Operator Loading**: Ensure modal subtheory is loaded for necessity interactions

## Integration with Logos Theory

These tests are part of the comprehensive Logos theory testing framework:

- **Unit Tests**: Located in `logos/tests/` for implementation testing
- **Integration Tests**: These subtheory tests validate end-to-end functionality
- **Cross-Theory Tests**: Located in `logos/tests/test_logos_examples.py`

For more information about counterfactual logic and testing strategy, see:
- [Logos Theory README](../../README.md)
- [Logos Unit Testing Policy](../../UNIT_TESTS.md)
- [Counterfactual Subtheory README](../README.md)
- [Paper](https://link.springer.com/article/10.1007/s10992-025-09793-8)
