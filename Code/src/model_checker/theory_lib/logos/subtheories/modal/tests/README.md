# Modal Subtheory Tests

This directory contains comprehensive tests for the Modal Subtheory of the Logos theory, covering all four modal operators: necessity (`\\Box`), possibility (`\\Diamond`), counterfactual necessity (`\\CFBox`), and counterfactual possibility (`\\CFDiamond`).

## Test Files

### test_modal_examples.py
**Purpose**: Integration tests that validate modal operators using modal logic examples

**Coverage**: 23 comprehensive examples testing modal reasoning
- **12 Countermodel Examples** (MOD_CM_*): Invalid arguments showing limits of modal logic
- **11 Theorem Examples** (MOD_TH_*): Valid arguments confirming modal principles

**Test Framework**: Uses parametrized testing with pytest to run all examples systematically

## Running Tests

### Basic Execution
```bash
# Run all modal tests
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py
```

### Specific Example Testing
```bash
# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py -k "MOD_CM_1"

# Run all countermodel examples
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py -k "MOD_CM"

# Run all theorem examples  
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py -k "MOD_TH"
```

### Integration with Project Testing
```bash
# Run via project test runner
python test_theories.py --theories logos --modal --examples

# Run specific modal examples via project runner
python test_theories.py --theories logos --examples MOD_CM_1 MOD_TH_5
```

## Test Categories

### Countermodel Examples (MOD_CM_*)
These tests validate that certain modal principles are **invalid** in the semantics:

| Example | Description | Tests |
|---------|-------------|-------|
| MOD_CM_1 | Necessitation of Contingent Truth | `A ⊢ □A` is invalid |
| MOD_CM_2 | S4 Principle | `□A → □□A` is invalid |
| MOD_CM_3 | S5 Principle | `◇A → □◇A` is invalid |
| MOD_CM_4 | Brouwer Principle | `A → □◇A` is invalid |
| MOD_CM_5 | Converse Barcan Formula | `∀x□Fx → □∀xFx` analogue is invalid |
| MOD_CM_6 | Modal Collapse | `◇A → A` is invalid |
| MOD_CM_7 | Necessity Distribution | `□(A ∨ B) → (□A ∨ □B)` is invalid |
| MOD_CM_8 | Possibility Conjunction | `(◇A ∧ ◇B) → ◇(A ∧ B)` is invalid |
| MOD_CM_9-12 | Complex Modal Failures | Various compound modal failures |

### Theorem Examples (MOD_TH_*)
These tests validate that core modal principles are **valid**:

| Example | Description | Tests |
|---------|-------------|-------|
| MOD_TH_1 | Necessitation Rule | If ⊢ A then ⊢ □A |
| MOD_TH_2 | Distribution Axiom | `□(A → B) → (□A → □B)` |
| MOD_TH_3 | Possibility Definition | `◇A ↔ ¬□¬A` |
| MOD_TH_4 | Necessity Implications | `□A → A` (T axiom) |
| MOD_TH_5 | Modal Modus Ponens | `□(A → B) ∧ □A ⊢ □B` |
| MOD_TH_6-7 | Operator Interactions | How □ and ◇ interact |
| MOD_TH_8-9 | Counterfactual Modal Operators | CFBox and CFDiamond properties |
| MOD_TH_10-11 | Complex Modal Validities | Multi-operator valid patterns |

## Test Structure

Each test follows the standard ModelChecker format:

```python
# Example: MOD_TH_4 - T Axiom (□A → A)
MOD_TH_4_premises = ['\\Box A']
MOD_TH_4_conclusions = ['A']
MOD_TH_4_settings = {
    'N': 3,                    # Number of atomic states
    'M': 3,                    # Additional constraint parameter
    'contingent': True,        # Require contingent propositions
    'disjoint': False,         # Allow overlapping content
    'max_time': 2,            # Solver timeout (seconds)
    'expectation': False,      # Expected result (False = valid)
}
```

### Settings Explanation
- **N**: Controls model size (modal logic typically needs moderate values)
- **M**: Additional parameter for modal structure constraints
- **contingent**: Whether atomic propositions must be contingent
- **disjoint**: Whether propositions must have disjoint subject matters
- **expectation**: Expected result (False for valid arguments, True for invalid)

## Test Dependencies

The modal tests load extensional and modal subtheories, plus counterfactual for CFBox/CFDiamond:

```python
# Dependency loading in test setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
```

**Dependencies**:
- **Extensional**: Required for basic logical operators used in modal examples
- **Modal**: The necessity/possibility operators being tested
- **Counterfactual**: Required for CFBox and CFDiamond operators (used in some modal examples)

## Modal Semantics

These tests validate the truthmaker semantics for modal operators:

### Standard Modal Operators

#### Necessity (□A)
**True** when: A is true at all alternative worlds accessible from the current world

#### Possibility (◇A)  
**True** when: A is true at some alternative world accessible from the current world

### Counterfactual Modal Operators

#### Counterfactual Necessity (CFBox A)
**True** when: A is true at all counterfactually accessible worlds

#### Counterfactual Possibility (CFDiamond A)
**True** when: A is true at some counterfactually accessible world

## Key Logical Properties Tested

### Valid Modal Principles
- **K Axiom**: □(A → B) → (□A → □B)
- **T Axiom**: □A → A (reflexivity)
- **Necessitation Rule**: If ⊢ A then ⊢ □A
- **Possibility Definition**: ◇A ↔ ¬□¬A
- **Modal Modus Ponens**: □(A → B) ∧ □A ⊢ □B

### Invalid Modal Principles
- **S4**: □A → □□A (not valid in all models)
- **S5**: ◇A → □◇A (not valid in all models)
- **Brouwer**: A → □◇A (not valid in all models)
- **Modal Collapse**: ◇A → A (would collapse modality)
- **Necessitation of Contingents**: A ⊢ □A (not valid for contingent A)

### Distribution Properties
- **Valid**: □(A ∧ B) ↔ (□A ∧ □B)
- **Valid**: ◇(A ∨ B) ↔ (◇A ∨ ◇B)
- **Invalid**: □(A ∨ B) → (□A ∨ □B)
- **Invalid**: (◇A ∧ ◇B) → ◇(A ∧ B)

## Debugging Failed Tests

When tests fail, check:

1. **Model Size**: Modal logic often needs N=3 or higher for countermodels
2. **Alternative Worlds**: Ensure sufficient world structure for modal operators
3. **Accessibility Relations**: Check if modal accessibility is properly constrained
4. **Dependencies**: Verify all required subtheories are loaded
5. **Modal Properties**: Confirm which modal axioms should/shouldn't hold

### Common Issues

- **Unexpected S4/S5 Validity**: The semantics may not validate these stronger axioms
- **Necessitation Problems**: Distinguish logical necessitation from material necessity
- **Accessibility Structure**: Some countermodels need specific world accessibility patterns
- **Counterfactual Interactions**: CFBox/CFDiamond may behave differently from standard modals

## Modal Logic Systems

The tests validate a modal logic that includes:

### Minimal Modal Logic (K)
- **K Axiom**: □(A → B) → (□A → □B)
- **Necessitation Rule**: If ⊢ A then ⊢ □A
- **Classical Base**: All propositional logic theorems

### Additional Principles
- **T Axiom**: □A → A (reflexivity)
- **Possibility-Necessity Duality**: ◇A ↔ ¬□¬A

### Non-Theorems
The semantics deliberately **does not** validate:
- **S4**: □A → □□A (transitivity)
- **S5**: ◇A → □◇A (Euclidean property)
- **B**: A → □◇A (symmetry)

This creates a hyperintensional modal logic suitable for the Logos framework.

## Integration with Logos Theory

These tests are part of the comprehensive Logos theory testing framework:

- **Foundation Layer**: Builds on extensional logic foundation
- **Unit Tests**: Located in `logos/tests/` for implementation testing
- **Integration Tests**: These subtheory tests validate end-to-end functionality
- **Cross-Theory Tests**: Located in `logos/tests/test_logos_examples.py`

For more information about modal logic and testing strategy, see:
- [Logos Theory README](../../README.md)
- [Logos Unit Testing Policy](../../UNIT_TESTS.md)
- [Modal Subtheory README](../README.md)