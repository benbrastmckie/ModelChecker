# Extensional Subtheory Tests

This directory contains comprehensive tests for the Extensional Subtheory of the Logos theory, covering all seven truth-functional operators: negation (`\\neg`), conjunction (`\\wedge`), disjunction (`\\vee`), conditional (`\\rightarrow`), biconditional (`\\leftrightarrow`), top (`\\top`), and bottom (`\\bot`).

## Test Files

### test_extensional_examples.py
**Purpose**: Integration tests that validate extensional operators using classical propositional logic examples

**Coverage**: 14 comprehensive examples testing truth-functional reasoning
- **7 Countermodel Examples** (EXT_CM_*): Invalid arguments showing limits of truth-functional logic
- **7 Theorem Examples** (EXT_TH_*): Valid arguments confirming classical propositional principles

**Test Framework**: Uses parametrized testing with pytest to run all examples systematically

## Running Tests

### Basic Execution
```bash
# Run all extensional tests
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py
```

### Specific Example Testing
```bash
# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_CM_1"

# Run all countermodel examples
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_CM"

# Run all theorem examples  
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_TH"
```

### Integration with Project Testing
```bash
# Run via project test runner
python test_theories.py --theories logos --extensional --examples

# Run specific extensional examples via project runner
python test_theories.py --theories logos --examples EXT_CM_1 EXT_TH_1
```

## Test Categories

### Countermodel Examples (EXT_CM_*)
These tests validate that certain invalid arguments remain **invalid** in the extensional fragment:

| Example | Description | Tests |
|---------|-------------|-------|
| EXT_CM_1 | Affirming the Consequent | `(A → B) ∧ B ⊢ A` is invalid |
| EXT_CM_2 | Denying the Antecedent | `(A → B) ∧ ¬A ⊢ ¬B` is invalid |
| EXT_CM_3 | Conjunction Introduction Error | Invalid conjunction introduction |
| EXT_CM_4 | Disjunction Elimination Error | Invalid disjunction elimination |
| EXT_CM_5 | Biconditional Misuse | Invalid biconditional reasoning |
| EXT_CM_6 | Material Conditional Confusion | Invalid conditional reasoning |
| EXT_CM_7 | Truth-Value Assignment Error | Invalid truth-functional reasoning |

### Theorem Examples (EXT_TH_*)
These tests validate that classical propositional principles are **valid**:

| Example | Description | Tests |
|---------|-------------|-------|
| EXT_TH_1 | Modus Ponens | `(A → B) ∧ A ⊢ B` |
| EXT_TH_2 | Modus Tollens | `(A → B) ∧ ¬B ⊢ ¬A` |
| EXT_TH_3 | Disjunctive Syllogism | `(A ∨ B) ∧ ¬A ⊢ B` |
| EXT_TH_4 | Hypothetical Syllogism | `(A → B) ∧ (B → C) ⊢ (A → C)` |
| EXT_TH_5 | Conjunction Elimination | `(A ∧ B) ⊢ A` |
| EXT_TH_6 | Addition (Disjunction Introduction) | `A ⊢ (A ∨ B)` |
| EXT_TH_7 | Law of Excluded Middle | `⊢ (A ∨ ¬A)` |

## Test Structure

Each test follows the standard ModelChecker format:

```python
# Example: EXT_TH_1 - Modus Ponens
EXT_TH_1_premises = ['(A \\rightarrow B)', 'A']
EXT_TH_1_conclusions = ['B']
EXT_TH_1_settings = {
    'N': 2,                    # Number of atomic states
    'M': 2,                    # Additional constraint parameter
    'contingent': True,        # Require contingent propositions
    'disjoint': False,         # Allow overlapping content
    'max_time': 1,            # Solver timeout (seconds)
    'expectation': False,      # Expected result (False = valid)
}
```

### Settings Explanation
- **N**: Controls model size (extensional logic typically needs small values)
- **M**: Additional parameter (usually minimal for truth-functional logic)
- **contingent**: Whether atomic propositions must be contingent
- **disjoint**: Whether propositions must have disjoint subject matters
- **expectation**: Expected result (False for valid arguments, True for invalid)

## Test Dependencies

The extensional tests load only the extensional subtheory:

```python
# Minimal dependency loading in test setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional'])
```

**Dependencies**:
- **Extensional**: Only the truth-functional operators being tested
- **No Modal Dependencies**: Extensional tests are self-contained
- **No Constitutive Dependencies**: No content-based operators needed

## Truth-Functional Semantics

These tests validate the classical truth-functional semantics:

### Basic Operators
- **Negation** (`¬A`): True when A is false
- **Conjunction** (`A ∧ B`): True when both A and B are true
- **Disjunction** (`A ∨ B`): True when at least one of A or B is true
- **Conditional** (`A → B`): False only when A is true and B is false
- **Biconditional** (`A ↔ B`): True when A and B have the same truth value

### Constants
- **Top** (`⊤`): Always true
- **Bottom** (`⊥`): Always false

## Key Logical Properties Tested

### Valid Inference Rules
- **Modus Ponens**: A → B, A ⊢ B
- **Modus Tollens**: A → B, ¬B ⊢ ¬A
- **Disjunctive Syllogism**: A ∨ B, ¬A ⊢ B
- **Hypothetical Syllogism**: A → B, B → C ⊢ A → C
- **Conjunction Elimination**: A ∧ B ⊢ A, B
- **Disjunction Introduction**: A ⊢ A ∨ B

### Valid Logical Laws
- **Law of Excluded Middle**: ⊢ A ∨ ¬A
- **Law of Non-Contradiction**: ⊢ ¬(A ∧ ¬A)
- **Double Negation**: A ↔ ¬¬A
- **De Morgan's Laws**: ¬(A ∧ B) ↔ (¬A ∨ ¬B)
- **Commutative Laws**: A ∧ B ↔ B ∧ A, A ∨ B ↔ B ∨ A

### Invalid Patterns
- **Affirming the Consequent**: A → B, B ⊬ A
- **Denying the Antecedent**: A → B, ¬A ⊬ ¬B
- **Converse Fallacy**: A → B ⊬ B → A
- **Inverse Fallacy**: A → B ⊬ ¬A → ¬B

## Debugging Failed Tests

When tests fail, check:

1. **Truth Tables**: Verify the expected truth-functional behavior
2. **Model Size**: N=2 is usually sufficient for extensional logic
3. **Operator Loading**: Ensure only extensional operators are loaded
4. **Settings**: Most extensional tests use simple settings
5. **Expected Results**: Verify countermodel/validity expectations

### Common Issues

- **Unexpected Validity**: Check if argument is actually classically valid
- **Unexpected Invalidity**: Verify the logical form is correct
- **Import Errors**: Ensure extensional operators are available
- **Timeout**: Extensional tests should complete quickly (max_time=1)

## Classical Logic Foundation

The extensional subtheory serves as the foundation for all other Logos subtheories:

### Dependency Relationship
- **Modal operators** depend on extensional operators for definitions
- **Constitutive operators** use conjunction and negation
- **Counterfactual operators** build on extensional and modal operators

### Truth-Functional Base
- Provides classical propositional logic foundation
- Establishes truth-functional semantics
- Validates basic inference rules
- Confirms classical logical laws

## Integration with Logos Theory

These tests are part of the comprehensive Logos theory testing framework:

- **Foundation Tests**: Extensional tests validate the logical foundation
- **Unit Tests**: Located in `logos/tests/` for implementation testing
- **Integration Tests**: These subtheory tests validate end-to-end functionality
- **Cross-Theory Tests**: Located in `logos/tests/test_logos_examples.py`

For more information about the extensional foundation and testing strategy, see:
- [Logos Theory README](../../README.md)
- [Logos Unit Testing Policy](../../UNIT_TESTS.md)
- [Extensional Subtheory README](../README.md)