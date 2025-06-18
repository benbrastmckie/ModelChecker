# Constitutive Subtheory Tests

This directory contains comprehensive tests for the Constitutive Subtheory of the Logos theory, covering all five constitutive operators: identity (`\\equiv`), ground (`\\leq`), essence (`\\sqsubseteq`), relevance (`\\preceq`), and reduction (`\\Rightarrow`).

## Test Files

### test_constitutive_examples.py
**Purpose**: Integration tests that validate constitutive operators using realistic logical examples

**Coverage**: 33 comprehensive examples testing constitutive relationships
- **14 Countermodel Examples** (CL_CM_*): Invalid arguments demonstrating where classical principles fail
- **19 Theorem Examples** (CL_TH_*): Valid arguments confirming hyperintensional principles

**Test Framework**: Uses parametrized testing with pytest to run all examples systematically

## Running Tests

### Basic Execution
```bash
# Run all constitutive tests
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py
```

### Specific Example Testing
```bash
# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM_1"

# Run all countermodel examples
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM"

# Run all theorem examples  
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_TH"
```

### Integration with Project Testing
```bash
# Run via project test runner
python test_theories.py --theories logos --constitutive --examples

# Run specific constitutive examples via project runner
python test_theories.py --theories logos --examples CL_CM_1 CL_TH_7
```

## Test Categories

### Countermodel Examples (CL_CM_*)
These tests validate that certain classical principles are **invalid** in hyperintensional logic:

| Example | Description | Tests |
|---------|-------------|-------|
| CL_CM_1 | Equivalence of Tautologies | `(A ∨ ¬A) ≡ (B ∨ ¬B)` is invalid |
| CL_CM_2 | Equivalence of Contradictions | `(A ∧ ¬A) ≡ (B ∧ ¬B)` is invalid |
| CL_CM_3 | Ground Conjunction Supplementation | Invalid classical supplementation |
| CL_CM_4 | Essence Disjunction Supplementation | Invalid classical supplementation |
| CL_CM_5-6 | Identity Absorption Laws | Classical absorption fails for identity |
| CL_CM_7-8 | Identity Distribution Laws | Classical distribution fails for identity |
| CL_CM_9 | Strict Implication to Ground | `□(A → B)` doesn't imply `A ≤ B` |
| CL_CM_10 | Strict Implication to Essence | `□(A → B)` doesn't imply `A ⊑ B` |
| CL_CM_11-12 | Content Relation Distribution | Ground/essence don't distribute |
| CL_CM_13-14 | Shannon Expansion | Shannon laws fail for identity |

### Theorem Examples (CL_TH_*)
These tests validate that hyperintensional principles are **valid**:

| Example | Description | Tests |
|---------|-------------|-------|
| CL_TH_1-2 | Ground-Essence Interconversion | `A ≤ B ⟷ ¬A ⊑ ¬B` |
| CL_TH_3-6 | Identity Interactions | How identity relates to ground/essence |
| CL_TH_7-8 | Negation Transparency | `A ≡ B → ¬A ≡ ¬B` |
| CL_TH_9-13 | Absorption/Distribution Reductions | Valid absorption patterns |
| CL_TH_14-15 | Strict Implication | Ground/essence imply strict implication |
| CL_TH_16-17 | Anti-symmetry Principles | Ground/essence anti-symmetry |
| CL_TH_18-19 | Transitivity Principles | Transitivity of content relations |

## Test Structure

Each test follows the standard ModelChecker format:

```python
# Example: CL_TH_16 - Grounding Anti-symmetry
CL_TH_16_premises = ['(A \\leq B)', '(B \\leq A)']
CL_TH_16_conclusions = ['(A \\equiv B)']
CL_TH_16_settings = {
    'N': 2,                    # Number of atomic states
    'M': 2,                    # Additional constraint parameter
    'contingent': False,       # Allow non-contingent propositions
    'disjoint': False,         # Allow overlapping content
    'max_time': 2,            # Solver timeout (seconds)
    'expectation': False,      # Expected result (False = valid)
}
```

### Settings Explanation
- **N**: Controls model size (smaller values often sufficient for constitutive logic)
- **M**: Additional parameter for complex semantic constraints
- **contingent**: Whether atomic propositions must be contingent
- **disjoint**: Whether propositions must have disjoint subject matters
- **expectation**: Expected result (False for valid arguments, True for invalid)

## Test Dependencies

The constitutive tests automatically load required operator dependencies:

```python
# Automatic dependency loading in test setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional', 'modal', 'constitutive'])
```

**Dependencies**:
- **Extensional**: Required for conjunction operator used in reduction
- **Modal**: Required for some examples involving necessity
- **Constitutive**: The operators being tested

## Debugging Failed Tests

When tests fail, check:

1. **Example Logic**: Verify the logical argument is correct
2. **Settings**: Ensure N, M values provide sufficient model space
3. **Dependencies**: Confirm all required subtheories are loaded
4. **Timeout**: Increase `max_time` for complex examples
5. **Expectation**: Verify the expected result matches the logical validity

### Common Issues

- **Timeout Errors**: Increase `max_time` or reduce N/M values
- **Import Errors**: Check that all required operators are available
- **Assertion Failures**: Verify example logic matches expected result
- **Model Size**: Some examples need larger N values for countermodels

## Integration with Logos Theory

These tests are part of the comprehensive Logos theory testing framework:

- **Unit Tests**: Located in `logos/tests/` for implementation testing
- **Integration Tests**: These subtheory tests validate end-to-end functionality
- **Cross-Theory Tests**: Located in `logos/tests/test_logos_examples.py`

For more information about the overall testing strategy, see:
- [Logos Theory README](../../README.md)
- [Logos Unit Testing Policy](../../UNIT_TESTS.md)
- [Constitutive Subtheory README](../README.md)