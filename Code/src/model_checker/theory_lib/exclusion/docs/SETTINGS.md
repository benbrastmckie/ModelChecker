# Exclusion Theory Settings Documentation

This document provides comprehensive documentation for all settings available in the exclusion theory implementation, explaining their purpose, usage, and impact on model construction and semantics.

## Overview

The exclusion theory extends the ModelChecker framework with witness-aware semantics for unilateral negation. Settings control various aspects of model construction, from basic constraints to advanced iteration behavior.

## Setting Categories

### Example Settings

These settings control model generation for specific examples and are defined in `DEFAULT_EXAMPLE_SETTINGS`:

#### Core Settings

**`N` (integer, default: 3)**
- **Purpose**: Number of atomic propositions in the model
- **Impact**: Determines the size of the state space (2^N possible states)
- **Usage**: Keep small (2-4) for manageable computation, especially with complex exclusion relations
- **Example**: `'N': 3` creates 8 possible states (including empty state)

**`max_time` (integer, default: 1)**
- **Purpose**: Maximum solver execution time in seconds
- **Impact**: Prevents infinite loops, controls Z3 solver timeout
- **Usage**: Increase for complex examples that need more solving time
- **Example**: `'max_time': 5` allows 5 seconds for solving

**`expectation` (boolean/None, default: None)**
- **Purpose**: Expected model existence for testing
- **Impact**: Used in test suites to verify expected outcomes
- **Values**: 
  - `True`: Expect a model to exist
  - `False`: Expect no model (unsat)
  - `None`: No expectation (exploratory mode)

#### Semantic Constraints

**`possible` (boolean, default: False)**
- **Purpose**: Restrict models to only possible states
- **Impact**: When True, excludes impossible states from consideration
- **Usage**: Usually False in exclusion theory to allow exploration of exclusion patterns
- **Note**: Interacts with coherence and conflict detection

**`contingent` (boolean, default: False)**
- **Purpose**: Make atomic propositions contingent
- **Impact**: Requires each atom to be both satisfied and unsatisfied by some states
- **Usage**: Creates more diverse models, prevents trivial solutions
- **Example**: With `contingent: True`, atom 'p' must have both verifiers and non-verifiers

**`non_empty` (boolean, default: False)**
- **Purpose**: Require atomic propositions to have at least one verifier
- **Impact**: Prevents atoms from being vacuously false everywhere
- **Usage**: Useful for ensuring meaningful semantic content
- **Constraint**: `∃state. verify(state, atom)`

**`non_null` (boolean, default: False)**
- **Purpose**: Prevent null state from verifying atoms
- **Impact**: The empty state (∅) cannot verify any atomic proposition
- **Usage**: Forces non-trivial verification patterns
- **Constraint**: `¬verify(∅, atom)`

**`disjoint` (boolean, default: False)**
- **Purpose**: Make atomic propositions have disjoint verifier sets
- **Impact**: No state can verify two different atoms
- **Usage**: Creates clear separation between propositions
- **Constraint**: `∀state. ¬(verify(state, p) ∧ verify(state, q))` for p ≠ q

**`fusion_closure` (boolean, default: False)**
- **Purpose**: Apply fusion closure to verification
- **Impact**: If states verify an atom, their fusion also verifies it
- **Usage**: Creates upward-closed verification sets
- **Note**: Not commonly used in exclusion theory examples

#### Iteration Settings

**`iterate` (integer, default: 1)**
- **Purpose**: Number of distinct models to find
- **Impact**: Triggers model iteration to find multiple valid models
- **Usage**: Set > 1 to explore semantic diversity
- **Example**: `'iterate': 3` finds 3 distinct models with different exclusion patterns

**`iteration_timeout` (float, default: 1.0)**
- **Purpose**: Timeout for isomorphism checking between models (seconds)
- **Impact**: Controls how long to check if two models are equivalent
- **Usage**: Increase for complex exclusion patterns that need careful comparison
- **Example**: `'iteration_timeout': 2.5` allows more thorough equivalence checking

**`iteration_attempts` (integer, default: 5)**
- **Purpose**: Maximum attempts to find a non-isomorphic model
- **Impact**: How many times to retry when finding duplicate models
- **Usage**: Increase when models tend to be similar
- **Example**: `'iteration_attempts': 8` for challenging exclusion examples

### General Settings

These settings control output and debugging behavior, defined in `DEFAULT_GENERAL_SETTINGS`:

**`print_impossible` (boolean, default: False)**
- **Purpose**: Include impossible states in output
- **Impact**: Shows states that violate possibility constraints
- **Usage**: Helpful for debugging exclusion and conflict patterns
- **Example**: Shows grayed-out impossible states in model display

**`print_constraints` (boolean, default: False)**
- **Purpose**: Print Z3 constraints when no model found
- **Impact**: Shows which constraints caused unsatisfiability
- **Usage**: Essential for debugging failed model searches
- **Example**: Displays grouped constraints by type (frame, atom, semantic)

**`print_z3` (boolean, default: False)**
- **Purpose**: Print raw Z3 model or unsat core
- **Impact**: Shows low-level solver output
- **Usage**: Advanced debugging of constraint generation
- **Example**: Displays Z3's internal representation of predicates

**`save_output` (boolean, default: False)**
- **Purpose**: Prompt to save output to file
- **Impact**: Interactive prompt after model display
- **Usage**: Useful for preserving complex model output
- **Note**: Only works in interactive mode

**`maximize` (boolean, default: False)**
- **Purpose**: Compare theories by maximizing model size
- **Impact**: Finds largest possible models for theory comparison
- **Usage**: Advanced feature for semantic analysis
- **Note**: Not commonly used with exclusion theory

## Advanced Iteration Settings

These settings fine-tune the iteration behavior and are typically set programmatically:

**`max_invalid_attempts` (integer, default: 3)**
- **Purpose**: Maximum attempts before giving up on invalid models
- **Impact**: Controls iteration robustness
- **Usage**: Increase for theories prone to invalid models

**`escape_attempts` (integer, default: 3)**
- **Purpose**: Attempts to escape local similarity regions
- **Impact**: Helps find truly distinct models
- **Usage**: Increase when models cluster in similar configurations

**`iteration_solver_timeout` (float, default: 5.0)**
- **Purpose**: Z3 solver timeout specifically for iteration (seconds)
- **Impact**: Separate from main `max_time` for iteration control
- **Usage**: Set higher than `max_time` for complex iteration

## Setting Interactions

### Exclusion-Specific Interactions

1. **Possibility and Exclusion**:
   ```python
   'possible': False,  # Allow impossible states
   'non_empty': True,  # But require witness assignments
   ```
   This combination explores exclusion patterns without possibility restrictions.

2. **Contingency and Witness Diversity**:
   ```python
   'contingent': True,   # Diverse verification
   'iterate': 3,         # Multiple models
   'non_null': True,     # Non-trivial witnesses
   ```
   Creates models with varied witness structures.

3. **Disjoint and Exclusion**:
   ```python
   'disjoint': True,     # Clear proposition separation
   'non_empty': True,    # Meaningful content
   'possible': False,    # Allow exclusion exploration
   ```
   Produces models with clear semantic boundaries.

## Usage Examples

### Basic Exclusion Example
```python
settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'expectation': True,
}
```

### Advanced Iteration Example
```python
settings = {
    'N': 4,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'iterate': 4,
    'iteration_timeout': 2.5,
    'iteration_attempts': 6,
    'max_time': 5,
}
```

### Debugging Configuration
```python
general_settings = {
    'print_impossible': True,
    'print_constraints': True,
    'print_z3': False,  # Only if needed
    'save_output': False,
    'maximize': False,
}
```

## Performance Guidelines

1. **State Space Size**: Keep N ≤ 4 for responsive interaction
2. **Iteration Count**: Balance `iterate` with `max_time`
3. **Timeouts**: Set `iteration_timeout` < `max_time` / `iterate`
4. **Constraint Complexity**: More constraints need higher timeouts

## Troubleshooting

### Common Issues

1. **Timeout with no model**:
   - Increase `max_time`
   - Reduce `N` or constraint complexity
   - Check for conflicting constraints

2. **Iteration finds duplicates**:
   - Increase `iteration_attempts`
   - Adjust `iteration_timeout`
   - Review exclusion patterns

3. **Unexpected impossible states**:
   - Check `possible` setting
   - Review exclusion relations
   - Enable `print_impossible` for debugging

### Debug Workflow

1. Start with `print_constraints: True`
2. If needed, enable `print_z3: True`
3. Use `print_impossible: True` for state analysis
4. Iterate with small `N` first, then scale up

## Integration with ModelChecker

The exclusion theory settings integrate seamlessly with the ModelChecker framework:

```python
from model_checker import BuildExample, get_theory

theory = get_theory('exclusion')
example = BuildExample(
    "my_example",
    theory,
    premises=['p'],
    conclusions=['q'],
    settings={
        'N': 3,
        'iterate': 2,
        'possible': False,
    }
)
```

Settings flow through the system: CLI flags → general settings → example settings → final merged configuration.