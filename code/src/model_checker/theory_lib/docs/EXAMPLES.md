# Examples.py Module Standard Format

This document defines the standard structure and conventions for all `examples.py` modules across theories and subtheories in the ModelChecker codebase.

## Overview

Each `examples.py` module should provide a standardized collection of test cases for semantic theories, including both countermodels (showing invalidity) and theorems (showing validity). The standardized format ensures consistency across all theories while maintaining backward compatibility.

## Required Module Structure

### 1. Header Documentation
- Module docstring explaining the theory/subtheory
- Usage instructions for command line and IDE execution
- Example categories overview
- Configuration notes

### 2. Imports Section
```python
# Standard imports
import sys
import os

# Add current directory to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import semantic classes
from .semantic import (
    TheorySemantics,
    TheoryProposition, 
    TheoryModelStructure,
)

# Import operators
from .operators import theory_operators
```

### 3. Example Definitions

#### 3.1 COUNTERMODELS Section
```python
#####################
### COUNTERMODELS ###
#####################

# [PREFIX]_CM_[NUMBER]: [DESCRIPTION]
[PREFIX]_CM_1_premises = [...]
[PREFIX]_CM_1_conclusions = [...]
[PREFIX]_CM_1_settings = {...}
[PREFIX]_CM_1_example = [
    [PREFIX]_CM_1_premises,
    [PREFIX]_CM_1_conclusions,
    [PREFIX]_CM_1_settings,
]

# Additional countermodels...
```

#### 3.2 THEOREMS Section
```python
################
### THEOREMS ###
################

# [PREFIX]_TH_[NUMBER]: [DESCRIPTION]
[PREFIX]_TH_1_premises = [...]
[PREFIX]_TH_1_conclusions = [...]
[PREFIX]_TH_1_settings = {...}
[PREFIX]_TH_1_example = [
    [PREFIX]_TH_1_premises,
    [PREFIX]_TH_1_conclusions,
    [PREFIX]_TH_1_settings,
]

# Additional theorems...
```

### 4. Collections Section
```python
# Create collections for different example types
theory_cm_examples = {
    "[PREFIX]_CM_1": [PREFIX]_CM_1_example,  # DESCRIPTION
    "[PREFIX]_CM_2": [PREFIX]_CM_2_example,  # DESCRIPTION
    # ... all countermodels
}

theory_th_examples = {
    "[PREFIX]_TH_1": [PREFIX]_TH_1_example,  # DESCRIPTION
    "[PREFIX]_TH_2": [PREFIX]_TH_2_example,  # DESCRIPTION
    # ... all theorems
}

# Combined collection of all examples
unit_tests = {**theory_cm_examples, **theory_th_examples}
```

### 5. Aliases and Compatibility
```python
# Aliases for main dictionary (backward compatibility)
test_example_range = unit_tests
all_theory_examples = unit_tests

# Default example range (curated subset for direct execution)
example_range = {
    # Select representative examples
    "[PREFIX]_CM_1": [PREFIX]_CM_1_example,
    "[PREFIX]_TH_1": [PREFIX]_TH_1_example,
    # ... curated selection
}
```

### 6. Settings and Theory Definition
```python
# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Define the semantic theory
theory_definition = {
    "semantics": TheorySemantics,
    "proposition": TheoryProposition,
    "model": TheoryModelStructure,
    "operators": theory_operators,
}

# Specify which theories to use
semantic_theories = {
    "Theory-Name": theory_definition,
}
```

### 7. Helper Functions
```python
def get_examples():
    """
    Get all theory examples.
    
    Returns:
        dict: Dictionary containing all theory examples
    """
    return {
        'countermodels': theory_cm_examples,
        'theorems': theory_th_examples,
        'all': unit_tests
    }
```

### 8. Command Line Support
```python
# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

## Naming Conventions

### Example Prefixes
- **EX_**: Extensional logic examples
- **MOD_**: Modal logic examples  
- **CF_**: Counterfactual logic examples
- **CON_**: Constitutive logic examples
- **REL_**: Relevance logic examples
- **TM_**: Temporal logic examples
- **BM_**: Bimodal logic examples
- **S1_**, **S2_**: Strategy-specific examples

### Example Types
- **CM**: Countermodel (invalid argument)
- **TH**: Theorem (valid argument)  
- **DEF**: Definition (optional)

### Complete Pattern
`[PREFIX]_[TYPE]_[NUMBER]`

Examples:
- `EX_CM_1`: Extensional countermodel #1
- `MOD_TH_5`: Modal theorem #5
- `CF_CM_12`: Counterfactual countermodel #12

## Example Structure

Each example follows the format:
```python
[NAME]_example = [premises, conclusions, settings]
```

Where:
- **premises**: List of strings representing premise formulas
- **conclusions**: List of strings representing conclusion formulas  
- **settings**: Dictionary of configuration options

### Common Settings
```python
settings = {
    'N': 2,                    # Number of atomic propositions
    'M': 1,                    # Number of time points (temporal theories)
    'contingent': False,       # Whether to use contingent valuations
    'non_null': False,         # Whether to enforce non-null constraints
    'non_empty': False,        # Whether to enforce non-empty constraints
    'disjoint': False,         # Whether to enforce disjoint valuations
    'max_time': 5,             # Maximum computation time in seconds
    'iterate': 1,              # Number of model iterations
    'expectation': True,       # Expected result (True for countermodel, False for theorem)
}
```

## Directory Organization

### Theory-Level Examples
- `theory_lib/[theory]/examples.py`: Main examples aggregating all subtheories
- Imports from subtheory examples using standardized `unit_tests` variable

### Subtheory Examples  
- `theory_lib/[theory]/subtheories/[subtheory]/examples.py`: Subtheory-specific examples
- Uses subtheory-specific prefixes (e.g., CF_ for counterfactual)

### Strategy Examples
- `theory_lib/[theory]/[strategy]/examples.py`: Strategy-specific examples
- Uses strategy prefixes (e.g., S1_, S2_)

## Backward Compatibility

To maintain compatibility with existing code:

1. **Always provide test_example_range alias:**
   ```python
   test_example_range = unit_tests
   ```

2. **Keep example_range for direct execution:**
   ```python
   example_range = {...}  # Curated subset
   ```

3. **Import pattern in theory __init__.py:**
   ```python
   def get_test_examples(theory_name):
       module = importlib.import_module(f".{theory_name}.examples", package=__name__)
       return module.test_example_range  # Uses our alias
   ```

## Integration with Test Framework

Test files should access examples via `unit_tests`:

```python
from model_checker.theory_lib.[theory] import examples

@pytest.mark.parametrize("example_name, example_case", examples.unit_tests.items())
def test_theory_examples(example_name, example_case):
    # Test implementation
    pass
```

## Quality Guidelines

1. **Descriptive Comments**: Each example should have a clear descriptive comment
2. **Appropriate Settings**: Settings should be tuned for the specific example
3. **Clear Organization**: Group related examples together
4. **Comprehensive Coverage**: Include both positive and negative test cases
5. **Performance**: Avoid overly complex examples that timeout frequently

This standardized format ensures consistency, maintainability, and extensibility across all ModelChecker theory implementations.