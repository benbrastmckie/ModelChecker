"""Examples package for Default Theory

This package provides a collection of test cases for the unified semantics,
including both countermodels showing invalidity and theorems showing validity.

The examples are organized by operator type:
- extensional.py: Examples for extensional operators (conjunction, disjunction, etc.)
- modal.py: Examples for modal operators (necessity, possibility)
- counterfactual.py: Examples for counterfactual operators
- constitutive.py: Examples for constitutive operators (ground, essence, etc.)
- relevance.py: Examples for relevance operators

Usage:
------
This package provides several ways to work with examples:

1. Individual Module Execution:
   Each example module can be run directly:
   ```bash
   model-checker path/to/this/examples/counterfactual.py
   # or in development:
   ./dev_cli.py path/to/this/examples/counterfactual.py
   ```

2. Combined Execution:
   This __init__.py file can be used to run examples from multiple modules:
   ```bash
   model-checker path/to/this/examples/__init__.py
   ```

3. Programmatic Access:
   Import the example collections for use in other code:
   ```python
   from model_checker.theory_lib.default.examples import counterfactual_examples
   ```

Example Format:
--------------
Each example is structured as a list: [premises, conclusions, settings]
- premises: List of formulas that serve as assumptions
- conclusions: List of formulas to be tested
- settings: Dictionary of specific settings for this example

Settings Options:
----------------
- N: Number of atomic propositions (default: 3)
- contingent: Whether to use contingent valuations
- disjoint: Whether to enforce disjoint valuations
- non_empty: Whether to enforce non-empty valuations
- non_null: Whether to enforce non-null valuations
- max_time: Maximum computation time in seconds
- iterate: Number of iterations for modal operators
- expectation: Expected result (True for countermodel found)

Notes:
------
- Each module maintains its own collections of examples
- The test_example_range dictionary is used by the test suite
- For individual module execution, edit the example_range dictionary in that module
"""

# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
if parent_dir not in sys.path:
    sys.path.insert(0, parent_dir)

# Import semantic classes
from ..semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import operators
from ..operators import default_operators

# Import example collections from the modules
from .counterfactual import (
    counterfactual_examples,
    counterfactual_cm_examples,
    counterfactual_th_examples
)

from .modal import (
    modal_examples,
    modal_cm_examples,
    modal_th_examples,
    modal_def_examples
)

from .constitutive import (
    constitutive_examples,
    constitutive_cm_examples,
    constitutive_th_examples
)

from .extensional import (
    extensional_examples,
    extensional_cm_examples,
    extensional_th_examples
)

from .relevance import (
    relevance_examples,
    relevance_cm_examples,
    relevance_th_examples
)

# Expose the collections in __all__
__all__ = [
    'general_settings',
    'default_theory',
    'semantic_theories',
    'example_range',
    'test_example_range',
    'counterfactual_examples',
    'counterfactual_cm_examples',
    'counterfactual_th_examples',
    'modal_examples',
    'modal_cm_examples',
    'modal_th_examples',
    'modal_def_examples',
    'constitutive_examples',
    'constitutive_cm_examples',
    'constitutive_th_examples',
    'extensional_examples',
    'extensional_cm_examples',
    'extensional_th_examples',
    'relevance_examples',
    'relevance_cm_examples',
    'relevance_th_examples',
]

########################
### DEFAULT SETTINGS ###
########################

general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}


####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": default_operators,
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": default_theory,
}

#########################################
### SPECIFY EXAMPLES FOR UNIT TESTING ###
#########################################

# This dictionary is used by the unit tests in /test/test_default.py
# It provides a consolidated list of all examples for testing
test_example_range = {
    **counterfactual_examples,
    **modal_examples,
    **constitutive_examples,
    **extensional_examples,
    **relevance_examples,
}

# For running examples when this module is executed directly
# You can add or remove examples as needed
example_range = {
    # Constitutive example as default
    "CL_CM_8": constitutive_examples["CL_CM_8"],
    
    # Add other examples as needed
    # "CF_CM_1": counterfactual_examples["CF_CM_1"],
    # "ML_CM_1": modal_examples["ML_CM_1"],
}

####################
### RUN EXAMPLES ###
####################

if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_dir)