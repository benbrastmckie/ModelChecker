"""
Extensional Examples Module for Default Theory

This module provides extensional-specific examples for the unified semantics,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Extensional Logic Countermodels (EL_CM_*):
   - Tests for invalid extensional arguments
   - Examples of conjunction, disjunction, negation, material implication

2. Extensional Logic Theorems (EL_TH_*):
   - Tests for valid extensional arguments
   - Classical logical properties like De Morgan's Laws

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/extensional.py
# or in development:
./dev_cli.py path/to/this/extensional.py
```

To use a specific collection of examples, modify the example_range dictionary below.
"""

# Standard imports
import sys
import os

# Add parent directories to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
parent_parent_dir = os.path.dirname(parent_dir)
if parent_dir not in sys.path:
    sys.path.insert(0, parent_dir)
if parent_parent_dir not in sys.path:
    sys.path.insert(0, parent_parent_dir)

# Import semantic classes
from ..semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import operators
from ..operators import default_operators

# EL_CM_1: CONTRADICTION
EL_CM_1_premises = ['A']
EL_CM_1_conclusions = ['\\neg A']
EL_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
EL_CM_1_example = [
    EL_CM_1_premises,
    EL_CM_1_conclusions,
    EL_CM_1_settings,
]

# EL_TH_1: MODUS PONENS
EL_TH_1_premises = ['A', '(A \\rightarrow B)']
EL_TH_1_conclusions = ['B']
EL_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EL_TH_1_example = [
    EL_TH_1_premises,
    EL_TH_1_conclusions,
    EL_TH_1_settings,
]

# EL_TH_2: AXIOM OF SIMPLIFICATION
EL_TH_2_premises = []
EL_TH_2_conclusions = ['(A \\rightarrow (B \\rightarrow A))']
EL_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EL_TH_2_example = [
    EL_TH_2_premises,
    EL_TH_2_conclusions,
    EL_TH_2_settings,
]

# EL_TH_3: AXIOM OF DISTRIBUTION
EL_TH_3_premises = []
EL_TH_3_conclusions = ['((A \\rightarrow (B \\rightarrow C)) \\rightarrow ((A \\rightarrow B) \\rightarrow (A \\rightarrow C)))']
EL_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EL_TH_3_example = [
    EL_TH_3_premises,
    EL_TH_3_conclusions,
    EL_TH_3_settings,
]

# EL_TH_4: CONTRAPOSITION
EL_TH_4_premises = []
EL_TH_4_conclusions = ['((\\neg A \\rightarrow \\neg B) \\rightarrow (B \\rightarrow A))']
EL_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EL_TH_4_example = [
    EL_TH_4_premises,
    EL_TH_4_conclusions,
    EL_TH_4_settings,
]

# Create collections for different extensional example types
extensional_cm_examples = {
    "EL_CM_1": EL_CM_1_example,
}

extensional_th_examples = {
    "EL_TH_1": EL_TH_1_example,
    "EL_TH_2": EL_TH_2_example,
    "EL_TH_3": EL_TH_3_example,
    "EL_TH_4": EL_TH_4_example,
}

# Combined collection of all extensional examples
extensional_examples = {**extensional_cm_examples, **extensional_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Define the semantic theory
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

# Specify which examples to run by default when running this module directly
# Uncomment examples you wish to run
example_range = {
    # Uncomment to run specific examples:
    # "EL_TH_1": EL_TH_1_example,
    
    # Quick test example - comment out or replace as needed
    "EL_CM_1": EL_CM_1_example,
}

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_dir)