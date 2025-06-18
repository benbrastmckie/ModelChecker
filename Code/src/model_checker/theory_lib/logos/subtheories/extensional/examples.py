"""
Extensional Examples Module for Logos Theory

This module provides extensional-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Extensional Logic Countermodels (EXT_CM_*):
   - Tests for invalid extensional arguments
   - Examples showing when classical logic fails

2. Extensional Logic Theorems (EXT_TH_*):
   - Tests for valid extensional arguments
   - Classical logical properties and inference rules

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
from ...semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)

# Import operators
from ...operators import LogosOperatorRegistry

# EXT_CM_1: CONTRADICTION (A does not entail not-A)
EXT_CM_1_premises = ['A']
EXT_CM_1_conclusions = ['\\neg A']
EXT_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
EXT_CM_1_example = [
    EXT_CM_1_premises,
    EXT_CM_1_conclusions,
    EXT_CM_1_settings,
]

# EXT_CM_2: AFFIRMING THE CONSEQUENT (Invalid inference)
EXT_CM_2_premises = ['B', '(A \\rightarrow B)']
EXT_CM_2_conclusions = ['A']
EXT_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
EXT_CM_2_example = [
    EXT_CM_2_premises,
    EXT_CM_2_conclusions,
    EXT_CM_2_settings,
]

# EXT_TH_1: MODUS PONENS (Valid inference)
EXT_TH_1_premises = ['A', '(A \\rightarrow B)']
EXT_TH_1_conclusions = ['B']
EXT_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# EXT_TH_2: MODUS TOLLENS (Valid inference)
EXT_TH_2_premises = ['\\neg B', '(A \\rightarrow B)']
EXT_TH_2_conclusions = ['\\neg A']
EXT_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_2_example = [
    EXT_TH_2_premises,
    EXT_TH_2_conclusions,
    EXT_TH_2_settings,
]

# EXT_TH_3: CONJUNCTION ELIMINATION
EXT_TH_3_premises = ['(A \\wedge B)']
EXT_TH_3_conclusions = ['A']
EXT_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_3_example = [
    EXT_TH_3_premises,
    EXT_TH_3_conclusions,
    EXT_TH_3_settings,
]

# EXT_TH_4: DISJUNCTION INTRODUCTION
EXT_TH_4_premises = ['A']
EXT_TH_4_conclusions = ['(A \\vee B)']
EXT_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_4_example = [
    EXT_TH_4_premises,
    EXT_TH_4_conclusions,
    EXT_TH_4_settings,
]

# EXT_TH_5: DOUBLE NEGATION ELIMINATION
EXT_TH_5_premises = ['\\neg \\neg A']
EXT_TH_5_conclusions = ['A']
EXT_TH_5_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_5_example = [
    EXT_TH_5_premises,
    EXT_TH_5_conclusions,
    EXT_TH_5_settings,
]

# EXT_TH_6: LAW OF EXCLUDED MIDDLE
EXT_TH_6_premises = []
EXT_TH_6_conclusions = ['(A \\vee \\neg A)']
EXT_TH_6_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_6_example = [
    EXT_TH_6_premises,
    EXT_TH_6_conclusions,
    EXT_TH_6_settings,
]

# EXT_TH_7: DE MORGAN'S LAW 1
EXT_TH_7_premises = ['\\neg (A \\wedge B)']
EXT_TH_7_conclusions = ['(\\neg A \\vee \\neg B)']
EXT_TH_7_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_7_example = [
    EXT_TH_7_premises,
    EXT_TH_7_conclusions,
    EXT_TH_7_settings,
]

# EXT_TH_8: DE MORGAN'S LAW 2
EXT_TH_8_premises = ['\\neg (A \\vee B)']
EXT_TH_8_conclusions = ['(\\neg A \\wedge \\neg B)']
EXT_TH_8_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_8_example = [
    EXT_TH_8_premises,
    EXT_TH_8_conclusions,
    EXT_TH_8_settings,
]

# EXT_TH_9: BICONDITIONAL FORWARD
EXT_TH_9_premises = ['(A \\leftrightarrow B)', 'A']
EXT_TH_9_conclusions = ['B']
EXT_TH_9_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_9_example = [
    EXT_TH_9_premises,
    EXT_TH_9_conclusions,
    EXT_TH_9_settings,
]

# EXT_TH_10: BICONDITIONAL BACKWARD
EXT_TH_10_premises = ['(A \\leftrightarrow B)', 'B']
EXT_TH_10_conclusions = ['A']
EXT_TH_10_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_10_example = [
    EXT_TH_10_premises,
    EXT_TH_10_conclusions,
    EXT_TH_10_settings,
]

# EXT_TH_11: TOP IS TAUTOLOGY
EXT_TH_11_premises = []
EXT_TH_11_conclusions = ['\\top']
EXT_TH_11_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_11_example = [
    EXT_TH_11_premises,
    EXT_TH_11_conclusions,
    EXT_TH_11_settings,
]

# EXT_TH_12: EX FALSO QUODLIBET
EXT_TH_12_premises = ['\\bot']
EXT_TH_12_conclusions = ['A']
EXT_TH_12_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
EXT_TH_12_example = [
    EXT_TH_12_premises,
    EXT_TH_12_conclusions,
    EXT_TH_12_settings,
]

# Create collections for different extensional example types
extensional_cm_examples = {
    "EXT_CM_1": EXT_CM_1_example,
    "EXT_CM_2": EXT_CM_2_example,
}

extensional_th_examples = {
    "EXT_TH_1": EXT_TH_1_example,
    "EXT_TH_2": EXT_TH_2_example,
    "EXT_TH_3": EXT_TH_3_example,
    "EXT_TH_4": EXT_TH_4_example,
    "EXT_TH_5": EXT_TH_5_example,
    "EXT_TH_6": EXT_TH_6_example,
    "EXT_TH_7": EXT_TH_7_example,
    "EXT_TH_8": EXT_TH_8_example,
    "EXT_TH_9": EXT_TH_9_example,
    "EXT_TH_10": EXT_TH_10_example,
    "EXT_TH_11": EXT_TH_11_example,
    "EXT_TH_12": EXT_TH_12_example,
}

# Combined collection of all extensional examples - using standardized variable name
unit_tests = {**extensional_cm_examples, **extensional_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for extensional theory
extensional_registry = LogosOperatorRegistry()
extensional_registry.load_subtheories(['extensional'])

# Define the semantic theory
extensional_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": extensional_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": extensional_theory,
}

# Specify which examples to run by default when running this module directly
# All examples included by default
example_range = unit_tests

def get_examples():
    """
    Get all extensional examples.
    
    Returns:
        dict: Dictionary containing all extensional examples
    """
    return {
        'countermodels': extensional_cm_examples,
        'theorems': extensional_th_examples,
        'all': unit_tests
    }

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
