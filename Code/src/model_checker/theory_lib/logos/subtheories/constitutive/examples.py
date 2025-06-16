"""
Constitutive Examples Module for Logos Theory

This module provides constitutive-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Constitutive Logic Countermodels (CON_CM_*):
   - Tests for invalid constitutive arguments
   - Examples showing where constitutive principles fail

2. Constitutive Logic Theorems (CON_TH_*):
   - Tests for valid constitutive arguments
   - Ground, essence, identity, relevance, and reduction principles

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/constitutive.py
# or in development:
./dev_cli.py path/to/this/constitutive.py
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

# CON_CM_1: IDENTITY IS NOT TRIVIAL (A does not entail B just because A a B)
CON_CM_1_premises = ['(A \\equiv B)']
CON_CM_1_conclusions = ['A']
CON_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
CON_CM_1_example = [
    CON_CM_1_premises,
    CON_CM_1_conclusions,
    CON_CM_1_settings,
]

# CON_CM_2: GROUND DOES NOT ENTAIL TRUTH (A d B does not entail A)
CON_CM_2_premises = ['(A \\leq B)']
CON_CM_2_conclusions = ['A']
CON_CM_2_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
CON_CM_2_example = [
    CON_CM_2_premises,
    CON_CM_2_conclusions,
    CON_CM_2_settings,
]

# CON_TH_1: IDENTITY IS REFLEXIVE
CON_TH_1_premises = []
CON_TH_1_conclusions = ['(A \\equiv A)']
CON_TH_1_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_1_example = [
    CON_TH_1_premises,
    CON_TH_1_conclusions,
    CON_TH_1_settings,
]

# CON_TH_2: IDENTITY IS SYMMETRIC
CON_TH_2_premises = ['(A \\equiv B)']
CON_TH_2_conclusions = ['(B \\equiv A)']
CON_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_2_example = [
    CON_TH_2_premises,
    CON_TH_2_conclusions,
    CON_TH_2_settings,
]

# CON_TH_3: IDENTITY IS TRANSITIVE
CON_TH_3_premises = ['(A \\equiv B)', '(B \\equiv C)']
CON_TH_3_conclusions = ['(A \\equiv C)']
CON_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_3_example = [
    CON_TH_3_premises,
    CON_TH_3_conclusions,
    CON_TH_3_settings,
]

# CON_TH_4: GROUND IS REFLEXIVE
CON_TH_4_premises = []
CON_TH_4_conclusions = ['(A \\leq A)']
CON_TH_4_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_4_example = [
    CON_TH_4_premises,
    CON_TH_4_conclusions,
    CON_TH_4_settings,
]

# CON_TH_5: GROUND IS TRANSITIVE
CON_TH_5_premises = ['(A \\leq B)', '(B \\leq C)']
CON_TH_5_conclusions = ['(A \\leq C)']
CON_TH_5_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_5_example = [
    CON_TH_5_premises,
    CON_TH_5_conclusions,
    CON_TH_5_settings,
]

# CON_TH_6: ESSENCE IS REFLEXIVE
CON_TH_6_premises = []
CON_TH_6_conclusions = ['(A \\sqsubseteq A)']
CON_TH_6_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_6_example = [
    CON_TH_6_premises,
    CON_TH_6_conclusions,
    CON_TH_6_settings,
]

# CON_TH_7: ESSENCE IS TRANSITIVE
CON_TH_7_premises = ['(A \\sqsubseteq B)', '(B \\sqsubseteq C)']
CON_TH_7_conclusions = ['(A \\sqsubseteq C)']
CON_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_7_example = [
    CON_TH_7_premises,
    CON_TH_7_conclusions,
    CON_TH_7_settings,
]

# CON_TH_8: RELEVANCE IS REFLEXIVE
CON_TH_8_premises = []
CON_TH_8_conclusions = ['(A \\preceq A)']
CON_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_8_example = [
    CON_TH_8_premises,
    CON_TH_8_conclusions,
    CON_TH_8_settings,
]

# CON_TH_9: RELEVANCE IS TRANSITIVE
CON_TH_9_premises = ['(A \\preceq B)', '(B \\preceq C)']
CON_TH_9_conclusions = ['(A \\preceq C)']
CON_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_9_example = [
    CON_TH_9_premises,
    CON_TH_9_conclusions,
    CON_TH_9_settings,
]

# CON_TH_10: REDUCTION IMPLIES GROUND
CON_TH_10_premises = ['(A \\reduction B)']
CON_TH_10_conclusions = ['(A \\leq B)']
CON_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_10_example = [
    CON_TH_10_premises,
    CON_TH_10_conclusions,
    CON_TH_10_settings,
]

# CON_TH_11: REDUCTION IMPLIES ESSENCE
CON_TH_11_premises = ['(A \\reduction B)']
CON_TH_11_conclusions = ['(A \\sqsubseteq B)']
CON_TH_11_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_11_example = [
    CON_TH_11_premises,
    CON_TH_11_conclusions,
    CON_TH_11_settings,
]

# CON_TH_12: GROUND AND ESSENCE TOGETHER GIVE REDUCTION
CON_TH_12_premises = ['(A \\leq B)', '(A \\sqsubseteq B)']
CON_TH_12_conclusions = ['(A \\reduction B)']
CON_TH_12_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CON_TH_12_example = [
    CON_TH_12_premises,
    CON_TH_12_conclusions,
    CON_TH_12_settings,
]

# Create collections for different constitutive example types
constitutive_cm_examples = {
    "CON_CM_1": CON_CM_1_example,
    "CON_CM_2": CON_CM_2_example,
}

constitutive_th_examples = {
    "CON_TH_1": CON_TH_1_example,
    "CON_TH_2": CON_TH_2_example,
    "CON_TH_3": CON_TH_3_example,
    "CON_TH_4": CON_TH_4_example,
    "CON_TH_5": CON_TH_5_example,
    "CON_TH_6": CON_TH_6_example,
    "CON_TH_7": CON_TH_7_example,
    "CON_TH_8": CON_TH_8_example,
    "CON_TH_9": CON_TH_9_example,
    "CON_TH_10": CON_TH_10_example,
    "CON_TH_11": CON_TH_11_example,
    "CON_TH_12": CON_TH_12_example,
}

# Combined collection of all constitutive examples
constitutive_examples = {**constitutive_cm_examples, **constitutive_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for constitutive theory
constitutive_registry = LogosOperatorRegistry()
constitutive_registry.load_subtheories(['extensional', 'constitutive'])

# Define the semantic theory
constitutive_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": constitutive_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Logos-Constitutive": constitutive_theory,
}

# Specify which examples to run by default when running this module directly
# Uncomment examples you wish to run
example_range = {
    # Quick test examples - comment out or replace as needed
    "CON_TH_1": CON_TH_1_example,  # Identity reflexivity
    "CON_TH_12": CON_TH_12_example,  # Reduction composition
}

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)