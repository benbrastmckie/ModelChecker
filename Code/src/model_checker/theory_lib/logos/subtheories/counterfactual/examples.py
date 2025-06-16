"""
Counterfactual Examples Module for Logos Theory

This module provides counterfactual-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Counterfactual Logic Countermodels (CF_CM_*):
   - Tests for invalid counterfactual arguments
   - Examples showing where counterfactual principles fail

2. Counterfactual Logic Theorems (CF_TH_*):
   - Tests for valid counterfactual arguments
   - Counterfactual conditional and imposition principles

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/counterfactual.py
# or in development:
./dev_cli.py path/to/this/counterfactual.py
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

# CF_CM_1: COUNTERFACTUAL DOES NOT ENTAIL MATERIAL CONDITIONAL
CF_CM_1_premises = ['(A \\boxright B)']
CF_CM_1_conclusions = ['(A \\rightarrow B)']
CF_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : True,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# CF_CM_2: MATERIAL CONDITIONAL DOES NOT ENTAIL COUNTERFACTUAL
CF_CM_2_premises = ['(A \\rightarrow B)']
CF_CM_2_conclusions = ['(A \\boxright B)']
CF_CM_2_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : True,
}
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    CF_CM_2_settings,
]

# CF_TH_1: COUNTERFACTUAL MODUS PONENS
CF_TH_1_premises = ['A', '(A \\boxright B)']
CF_TH_1_conclusions = ['B']
CF_TH_1_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_1_example = [
    CF_TH_1_premises,
    CF_TH_1_conclusions,
    CF_TH_1_settings,
]

# CF_TH_2: COUNTERFACTUAL REFLEXIVITY
CF_TH_2_premises = []
CF_TH_2_conclusions = ['(A \\boxright A)']
CF_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_2_example = [
    CF_TH_2_premises,
    CF_TH_2_conclusions,
    CF_TH_2_settings,
]

# CF_TH_3: COUNTERFACTUAL IMPLIES MIGHT COUNTERFACTUAL
CF_TH_3_premises = ['(A \\boxright B)']
CF_TH_3_conclusions = ['(A \\diamondright B)']
CF_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_3_example = [
    CF_TH_3_premises,
    CF_TH_3_conclusions,
    CF_TH_3_settings,
]

# CF_TH_4: COUNTERFACTUAL TRANSITIVITY
CF_TH_4_premises = ['(A \\boxright B)', '(B \\boxright C)']
CF_TH_4_conclusions = ['(A \\boxright C)']
CF_TH_4_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_4_example = [
    CF_TH_4_premises,
    CF_TH_4_conclusions,
    CF_TH_4_settings,
]

# CF_TH_5: IMPOSITION REFLEXIVITY
CF_TH_5_premises = []
CF_TH_5_conclusions = ['(A \\imposition A)']
CF_TH_5_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_5_example = [
    CF_TH_5_premises,
    CF_TH_5_conclusions,
    CF_TH_5_settings,
]

# CF_TH_6: IMPOSITION IMPLIES MIGHT IMPOSITION
CF_TH_6_premises = ['(A \\imposition B)']
CF_TH_6_conclusions = ['(A \\could B)']
CF_TH_6_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_6_example = [
    CF_TH_6_premises,
    CF_TH_6_conclusions,
    CF_TH_6_settings,
]

# CF_TH_7: COUNTERFACTUAL DISTRIBUTION OVER CONJUNCTION
CF_TH_7_premises = ['(A \\boxright (B \\wedge C))']
CF_TH_7_conclusions = ['((A \\boxright B) \\wedge (A \\boxright C))']
CF_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_7_example = [
    CF_TH_7_premises,
    CF_TH_7_conclusions,
    CF_TH_7_settings,
]

# CF_TH_8: MIGHT COUNTERFACTUAL DISTRIBUTION OVER DISJUNCTION
CF_TH_8_premises = ['((A \\diamondright B) \\vee (A \\diamondright C))']
CF_TH_8_conclusions = ['(A \\diamondright (B \\vee C))']
CF_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_8_example = [
    CF_TH_8_premises,
    CF_TH_8_conclusions,
    CF_TH_8_settings,
]

# CF_TH_9: IMPOSSIBLE ANTECEDENT COUNTERFACTUAL
CF_TH_9_premises = ['\\neg \\Diamond A']
CF_TH_9_conclusions = ['(A \\boxright B)']
CF_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_9_example = [
    CF_TH_9_premises,
    CF_TH_9_conclusions,
    CF_TH_9_settings,
]

# CF_TH_10: NECESSARY CONSEQUENT COUNTERFACTUAL
CF_TH_10_premises = ['\\Box B']
CF_TH_10_conclusions = ['(A \\boxright B)']
CF_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_10_example = [
    CF_TH_10_premises,
    CF_TH_10_conclusions,
    CF_TH_10_settings,
]

# Create collections for different counterfactual example types
counterfactual_cm_examples = {
    "CF_CM_1": CF_CM_1_example,
    "CF_CM_2": CF_CM_2_example,
}

counterfactual_th_examples = {
    "CF_TH_1": CF_TH_1_example,
    "CF_TH_2": CF_TH_2_example,
    "CF_TH_3": CF_TH_3_example,
    "CF_TH_4": CF_TH_4_example,
    "CF_TH_5": CF_TH_5_example,
    "CF_TH_6": CF_TH_6_example,
    "CF_TH_7": CF_TH_7_example,
    "CF_TH_8": CF_TH_8_example,
    "CF_TH_9": CF_TH_9_example,
    "CF_TH_10": CF_TH_10_example,
}

# Combined collection of all counterfactual examples
counterfactual_examples = {**counterfactual_cm_examples, **counterfactual_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for counterfactual theory (includes extensional and modal dependencies)
counterfactual_registry = LogosOperatorRegistry()
counterfactual_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

# Define the semantic theory
counterfactual_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": counterfactual_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Logos-Counterfactual": counterfactual_theory,
}

# Specify which examples to run by default when running this module directly
# Uncomment examples you wish to run
example_range = {
    # Quick test examples - comment out or replace as needed
    "CF_TH_2": CF_TH_2_example,  # Counterfactual reflexivity
    "CF_TH_3": CF_TH_3_example,  # Counterfactual implies might counterfactual
}

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)