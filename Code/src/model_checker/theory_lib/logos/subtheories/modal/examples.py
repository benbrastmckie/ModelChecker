"""
Modal Examples Module for Logos Theory

This module provides modal-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Modal Logic Countermodels (MOD_CM_*):
   - Tests for invalid modal arguments
   - Examples showing where modal principles fail

2. Modal Logic Theorems (MOD_TH_*):
   - Tests for valid modal arguments
   - Classical modal logical properties and inference rules

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/modal.py
# or in development:
./dev_cli.py path/to/this/modal.py
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

# MOD_CM_1: NECESSITY DOES NOT ENTAIL POSSIBILITY (False in some modal systems)
MOD_CM_1_premises = ['\\Box A']
MOD_CM_1_conclusions = ['\\Diamond A']
MOD_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
MOD_CM_1_example = [
    MOD_CM_1_premises,
    MOD_CM_1_conclusions,
    MOD_CM_1_settings,
]

# MOD_CM_2: CONVERSE BARCAN FORMULA (Not valid in all modal systems)
MOD_CM_2_premises = ['\\Diamond A']
MOD_CM_2_conclusions = ['A']
MOD_CM_2_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
MOD_CM_2_example = [
    MOD_CM_2_premises,
    MOD_CM_2_conclusions,
    MOD_CM_2_settings,
]

# MOD_TH_1: NECESSITY DISTRIBUTION OVER CONJUNCTION
MOD_TH_1_premises = ['\\Box (A \\wedge B)']
MOD_TH_1_conclusions = ['(\\Box A \\wedge \\Box B)']
MOD_TH_1_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_1_example = [
    MOD_TH_1_premises,
    MOD_TH_1_conclusions,
    MOD_TH_1_settings,
]

# MOD_TH_2: POSSIBILITY DISTRIBUTION OVER DISJUNCTION
MOD_TH_2_premises = ['(\\Diamond A \\vee \\Diamond B)']
MOD_TH_2_conclusions = ['\\Diamond (A \\vee B)']
MOD_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_2_example = [
    MOD_TH_2_premises,
    MOD_TH_2_conclusions,
    MOD_TH_2_settings,
]

# MOD_TH_3: MODAL DUALITY (Box and Diamond)
MOD_TH_3_premises = ['\\Box A']
MOD_TH_3_conclusions = ['\\neg \\Diamond \\neg A']
MOD_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_3_example = [
    MOD_TH_3_premises,
    MOD_TH_3_conclusions,
    MOD_TH_3_settings,
]

# MOD_TH_4: MODAL DUALITY (Diamond and Box)
MOD_TH_4_premises = ['\\Diamond A']
MOD_TH_4_conclusions = ['\\neg \\Box \\neg A']
MOD_TH_4_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_4_example = [
    MOD_TH_4_premises,
    MOD_TH_4_conclusions,
    MOD_TH_4_settings,
]

# MOD_TH_5: MODAL K AXIOM (Distribution of necessity over implication)
MOD_TH_5_premises = ['\\Box (A \\rightarrow B)', '\\Box A']
MOD_TH_5_conclusions = ['\\Box B']
MOD_TH_5_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_5_example = [
    MOD_TH_5_premises,
    MOD_TH_5_conclusions,
    MOD_TH_5_settings,
]

# MOD_TH_6: NECESSITATION RULE
MOD_TH_6_premises = []
MOD_TH_6_conclusions = ['\\Box (A \\rightarrow A)']
MOD_TH_6_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_6_example = [
    MOD_TH_6_premises,
    MOD_TH_6_conclusions,
    MOD_TH_6_settings,
]

# MOD_TH_7: COUNTERFACTUAL NECESSITY IMPLIES NECESSITY
MOD_TH_7_premises = ['\\CFBox A']
MOD_TH_7_conclusions = ['\\Box A']
MOD_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_7_example = [
    MOD_TH_7_premises,
    MOD_TH_7_conclusions,
    MOD_TH_7_settings,
]

# MOD_TH_8: POSSIBILITY IMPLIES COUNTERFACTUAL POSSIBILITY
MOD_TH_8_premises = ['\\Diamond A']
MOD_TH_8_conclusions = ['\\CFDiamond A']
MOD_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_8_example = [
    MOD_TH_8_premises,
    MOD_TH_8_conclusions,
    MOD_TH_8_settings,
]

# MOD_TH_9: COUNTERFACTUAL MODAL DUALITY
MOD_TH_9_premises = ['\\CFBox A']
MOD_TH_9_conclusions = ['\\neg \\CFDiamond \\neg A']
MOD_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_9_example = [
    MOD_TH_9_premises,
    MOD_TH_9_conclusions,
    MOD_TH_9_settings,
]

# MOD_TH_10: DOUBLE NECESSITY
MOD_TH_10_premises = ['\\Box \\Box A']
MOD_TH_10_conclusions = ['\\Box A']
MOD_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
MOD_TH_10_example = [
    MOD_TH_10_premises,
    MOD_TH_10_conclusions,
    MOD_TH_10_settings,
]

# Create collections for different modal example types
modal_cm_examples = {
    "MOD_CM_1": MOD_CM_1_example,
    "MOD_CM_2": MOD_CM_2_example,
}

modal_th_examples = {
    "MOD_TH_1": MOD_TH_1_example,
    "MOD_TH_2": MOD_TH_2_example,
    "MOD_TH_3": MOD_TH_3_example,
    "MOD_TH_4": MOD_TH_4_example,
    "MOD_TH_5": MOD_TH_5_example,
    "MOD_TH_6": MOD_TH_6_example,
    "MOD_TH_7": MOD_TH_7_example,
    "MOD_TH_8": MOD_TH_8_example,
    "MOD_TH_9": MOD_TH_9_example,
    "MOD_TH_10": MOD_TH_10_example,
}

# Combined collection of all modal examples
modal_examples = {**modal_cm_examples, **modal_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for modal theory (includes extensional dependencies)
modal_registry = LogosOperatorRegistry()
modal_registry.load_subtheories(['extensional', 'modal'])

# Define the semantic theory
modal_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": modal_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Logos-Modal": modal_theory,
}

# Specify which examples to run by default when running this module directly
# Uncomment examples you wish to run
example_range = {
    # Quick test examples - comment out or replace as needed
    "MOD_TH_3": MOD_TH_3_example,  # Modal duality
    "MOD_TH_5": MOD_TH_5_example,  # K axiom
}

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)