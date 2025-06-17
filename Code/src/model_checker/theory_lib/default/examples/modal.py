"""
Modal Examples Module for Default Theory

This module provides modal-specific examples for the unified semantics,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Modal Logic Countermodels (ML_CM_*):
   - Tests for invalid modal arguments
   - Examples of necessity and possibility operators

2. Modal Logic Theorems (ML_TH_*):
   - Tests for valid modal arguments
   - Includes K, T, 4, B, and 5 axioms in box and counterfactual forms

3. Modal Operator Definitions (ML_DEF_*):
   - Tests for defined modal operators
   - Comparison between primitive and defined modal operators

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
from ..semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import operators
from ..operators import default_operators

# ML_CM_1: DISTRIBUTION OF NECESSITY OVER DISJUNCTION
ML_CM_1_premises = ['\\Box (A \\vee B)']
ML_CM_1_conclusions = ['\\Box A \\vee \\Box B']
ML_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
ML_CM_1_example = [
    ML_CM_1_premises,
    ML_CM_1_conclusions,
    ML_CM_1_settings,
]

# ML_CM_2: NECESSITATED ARGUMENTS MODUS PONENS
ML_CM_2_premises = ['\\Box A', '(A \\rightarrow B)']
ML_CM_2_conclusions = ['\\Box B']
ML_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
ML_CM_2_example = [
    ML_CM_2_premises,
    ML_CM_2_conclusions,
    ML_CM_2_settings,
]

# ML_CM_3: COUNTERFACTUAL IMPLIES STRICT CONDITIONAL
ML_CM_3_premises = ['(A \\boxright B)']
ML_CM_3_conclusions = ['\\Box (A \\rightarrow B)']
ML_CM_3_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
ML_CM_3_example = [
    ML_CM_3_premises,
    ML_CM_3_conclusions,
    ML_CM_3_settings,
]

# ML_TH_1: STRICT CONDITIONAL TO COUNTERFACTUAL
ML_TH_1_premises = ['\\Box (A \\rightarrow B)']
ML_TH_1_conclusions = ['(A \\boxright B)']
ML_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_1_example = [
    ML_TH_1_premises,
    ML_TH_1_conclusions,
    ML_TH_1_settings,
]

# ML_TH_2: K AXIOM (BOX)
ML_TH_2_premises = ['\\Box (A \\rightarrow B)']
ML_TH_2_conclusions = ['(\\Box A \\rightarrow \\Box B)']
ML_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_2_example = [
    ML_TH_2_premises,
    ML_TH_2_conclusions,
    ML_TH_2_settings,
]

# ML_TH_3: K AXIOM (TOP)
ML_TH_3_premises = ['(\\top \\boxright (A \\rightarrow B))']
ML_TH_3_conclusions = ['((\\top \\boxright A) \\rightarrow (\\top \\boxright B))']
ML_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_3_example = [
    ML_TH_3_premises,
    ML_TH_3_conclusions,
    ML_TH_3_settings,
]

# ML_TH_4: T AXIOM (TOP)
ML_TH_4_premises = ['(\\top \\boxright A)']
ML_TH_4_conclusions = ['A']
ML_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_4_example = [
    ML_TH_4_premises,
    ML_TH_4_conclusions,
    ML_TH_4_settings,
]

# ML_TH_5: T AXIOM (BOX)
ML_TH_5_premises = ['\\Box A']
ML_TH_5_conclusions = ['A']
ML_TH_5_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_5_example = [
    ML_TH_5_premises,
    ML_TH_5_conclusions,
    ML_TH_5_settings,
]

# ML_TH_6: 4 AXIOM (TOP)
ML_TH_6_premises = ['(\\top \\boxright A)']
ML_TH_6_conclusions = ['(\\top \\boxright (\\top \\boxright A))']
ML_TH_6_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_6_example = [
    ML_TH_6_premises,
    ML_TH_6_conclusions,
    ML_TH_6_settings,
]

# ML_TH_7: 4 AXIOM (BOX)
ML_TH_7_premises = ['\\Box A']
ML_TH_7_conclusions = ['\\Box \\Box A']
ML_TH_7_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_7_example = [
    ML_TH_7_premises,
    ML_TH_7_conclusions,
    ML_TH_7_settings,
]

# ML_TH_8: B AXIOM (TOP)
ML_TH_8_premises = ['A']
ML_TH_8_conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']
ML_TH_8_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_8_example = [
    ML_TH_8_premises,
    ML_TH_8_conclusions,
    ML_TH_8_settings,
]

# ML_TH_9: B AXIOM (BOX)
ML_TH_9_premises = ['A']
ML_TH_9_conclusions = ['\\Box \\Diamond A']
ML_TH_9_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_9_example = [
    ML_TH_9_premises,
    ML_TH_9_conclusions,
    ML_TH_9_settings,
]

# ML_TH_10: 5 AXIOM (TOP)
ML_TH_10_premises = ['(\\top \\boxright \\neg A)']
ML_TH_10_conclusions = ['(\\top \\boxright (\\top \\boxright \\neg A))']
ML_TH_10_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_10_example = [
    ML_TH_10_premises,
    ML_TH_10_conclusions,
    ML_TH_10_settings,
]

# ML_TH_11: 5 AXIOM (BOX)
ML_TH_11_premises = ['\\Diamond A']
ML_TH_11_conclusions = ['\\Box \\Diamond A']
ML_TH_11_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_11_example = [
    ML_TH_11_premises,
    ML_TH_11_conclusions,
    ML_TH_11_settings,
]

# ML_TH_12: BOX-TO-TOP EQUIVALENCE
ML_TH_12_premises = ['\\Box A']
ML_TH_12_conclusions = ['(\\top \\boxright A)']
ML_TH_12_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_12_example = [
    ML_TH_12_premises,
    ML_TH_12_conclusions,
    ML_TH_12_settings,
]

# ML_TH_13: TOP-TO-BOX EQUIVALENCE
ML_TH_13_premises = ['(\\top \\boxright A)']
ML_TH_13_conclusions = ['\\Box A']
ML_TH_13_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_13_example = [
    ML_TH_13_premises,
    ML_TH_13_conclusions,
    ML_TH_13_settings,
]

# ML_TH_14: NECESSARY EQUIVALENCE OF TAUTOLOGIES
ML_TH_14_premises = []
ML_TH_14_conclusions = ['\\Box ((A \\vee \\neg A) \\leftrightarrow (B \\vee \\neg B))']
ML_TH_14_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_TH_14_example = [
    ML_TH_14_premises,
    ML_TH_14_conclusions,
    ML_TH_14_settings,
]

#################################
###### DEFINED MODAL OPERATORS ##
#################################

# ML_DEF_1: PRIMITIVE VS DEFINED NECESSITY
ML_DEF_1_premises = ['\\Box A']
ML_DEF_1_conclusions = ['\\nbox A']
ML_DEF_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_1_example = [
    ML_DEF_1_premises,
    ML_DEF_1_conclusions,
    ML_DEF_1_settings,
]

# ML_DEF_2: DEFINED VS PRIMITIVE NECESSITY
ML_DEF_2_premises = ['\\nbox A']
ML_DEF_2_conclusions = ['\\Box A']
ML_DEF_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_2_example = [
    ML_DEF_2_premises,
    ML_DEF_2_conclusions,
    ML_DEF_2_settings,
]

# ML_DEF_3: PRIMITIVE VS DEFINED POSSIBILITY
ML_DEF_3_premises = ['\\Diamond A']
ML_DEF_3_conclusions = ['\\ndiamond A']
ML_DEF_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_3_example = [
    ML_DEF_3_premises,
    ML_DEF_3_conclusions,
    ML_DEF_3_settings,
]

# ML_DEF_4: DEFINED VS PRIMITIVE POSSIBILITY
ML_DEF_4_premises = ['\\ndiamond A']
ML_DEF_4_conclusions = ['\\Diamond A']
ML_DEF_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_4_example = [
    ML_DEF_4_premises,
    ML_DEF_4_conclusions,
    ML_DEF_4_settings,
]

# ML_DEF_5: NECESSITY AND NEGATED POSSIBILITY
ML_DEF_5_premises = ['\\Box A']
ML_DEF_5_conclusions = ['\\neg \\Diamond \\neg A']
ML_DEF_5_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_5_example = [
    ML_DEF_5_premises,
    ML_DEF_5_conclusions,
    ML_DEF_5_settings,
]

# ML_DEF_6: POSSIBILITY AND NEGATED NECESSITY
ML_DEF_6_premises = ['\\Diamond A']
ML_DEF_6_conclusions = ['\\neg \\Box \\neg A']
ML_DEF_6_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
ML_DEF_6_example = [
    ML_DEF_6_premises,
    ML_DEF_6_conclusions,
    ML_DEF_6_settings,
]

# Create collections for different modal example types
modal_cm_examples = {
    "ML_CM_1": ML_CM_1_example,
    "ML_CM_2": ML_CM_2_example,
    "ML_CM_3": ML_CM_3_example,
}

modal_th_examples = {
    "ML_TH_1": ML_TH_1_example,
    "ML_TH_2": ML_TH_2_example,
    "ML_TH_3": ML_TH_3_example,
    "ML_TH_4": ML_TH_4_example,
    "ML_TH_5": ML_TH_5_example,
    "ML_TH_6": ML_TH_6_example,
    "ML_TH_7": ML_TH_7_example,
    "ML_TH_8": ML_TH_8_example,
    "ML_TH_9": ML_TH_9_example,
    "ML_TH_10": ML_TH_10_example,
    "ML_TH_11": ML_TH_11_example,
    "ML_TH_12": ML_TH_12_example,
    "ML_TH_13": ML_TH_13_example,
    "ML_TH_14": ML_TH_14_example,
}

modal_def_examples = {
    # TODO: fix these examples
    # "ML_DEF_1": ML_DEF_1_example,
    # "ML_DEF_2": ML_DEF_2_example,
    # "ML_DEF_3": ML_DEF_3_example,
    # "ML_DEF_4": ML_DEF_4_example,
    "ML_DEF_5": ML_DEF_5_example,
    "ML_DEF_6": ML_DEF_6_example,
}

# Combined collection of all modal examples
modal_examples = {**modal_cm_examples, **modal_th_examples, **modal_def_examples}

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

# # Specify which examples to run by default when running this module directly
# # All examples included by default
# example_range = modal_examples

# Or specify individual examples
example_range = {

    ### COUNTERMODELS ###

    # "ML_CM_1": ML_CM_1_example,
    # "ML_CM_2": ML_CM_2_example,
    # "ML_CM_3": ML_CM_3_example,

    ### THEOREMS ###

    # "ML_TH_1": ML_TH_1_example,
    # "ML_TH_2": ML_TH_2_example,
    # "ML_TH_3": ML_TH_3_example,
    "ML_TH_13": ML_TH_13_example,
}

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_dir)
