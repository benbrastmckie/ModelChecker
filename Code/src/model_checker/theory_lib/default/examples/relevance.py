"""
Relevance Examples Module for Default Theory

This module provides relevance-specific examples for the unified semantics,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Relevance Logic Countermodels (RL_CM_*):
   - Tests for invalid relevance arguments
   - Examples with the relevance operator

2. Relevance Logic Theorems (RL_TH_*):
   - Tests for valid relevance arguments
   - Relationships between relevance and other operators

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/relevance.py
# or in development:
./dev_cli.py path/to/this/relevance.py
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

# RL_CM_1: ANTECEDENT STRENGTHENING
RL_CM_1_premises = []
RL_CM_1_conclusions = ['((A \\wedge B) \\preceq A)']
RL_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_1_example = [
    RL_CM_1_premises,
    RL_CM_1_conclusions,
    RL_CM_1_settings,
]

# RL_CM_2: ANTECEDENT WEAKENING
RL_CM_2_premises = []
RL_CM_2_conclusions = ['((A \\vee B) \\preceq A)']
RL_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_2_example = [
    RL_CM_2_premises,
    RL_CM_2_conclusions,
    RL_CM_2_settings,
]

# RL_CM_3: RELEVANCE TRANSITIVITY
RL_CM_3_premises = ['(A \\preceq B)', '(B \\preceq C)']
RL_CM_3_conclusions = ['(A \\preceq C)']
RL_CM_3_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_3_example = [
    RL_CM_3_premises,
    RL_CM_3_conclusions,
    RL_CM_3_settings,
]

# RL_CM_4: RELEVANT IMPLICATION: GROUND
RL_CM_4_premises = ['\\Box (A \\rightarrow B)', '(A \\preceq B)']
RL_CM_4_conclusions = ['(A \\leq B)']
RL_CM_4_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_4_example = [
    RL_CM_4_premises,
    RL_CM_4_conclusions,
    RL_CM_4_settings,
]

# RL_CM_5: RELEVANT IMPLICATION: ESSENCE
RL_CM_5_premises = ['\\Box (B \\rightarrow A)', '(A \\preceq B)']
RL_CM_5_conclusions = ['(A \\sqsubseteq B)']
RL_CM_5_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_5_example = [
    RL_CM_5_premises,
    RL_CM_5_conclusions,
    RL_CM_5_settings,
]

# RL_CM_6: RELEVANT IMPLICATION: IDENTITY
RL_CM_6_premises = ['\\Box (A \\leftrightarrow B)', '(A \\preceq B)', '(B \\preceq A)']
RL_CM_6_conclusions = ['(A \\equiv B)']
RL_CM_6_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_6_example = [
    RL_CM_6_premises,
    RL_CM_6_conclusions,
    RL_CM_6_settings,
]

# RL_CM_7: STRICT IMPLICATION
RL_CM_7_premises = ['\\Box (A \\rightarrow B)']
RL_CM_7_conclusions = ['(A \\preceq B)']
RL_CM_7_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_7_example = [
    RL_CM_7_premises,
    RL_CM_7_conclusions,
    RL_CM_7_settings,
]

# RL_CM_8: REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
RL_CM_8_premises = []
RL_CM_8_conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\preceq (A \\vee (B \\wedge C)))']
RL_CM_8_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_8_example = [
    RL_CM_8_premises,
    RL_CM_8_conclusions,
    RL_CM_8_settings,
]

# RL_CM_9: REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
RL_CM_9_premises = []
RL_CM_9_conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\preceq (A \\wedge (B \\vee C)))']
RL_CM_9_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_9_example = [
    RL_CM_9_premises,
    RL_CM_9_conclusions,
    RL_CM_9_settings,
]

# RL_CM_10: CONJUNCTION INTRODUCTION
RL_CM_10_premises = ['(A \\preceq B)']
RL_CM_10_conclusions = ['(A \\preceq (B \\wedge C))']
RL_CM_10_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_10_example = [
    RL_CM_10_premises,
    RL_CM_10_conclusions,
    RL_CM_10_settings,
]

# RL_CM_11: DISJUNCTION INTRODUCTION
RL_CM_11_premises = ['(A \\preceq B)']
RL_CM_11_conclusions = ['(A \\preceq (B \\vee C))']
RL_CM_11_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
RL_CM_11_example = [
    RL_CM_11_premises,
    RL_CM_11_conclusions,
    RL_CM_11_settings,
]

# RL_TH_1: RELEVANCE TO CONJUNCTION
RL_TH_1_premises = ['(A \\preceq B)']
RL_TH_1_conclusions = ['((A \\wedge B) \\leq B)']
RL_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_1_example = [
    RL_TH_1_premises,
    RL_TH_1_conclusions,
    RL_TH_1_settings,
]

# RL_TH_2: RELEVANCE TO DISJUNCTION
RL_TH_2_premises = ['(A \\preceq B)']
RL_TH_2_conclusions = ['((A \\vee B) \\sqsubseteq B)']
RL_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_2_example = [
    RL_TH_2_premises,
    RL_TH_2_conclusions,
    RL_TH_2_settings,
]

# RL_TH_3: CONJUNCTION TO RELEVANCE
RL_TH_3_premises = ['((A \\wedge B) \\leq B)']
RL_TH_3_conclusions = ['(A \\preceq B)']
RL_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_3_example = [
    RL_TH_3_premises,
    RL_TH_3_conclusions,
    RL_TH_3_settings,
]

# RL_TH_4: DISJUNCTION TO RELEVANCE
RL_TH_4_premises = ['((A \\vee B) \\sqsubseteq B)']
RL_TH_4_conclusions = ['(A \\preceq B)']
RL_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_4_example = [
    RL_TH_4_premises,
    RL_TH_4_conclusions,
    RL_TH_4_settings,
]

# RL_TH_5: CONJUNCTION INTRODUCTION
RL_TH_5_premises = []
RL_TH_5_conclusions = ['(A \\preceq (A \\wedge B))']
RL_TH_5_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_5_example = [
    RL_TH_5_premises,
    RL_TH_5_conclusions,
    RL_TH_5_settings,
]

# RL_TH_6: DISJUNCTION INTRODUCTION
RL_TH_6_premises = []
RL_TH_6_conclusions = ['(A \\preceq (A \\vee B))']
RL_TH_6_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_6_example = [
    RL_TH_6_premises,
    RL_TH_6_conclusions,
    RL_TH_6_settings,
]

# RL_TH_7: GROUNDING RELEVANCE
RL_TH_7_premises = ['(A \\leq B)']
RL_TH_7_conclusions = ['(A \\preceq B)']
RL_TH_7_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_7_example = [
    RL_TH_7_premises,
    RL_TH_7_conclusions,
    RL_TH_7_settings,
]

# RL_TH_8: ESSENCE RELEVANCE
RL_TH_8_premises = ['(A \\sqsubseteq B)']
RL_TH_8_conclusions = ['(A \\preceq B)']
RL_TH_8_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_8_example = [
    RL_TH_8_premises,
    RL_TH_8_conclusions,
    RL_TH_8_settings,
]

# RL_TH_9: IDENTITY RELEVANCE
RL_TH_9_premises = ['(A \\equiv B)']
RL_TH_9_conclusions = ['(A \\preceq B)']
RL_TH_9_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
RL_TH_9_example = [
    RL_TH_9_premises,
    RL_TH_9_conclusions,
    RL_TH_9_settings,
]

# Create collections for different relevance example types
relevance_cm_examples = {
    "RL_CM_1": RL_CM_1_example,
    "RL_CM_2": RL_CM_2_example,
    "RL_CM_3": RL_CM_3_example,
    "RL_CM_4": RL_CM_4_example,
    "RL_CM_5": RL_CM_5_example,
    "RL_CM_6": RL_CM_6_example,
    "RL_CM_7": RL_CM_7_example,
    "RL_CM_8": RL_CM_8_example,
    "RL_CM_9": RL_CM_9_example,
    "RL_CM_10": RL_CM_10_example,
    "RL_CM_11": RL_CM_11_example,
}

relevance_th_examples = {
    "RL_TH_1": RL_TH_1_example,
    "RL_TH_2": RL_TH_2_example,
    "RL_TH_3": RL_TH_3_example,
    "RL_TH_4": RL_TH_4_example,
    "RL_TH_5": RL_TH_5_example,
    "RL_TH_6": RL_TH_6_example,
    "RL_TH_7": RL_TH_7_example,
    "RL_TH_8": RL_TH_8_example,
    "RL_TH_9": RL_TH_9_example,
}

# Combined collection of all relevance examples
relevance_examples = {**relevance_cm_examples, **relevance_th_examples}

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
# All examples included by default
example_range = relevance_examples

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_dir)
