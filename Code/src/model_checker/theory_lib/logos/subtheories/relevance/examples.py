"""
Relevance Examples Module for Logos Theory

This module provides relevance-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Relevance Logic Countermodels (REL_CM_*):
   - Tests for invalid relevance arguments
   - Examples with the relevance operator

2. Relevance Logic Theorems (REL_TH_*):
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
from ...semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)

# Import operators
from ...operators import LogosOperatorRegistry

# REL_CM_1: ANTECEDENT STRENGTHENING
REL_CM_1_premises = []
REL_CM_1_conclusions = ['((A \\wedge B) \\preceq A)']
REL_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_1_example = [
    REL_CM_1_premises,
    REL_CM_1_conclusions,
    REL_CM_1_settings,
]

# REL_CM_2: ANTECEDENT WEAKENING
REL_CM_2_premises = []
REL_CM_2_conclusions = ['((A \\vee B) \\preceq A)']
REL_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_2_example = [
    REL_CM_2_premises,
    REL_CM_2_conclusions,
    REL_CM_2_settings,
]

# REL_CM_3: RELEVANCE TRANSITIVITY
REL_CM_3_premises = ['(A \\preceq B)', '(B \\preceq C)']
REL_CM_3_conclusions = ['(A \\preceq C)']
REL_CM_3_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_3_example = [
    REL_CM_3_premises,
    REL_CM_3_conclusions,
    REL_CM_3_settings,
]

# REL_CM_4: RELEVANT IMPLICATION: GROUND
REL_CM_4_premises = ['\\Box (A \\rightarrow B)', '(A \\preceq B)']
REL_CM_4_conclusions = ['(A \\leq B)']
REL_CM_4_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_4_example = [
    REL_CM_4_premises,
    REL_CM_4_conclusions,
    REL_CM_4_settings,
]

# REL_CM_5: RELEVANT IMPLICATION: ESSENCE
REL_CM_5_premises = ['\\Box (B \\rightarrow A)', '(A \\preceq B)']
REL_CM_5_conclusions = ['(A \\sqsubseteq B)']
REL_CM_5_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_5_example = [
    REL_CM_5_premises,
    REL_CM_5_conclusions,
    REL_CM_5_settings,
]

# REL_CM_6: RELEVANT IMPLICATION: IDENTITY
REL_CM_6_premises = ['\\Box (A \\leftrightarrow B)', '(A \\preceq B)', '(B \\preceq A)']
REL_CM_6_conclusions = ['(A \\equiv B)']
REL_CM_6_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_6_example = [
    REL_CM_6_premises,
    REL_CM_6_conclusions,
    REL_CM_6_settings,
]

# REL_CM_7: STRICT IMPLICATION
REL_CM_7_premises = ['\\Box (A \\rightarrow B)']
REL_CM_7_conclusions = ['(A \\preceq B)']
REL_CM_7_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_7_example = [
    REL_CM_7_premises,
    REL_CM_7_conclusions,
    REL_CM_7_settings,
]

# REL_CM_8: REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
REL_CM_8_premises = []
REL_CM_8_conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\preceq (A \\vee (B \\wedge C)))']
REL_CM_8_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_8_example = [
    REL_CM_8_premises,
    REL_CM_8_conclusions,
    REL_CM_8_settings,
]

# REL_CM_9: REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
REL_CM_9_premises = []
REL_CM_9_conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\preceq (A \\wedge (B \\vee C)))']
REL_CM_9_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_9_example = [
    REL_CM_9_premises,
    REL_CM_9_conclusions,
    REL_CM_9_settings,
]

# REL_CM_10: CONJUNCTION INTRODUCTION
REL_CM_10_premises = ['(A \\preceq B)']
REL_CM_10_conclusions = ['(A \\preceq (B \\wedge C))']
REL_CM_10_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_10_example = [
    REL_CM_10_premises,
    REL_CM_10_conclusions,
    REL_CM_10_settings,
]

# REL_CM_11: DISJUNCTION INTRODUCTION
REL_CM_11_premises = ['(A \\preceq B)']
REL_CM_11_conclusions = ['(A \\preceq (B \\vee C))']
REL_CM_11_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
REL_CM_11_example = [
    REL_CM_11_premises,
    REL_CM_11_conclusions,
    REL_CM_11_settings,
]

# REL_TH_1: RELEVANCE TO CONJUNCTION
REL_TH_1_premises = ['(A \\preceq B)']
REL_TH_1_conclusions = ['((A \\wedge B) \\leq B)']
REL_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_1_example = [
    REL_TH_1_premises,
    REL_TH_1_conclusions,
    REL_TH_1_settings,
]

# REL_TH_2: RELEVANCE TO DISJUNCTION
REL_TH_2_premises = ['(A \\preceq B)']
REL_TH_2_conclusions = ['((A \\vee B) \\sqsubseteq B)']
REL_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_2_example = [
    REL_TH_2_premises,
    REL_TH_2_conclusions,
    REL_TH_2_settings,
]

# REL_TH_3: CONJUNCTION TO RELEVANCE
REL_TH_3_premises = ['((A \\wedge B) \\leq B)']
REL_TH_3_conclusions = ['(A \\preceq B)']
REL_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_3_example = [
    REL_TH_3_premises,
    REL_TH_3_conclusions,
    REL_TH_3_settings,
]

# REL_TH_4: DISJUNCTION TO RELEVANCE
REL_TH_4_premises = ['((A \\vee B) \\sqsubseteq B)']
REL_TH_4_conclusions = ['(A \\preceq B)']
REL_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_4_example = [
    REL_TH_4_premises,
    REL_TH_4_conclusions,
    REL_TH_4_settings,
]

# REL_TH_5: CONJUNCTION INTRODUCTION
REL_TH_5_premises = []
REL_TH_5_conclusions = ['(A \\preceq (A \\wedge B))']
REL_TH_5_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_5_example = [
    REL_TH_5_premises,
    REL_TH_5_conclusions,
    REL_TH_5_settings,
]

# REL_TH_6: DISJUNCTION INTRODUCTION
REL_TH_6_premises = []
REL_TH_6_conclusions = ['(A \\preceq (A \\vee B))']
REL_TH_6_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_6_example = [
    REL_TH_6_premises,
    REL_TH_6_conclusions,
    REL_TH_6_settings,
]

# REL_TH_7: GROUNDING RELEVANCE
REL_TH_7_premises = ['(A \\leq B)']
REL_TH_7_conclusions = ['(A \\preceq B)']
REL_TH_7_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_7_example = [
    REL_TH_7_premises,
    REL_TH_7_conclusions,
    REL_TH_7_settings,
]

# REL_TH_8: ESSENCE RELEVANCE
REL_TH_8_premises = ['(A \\sqsubseteq B)']
REL_TH_8_conclusions = ['(A \\preceq B)']
REL_TH_8_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_8_example = [
    REL_TH_8_premises,
    REL_TH_8_conclusions,
    REL_TH_8_settings,
]

# REL_TH_9: IDENTITY RELEVANCE
REL_TH_9_premises = ['(A \\equiv B)']
REL_TH_9_conclusions = ['(A \\preceq B)']
REL_TH_9_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
REL_TH_9_example = [
    REL_TH_9_premises,
    REL_TH_9_conclusions,
    REL_TH_9_settings,
]

# Create collections for different relevance example types
relevance_cm_examples = {
    "REL_CM_1": REL_CM_1_example,  # ANTECEDENT STRENGTHENING
    "REL_CM_2": REL_CM_2_example,  # ANTECEDENT WEAKENING
    "REL_CM_3": REL_CM_3_example,  # RELEVANCE TRANSITIVITY
    "REL_CM_4": REL_CM_4_example,  # RELEVANT IMPLICATION: GROUND
    "REL_CM_5": REL_CM_5_example,  # RELEVANT IMPLICATION: ESSENCE
    "REL_CM_6": REL_CM_6_example,  # RELEVANT IMPLICATION: IDENTITY
    "REL_CM_7": REL_CM_7_example,  # STRICT IMPLICATION
    "REL_CM_8": REL_CM_8_example,  # REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
    "REL_CM_9": REL_CM_9_example,  # REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
    "REL_CM_10": REL_CM_10_example,  # CONJUNCTION INTRODUCTION
    "REL_CM_11": REL_CM_11_example,  # DISJUNCTION INTRODUCTION
}

relevance_th_examples = {
    "REL_TH_1": REL_TH_1_example,  # RELEVANCE TO CONJUNCTION
    "REL_TH_2": REL_TH_2_example,  # RELEVANCE TO DISJUNCTION
    "REL_TH_3": REL_TH_3_example,  # CONJUNCTION TO RELEVANCE
    "REL_TH_4": REL_TH_4_example,  # DISJUNCTION TO RELEVANCE
    "REL_TH_5": REL_TH_5_example,  # CONJUNCTION INTRODUCTION
    "REL_TH_6": REL_TH_6_example,  # DISJUNCTION INTRODUCTION
    "REL_TH_7": REL_TH_7_example,  # GROUNDING RELEVANCE
    "REL_TH_8": REL_TH_8_example,  # ESSENCE RELEVANCE
    "REL_TH_9": REL_TH_9_example,  # IDENTITY RELEVANCE
}

# Combined collection of all relevance examples
unit_tests = {**relevance_cm_examples, **relevance_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for relevance theory (includes modal for Box operator)
relevance_registry = LogosOperatorRegistry()
relevance_registry.load_subtheories(['extensional', 'constitutive', 'modal'])

# Define the semantic theory
relevance_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": relevance_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": relevance_theory,
}

# # Specify which examples to run by default when running this module directly
# # All examples included by default
# example_range = relevance_examples

# Or specify individual examples to run
example_range = {

    # COUNTERMODELS
    "REL_CM_1": REL_CM_1_example,  # ANTECEDENT STRENGTHENING
    "REL_CM_2": REL_CM_2_example,  # ANTECEDENT WEAKENING
    "REL_CM_3": REL_CM_3_example,  # RELEVANCE TRANSITIVITY
    "REL_CM_7": REL_CM_7_example,  # STRICT IMPLICATION

    # THEOREMS
    "REL_TH_5": REL_TH_5_example,  # CONJUNCTION INTRODUCTION
    "REL_TH_6": REL_TH_6_example,  # DISJUNCTION INTRODUCTION
    "REL_TH_7": REL_TH_7_example,  # GROUNDING RELEVANCE
    "REL_TH_8": REL_TH_8_example,  # ESSENCE RELEVANCE

}

def get_examples():
    """
    Get all relevance examples.
    
    Returns:
        dict: Dictionary containing all relevance examples
    """
    return {
        'countermodels': relevance_cm_examples,
        'theorems': relevance_th_examples,
        'all': unit_tests
    }

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
