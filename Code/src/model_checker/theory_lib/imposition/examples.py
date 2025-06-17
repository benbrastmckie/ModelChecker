"""
Examples Module for Imposition Theory

This module defines a comprehensive test suite for comparing different semantic theories,
particularly focusing on counterfactual conditionals and constitutive operators.

Usage:
------
This module can be run in two ways:

1. Command Line:
   ```bash
   model-checker path/to/this/examples.py
   ```

2. IDE (VSCodium/VSCode):
   - Open this file in VSCodium/VSCode
   - Use the "Run Python File" play button in the top-right corner
   - Or right-click in the editor and select "Run Python File"

Configuration:
-------------
The examples and theories to be run can be configured by:

1. Modifying which examples are run:
   - Edit the example_range dictionary
   - Comment/uncomment specific examples
   - Modify semantic_theories to change which theories to compare

2. To add new examples:
   - Define premises, conclusions, and settings
   - Follow the naming conventions:
     - Countermodels: CF_CM_*, CL_CM_*
     - Theorems: CF_TH_*, CL_TH_*
   - Add to example_range dictionary

Module Structure:
----------------
1. Imports:
   - System utilities (os, sys)
   - Local semantic definitions (ImpositionSemantics)
   - Local operator definitions (imposition_operators)
   - Default theory components for comparison

2. Semantic Theories:
   - imposition_theory: Fine's imposition theory with components
   - default_theory: Brast-McKie's default theory (for comparison)
   - imposition_dictionary: Translation between theories

3. Example Categories:
   a) Counterfactual Countermodels (CF_CM_*):
      - Tests for invalid counterfactual arguments
      - Includes antecedent strengthening, transitivity, contraposition
      - Complex examples like Sobel sequences
   
   b) Counterfactual Theorems (CF_TH_*):
      - Tests for valid counterfactual arguments
      - Basic properties like identity and modus ponens

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

Notes:
------
- At least one semantic theory must be included in semantic_theories
- At least one example must be included in example_range
- Some examples may require adjusting the settings to produce good models

Help:
-----
More information can be found in the README.md for the imposition theory.
"""

##########################
### DEFINE THE IMPORTS ###
##########################

# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from semantic import ImpositionSemantics
from operators import imposition_operators

# Default
from model_checker.theory_lib.default import (
    Semantics,
    Proposition,
    ModelStructure,
    default_operators,
)

__all__ = [
    'general_settings',
    'example_settings',
    'imposition_theory',
    'semantic_theories',
    'test_example_range',
]


####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

# imposition_operators.add_operator(default_operators)

imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": imposition_operators,
    # base theory does not require a translation dictionary for comparison
    # since the examples are stated in the language of the default theory
}

imposition_dictionary = {
    "\\imposition" : "\\boxright",
    "\\could" : "\\diamondright",
}

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": default_operators,
    "dictionary": imposition_dictionary,
}


########################
### DEFAULT SETTINGS ###
########################

general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

example_settings = {  # defaults can be tailored to each example
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : True,
}



#####################
### COUNTERMODELS ###
#####################

# # CF_CM_0: COUNTERFACTUAL IMPORTATION
# CF_CM_0_premises = ['(A \\boxright (B \\boxright C))']
# CF_CM_0_conclusions = ['((A \\wedge B) \\boxright C)']
# CF_CM_0_settings = {
#     'N' : 6,
#     'contingent' : True,
#     'non_null' : True,
#     'non_empty' : True,
#     'disjoint' : False,
#     'max_time' : 10,
#     'expectation' : True,
# }
# CF_CM_0_example = [
#     CF_CM_0_premises,
#     CF_CM_0_conclusions,
#     CF_CM_0_settings,
# ]

# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_1_premises = ['\\neg A', '(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# IMPOSITION COUNTERMODELS (from t_imposition.py)

# IM_CM_1: IMPOSITION ANTECEDENT STRENGTHENING
IM_CM_1_premises = ['(A \\imposition C)']
IM_CM_1_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
IM_CM_1_example = [
    IM_CM_1_premises,
    IM_CM_1_conclusions,
    IM_CM_1_settings,
]

# IM_CM_2: MIGHT IMPOSITION ANTECEDENT STRENGTHENING
IM_CM_2_premises = ['(A \\could C)']
IM_CM_2_conclusions = ['((A \\wedge B) \\could C)']
IM_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
IM_CM_2_example = [
    IM_CM_2_premises,
    IM_CM_2_conclusions,
    IM_CM_2_settings,
]

# CF_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_2_premises = ['\\neg A', '(A \\diamondright C)']
CF_CM_2_conclusions = ['((A \\wedge B) \\diamondright C)']
CF_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    CF_CM_2_settings,
]

# CF_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
CF_CM_3_premises = ['\\neg A', '(A \\boxright C)', '\\Diamond (A \\wedge B)']
CF_CM_3_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_3_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_3_example = [
    CF_CM_3_premises,
    CF_CM_3_conclusions,
    CF_CM_3_settings,
]

# CF_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
CF_CM_4_premises = ['\\neg A','(A \\boxright C)']
CF_CM_4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_4_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_4_example = [
    CF_CM_4_premises,
    CF_CM_4_conclusions,
    CF_CM_4_settings,
]

# CF_CM_5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
CF_CM_5_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM_5_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_5_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_5_example = [
    CF_CM_5_premises,
    CF_CM_5_conclusions,
    CF_CM_5_settings,
]

# CF_CM_6: WEAKENED MONOTONICITY
CF_CM_6_premises = ['\\neg A', '(A \\boxright B)','(A \\boxright C)']
CF_CM_6_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_6_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_6_example = [
    CF_CM_6_premises,
    CF_CM_6_conclusions,
    CF_CM_6_settings,
]

# CF_CM_7: COUNTERFACTUAL CONTRAPOSITION
CF_CM_7_premises = ['(A \\boxright B)']
CF_CM_7_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_7_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_7_example = [
    CF_CM_7_premises,
    CF_CM_7_conclusions,
    CF_CM_7_settings,
]

# CF_CM_8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
CF_CM_8_premises = ['\\neg B','(A \\boxright B)']
CF_CM_8_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_8_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_8_example = [
    CF_CM_8_premises,
    CF_CM_8_conclusions,
    CF_CM_8_settings,
]

# CF_CM_9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
CF_CM_9_premises = ['\\neg A','\\neg B','(A \\boxright B)']
CF_CM_9_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_9_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_9_example = [
    CF_CM_9_premises,
    CF_CM_9_conclusions,
    CF_CM_9_settings,
]

# CF_CM_10: TRANSITIVITY
CF_CM_10_premises = ['(A \\boxright B)','(B \\boxright C)']
CF_CM_10_conclusions = ['(A \\boxright C)']
CF_CM_10_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_10_example = [
    CF_CM_10_premises,
    CF_CM_10_conclusions,
    CF_CM_10_settings,
]

# CF_CM_11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
CF_CM_11_premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
CF_CM_11_conclusions = ['(A \\boxright C)']
CF_CM_11_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_11_example = [
    CF_CM_11_premises,
    CF_CM_11_conclusions,
    CF_CM_11_settings,
]

# CF_CM_12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
CF_CM_12_premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
CF_CM_12_conclusions = ['(A \\boxright C)']
CF_CM_12_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_12_example = [
    CF_CM_12_premises,
    CF_CM_12_conclusions,
    CF_CM_12_settings,
]

# CF_CM_13: SOBEL SEQUENCE
CF_CM_13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)',
]
CF_CM_13_conclusions = []
CF_CM_13_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_13_example = [
    CF_CM_13_premises,
    CF_CM_13_conclusions,
    CF_CM_13_settings,
]

# CF_CM_14: SOBEL SEQUENCE WITH POSSIBILITY
CF_CM_14_premises = [
    '\\Diamond A',
    '(A \\boxright X)',
    '\\Diamond (A \\wedge B)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '\\Diamond ((A \\wedge B) \\wedge C)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\Diamond (((A \\wedge B) \\wedge C) \\wedge D)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '\\Diamond ((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\Diamond (((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '\\Diamond ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)',
]
CF_CM_14_conclusions = []
CF_CM_14_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_14_example = [
    CF_CM_14_premises,
    CF_CM_14_conclusions,
    CF_CM_14_settings,
]

# CF_CM_15: COUNTERFACTUAL EXCLUDED MIDDLE
CF_CM_15_premises = ['\\neg A']
CF_CM_15_conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
CF_CM_15_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_15_example = [
    CF_CM_15_premises,
    CF_CM_15_conclusions,
    CF_CM_15_settings,
]

# CF_CM_16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
CF_CM_16_premises = ['\\neg A','(A \\boxright (B \\vee C))']
CF_CM_16_conclusions = ['(A \\boxright B)','(A \\boxright C)']
CF_CM_16_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_16_example = [
    CF_CM_16_premises,
    CF_CM_16_conclusions,
    CF_CM_16_settings,
]

# CF_CM_17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
CF_CM_17_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM_17_conclusions = ['((A \\vee B) \\boxright C)']
CF_CM_17_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_17_example = [
    CF_CM_17_premises,
    CF_CM_17_conclusions,
    CF_CM_17_settings,
]

# CF_CM_18: MUST FACTIVITY
CF_CM_18_premises = ['A','B']
CF_CM_18_conclusions = ['(A \\boxright B)']
CF_CM_18_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_18_example = [
    CF_CM_18_premises,
    CF_CM_18_conclusions,
    CF_CM_18_settings,
]

# CF_CM_19: COUNTERFACTUAL EXPORTATION
CF_CM_19_premises = ['((A \\wedge B) \\boxright C)']
CF_CM_19_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM_19_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'expectation' : True,
}
CF_CM_19_example = [
    CF_CM_19_premises,
    CF_CM_19_conclusions,
    CF_CM_19_settings,
]

# CF_CM_20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
CF_CM_20_premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
CF_CM_20_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM_20_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'expectation' : True,
}
CF_CM_20_example = [
    CF_CM_20_premises,
    CF_CM_20_conclusions,
    CF_CM_20_settings,
]

# CF_CM_21:
CF_CM_21_premises = ['\\neg A','\\neg (A \\boxright B)']
CF_CM_21_conclusions = ['(A \\boxright \\neg B)']
CF_CM_21_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
CF_CM_21_example = [
    CF_CM_21_premises,
    CF_CM_21_conclusions,
    CF_CM_21_settings,
]




############################
### LOGICAL CONSEQUENCES ###
############################

# CF_TH_1: COUNTERFACTUAL IDENTITY
CF_TH_1_premises = []
CF_TH_1_conclusions = ['(A \\boxright A)']
CF_TH_1_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_1_example = [
    CF_TH_1_premises,
    CF_TH_1_conclusions,
    CF_TH_1_settings,
]

# CF_TH_2: COUNTERFACTUAL MODUS PONENS
CF_TH_2_premises = ['A','(A \\boxright B)']
CF_TH_2_conclusions = ['B']
CF_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_2_example = [
    CF_TH_2_premises,
    CF_TH_2_conclusions,
    CF_TH_2_settings,
]

# CF_TH_3: WEAKENED TRANSITIVITY
CF_TH_3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
CF_TH_3_conclusions = ['(A \\boxright C)']
CF_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_3_example = [
    CF_TH_3_premises,
    CF_TH_3_conclusions,
    CF_TH_3_settings,
]

# CF_TH_4: ANTECEDENT DISJUNCTION TO CONJUNCTION
CF_TH_4_premises = ['((A \\vee B) \\boxright C)']
CF_TH_4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_TH_4_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_4_example = [
    CF_TH_4_premises,
    CF_TH_4_conclusions,
    CF_TH_4_settings,
]

# CF_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
CF_TH_5_premises = ['((A \\vee B) \\boxright C)']
CF_TH_5_conclusions = ['(A \\boxright C)']
CF_TH_5_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_5_example = [
    CF_TH_5_premises,
    CF_TH_5_conclusions,
    CF_TH_5_settings,
]

# CF_TH_6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
CF_TH_6_premises = ['((A \\vee B) \\boxright C)']
CF_TH_6_conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
CF_TH_6_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_6_example = [
    CF_TH_6_premises,
    CF_TH_6_conclusions,
    CF_TH_6_settings,
]

# CF_TH_7:
CF_TH_7_premises = [
    '(A \\boxright C)',
    '(B \\boxright C)',
    '((A \\wedge B) \\boxright C)',
]
CF_TH_7_conclusions = ['((A \\vee B) \\boxright C)']
CF_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_7_example = [
    CF_TH_7_premises,
    CF_TH_7_conclusions,
    CF_TH_7_settings,
]

# CF_TH_8:
CF_TH_8_premises = ['(A \\boxright (B \\wedge C))']
CF_TH_8_conclusions = ['(A \\boxright B)']
CF_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_8_example = [
    CF_TH_8_premises,
    CF_TH_8_conclusions,
    CF_TH_8_settings,
]

# CF_TH_9:
CF_TH_9_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_TH_9_conclusions = ['(A \\boxright (B \\wedge C))']
CF_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_9_example = [
    CF_TH_9_premises,
    CF_TH_9_conclusions,
    CF_TH_9_settings,
]

# CF_TH_10: MIGHT FACTIVITY
CF_TH_10_premises = ['A','B']
CF_TH_10_conclusions = ['(A \\diamondright B)']
CF_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_10_example = [
    CF_TH_10_premises,
    CF_TH_10_conclusions,
    CF_TH_10_settings,
]

# IMPOSITION THEOREMS (from t_imposition.py)

# IM_TH_1: IMPOSITION IDENTITY
IM_TH_1_premises = []
IM_TH_1_conclusions = ['(A \\imposition A)']
IM_TH_1_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_1_example = [
    IM_TH_1_premises,
    IM_TH_1_conclusions,
    IM_TH_1_settings,
]

# IM_TH_2: IMPOSITION MODUS PONENS
IM_TH_2_premises = ['A', '(A \\imposition B)']
IM_TH_2_conclusions = ['B']
IM_TH_2_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_2_example = [
    IM_TH_2_premises,
    IM_TH_2_conclusions,
    IM_TH_2_settings,
]

# IM_TH_3: WEAKENED TRANSITIVITY
IM_TH_3_premises = ['(A \\imposition B)', '((A \\wedge B) \\imposition C)']
IM_TH_3_conclusions = ['(A \\imposition C)']
IM_TH_3_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_3_example = [
    IM_TH_3_premises,
    IM_TH_3_conclusions,
    IM_TH_3_settings,
]

# IM_TH_4: ANTECEDENT DISJUNCTION TO CONJUNCTION
IM_TH_4_premises = ['((A \\vee B) \\imposition C)']
IM_TH_4_conclusions = ['((A \\wedge B) \\imposition C)']
IM_TH_4_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_4_example = [
    IM_TH_4_premises,
    IM_TH_4_conclusions,
    IM_TH_4_settings,
]

# IM_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_5_premises = ['((A \\vee B) \\imposition C)']
IM_TH_5_conclusions = ['(A \\imposition C)']
IM_TH_5_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_5_example = [
    IM_TH_5_premises,
    IM_TH_5_conclusions,
    IM_TH_5_settings,
]

# IM_TH_6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_6_premises = ['((A \\vee B) \\imposition C)']
IM_TH_6_conclusions = ['((A \\imposition C) \\wedge (B \\imposition C))']
IM_TH_6_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_6_example = [
    IM_TH_6_premises,
    IM_TH_6_conclusions,
    IM_TH_6_settings,
]

# IM_TH_10: MIGHT COUNTERFACTUAL FACTIVITY
IM_TH_10_premises = ['A', 'B']
IM_TH_10_conclusions = ['(A \\could B)']
IM_TH_10_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
IM_TH_10_example = [
    IM_TH_10_premises,
    IM_TH_10_conclusions,
    IM_TH_10_settings,
]

# CF_TH_11: DEFINITION OF NEC
CF_TH_11_premises = ['\\Box A']
CF_TH_11_conclusions = ['(\\top \\boxright A)']
CF_TH_11_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_11_example = [
    CF_TH_11_premises,
    CF_TH_11_conclusions,
    CF_TH_11_settings,
]

# CF_TH_12: DEFINITION OF MUST COUNTERFACTUAL
CF_TH_12_premises = ['(\\neg A \\boxright \\bot)']
CF_TH_12_conclusions = ['(\\top \\boxright A)']
CF_TH_12_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_12_example = [
    CF_TH_12_premises,
    CF_TH_12_conclusions,
    CF_TH_12_settings,
]


###############################################
### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###
###############################################

# NOTE: at least one theory is required, multiple are permitted for comparison
semantic_theories = {
    "Fine" : imposition_theory,
    "Brast-McKie" : default_theory,
    # additional theories will require their own translation dictionaries
}

test_example_range = {
    # Counterfactual Countermodels
    "CF_CM_1" : CF_CM_1_example,
    "CF_CM_2" : CF_CM_2_example,
    "CF_CM_3" : CF_CM_3_example,
    "CF_CM_4" : CF_CM_4_example,
    "CF_CM_5" : CF_CM_5_example,
    "CF_CM_6" : CF_CM_6_example,
    "CF_CM_7" : CF_CM_7_example,
    "CF_CM_8" : CF_CM_8_example,
    "CF_CM_9" : CF_CM_9_example,
    "CF_CM_10" : CF_CM_10_example,
    "CF_CM_11" : CF_CM_11_example,
    "CF_CM_12" : CF_CM_12_example,
    "CF_CM_13" : CF_CM_13_example,
    "CF_CM_14" : CF_CM_14_example,
    "CF_CM_15" : CF_CM_15_example,
    "CF_CM_16" : CF_CM_16_example,
    "CF_CM_17" : CF_CM_17_example,
    "CF_CM_18" : CF_CM_18_example,
    "CF_CM_19" : CF_CM_19_example,
    "CF_CM_20" : CF_CM_20_example,
    "CF_CM_21" : CF_CM_21_example,

    # Counterfactual Theorems
    "CF_TH_1" : CF_TH_1_example,
    "CF_TH_2" : CF_TH_2_example,
    "CF_TH_3" : CF_TH_3_example,
    "CF_TH_4" : CF_TH_4_example,
    "CF_TH_5" : CF_TH_5_example,
    "CF_TH_6" : CF_TH_6_example,
    "CF_TH_7" : CF_TH_7_example,
    "CF_TH_8" : CF_TH_8_example,
    "CF_TH_9" : CF_TH_9_example,
    "CF_TH_10" : CF_TH_10_example,
    "CF_TH_11" : CF_TH_11_example,
    "CF_TH_12" : CF_TH_12_example,

    # Imposition Countermodels
    "IM_CM_1" : IM_CM_1_example,
    "IM_CM_2" : IM_CM_2_example,

    # Imposition Theorems
    "IM_TH_1" : IM_TH_1_example,
    "IM_TH_2" : IM_TH_2_example,
    "IM_TH_3" : IM_TH_3_example,
    "IM_TH_4" : IM_TH_4_example,
    "IM_TH_5" : IM_TH_5_example,
    "IM_TH_6" : IM_TH_6_example,
    "IM_TH_10" : IM_TH_10_example,
}

# NOTE: at least one example is required, multiple are permitted for comparison
example_range = {
    # Counterfactual Countermodels
    # "CF_CM_1" : CF_CM_1_example,
    # "CF_CM_2" : CF_CM_2_example,
    # "CF_CM_3" : CF_CM_3_example,
    # "CF_CM_4" : CF_CM_4_example,
    # "CF_CM_5" : CF_CM_5_example,
    # "CF_CM_6" : CF_CM_6_example,
    # "CF_CM_7" : CF_CM_7_example,
    # "CF_CM_8" : CF_CM_8_example,
    # "CF_CM_9" : CF_CM_9_example,
    # "CF_CM_10" : CF_CM_10_example,
    # "CF_CM_11" : CF_CM_11_example,
    # "CF_CM_12" : CF_CM_12_example,
    # "CF_CM_13" : CF_CM_13_example,
    # "CF_CM_14" : CF_CM_14_example,
    # "CF_CM_15" : CF_CM_15_example,
    # "CF_CM_16" : CF_CM_16_example,
    # "CF_CM_17" : CF_CM_17_example,
    # "CF_CM_18" : CF_CM_18_example,
    # "CF_CM_19" : CF_CM_19_example,
    # "CF_CM_20" : CF_CM_20_example,
    # "CF_CM_21" : CF_CM_21_example,

    # Counterfactual Theorems
    # "CF_TH_1" : CF_TH_1_example,
    # "CF_TH_2" : CF_TH_2_example,
    # "CF_TH_3" : CF_TH_3_example,
    # "CF_TH_4" : CF_TH_4_example,
    # "CF_TH_5" : CF_TH_5_example,
    # "CF_TH_6" : CF_TH_6_example,
    # "CF_TH_7" : CF_TH_7_example,
    # "CF_TH_8" : CF_TH_8_example,
    # "CF_TH_9" : CF_TH_9_example,
    # "CF_TH_10" : CF_TH_10_example,
    # "CF_TH_11" : CF_TH_11_example,
    # "CF_TH_12" : CF_TH_12_example,

    # Imposition Countermodels
    "IM_CM_1" : IM_CM_1_example,
    "IM_CM_2" : IM_CM_2_example,

    # Imposition Theorems
    "IM_TH_1" : IM_TH_1_example,
    "IM_TH_3" : IM_TH_3_example,
    # "IM_TH_4" : IM_TH_4_example,
    # "IM_TH_5" : IM_TH_5_example,
    # "IM_TH_6" : IM_TH_6_example,
    # "IM_TH_10" : IM_TH_10_example,
}



####################
### RUN EXAMPLES ###
####################

if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
