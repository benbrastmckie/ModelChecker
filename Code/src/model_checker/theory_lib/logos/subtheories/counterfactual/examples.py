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

# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_1_premises = ['\\neg A', '(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N' : 6,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 3,
    'expectation' : True,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
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
    'iterate' : 1,
    'expectation' : True,
}
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    CF_CM_2_settings,
]

# CF_TH_1: COUNTERFACTUAL IDENTITY
CF_TH_1_premises = []
CF_TH_1_conclusions = ['(A \\boxright A)']
CF_TH_1_settings = {
    'N' : 2,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_6_example = [
    CF_TH_6_premises,
    CF_TH_6_conclusions,
    CF_TH_6_settings,
]

# CF_TH_7: COUNTERFACTUAL DISJUNCTION INTRODUCTION
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
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_7_example = [
    CF_TH_7_premises,
    CF_TH_7_conclusions,
    CF_TH_7_settings,
]

# CF_TH_8: COUNTERFACTUAL CONSEQUENT WEAKENING
CF_TH_8_premises = ['(A \\boxright (B \\wedge C))']
CF_TH_8_conclusions = ['(A \\boxright B)']
CF_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_8_example = [
    CF_TH_8_premises,
    CF_TH_8_conclusions,
    CF_TH_8_settings,
]

# CF_TH_9: COUNTERFACTUAL CONJUNCTION INTRODUCTION
CF_TH_9_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_TH_9_conclusions = ['(A \\boxright (B \\wedge C))']
CF_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
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
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_10_example = [
    CF_TH_10_premises,
    CF_TH_10_conclusions,
    CF_TH_10_settings,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
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
    'iterate' : 1,
    'expectation' : True,
}
CF_CM_20_example = [
    CF_CM_20_premises,
    CF_CM_20_conclusions,
    CF_CM_20_settings,
]

# CF_CM_21: COUNTERFACTUAL NEGATION DISTRIBUTION
CF_CM_21_premises = ['\\neg A','\\neg (A \\boxright B)']
CF_CM_21_conclusions = ['(A \\boxright \\neg B)']
CF_CM_21_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
CF_CM_21_example = [
    CF_CM_21_premises,
    CF_CM_21_conclusions,
    CF_CM_21_settings,
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
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_11_example = [
    CF_TH_11_premises,
    CF_TH_11_conclusions,
    CF_TH_11_settings,
]

# CF_TH_12: CONTRADICTION TO IMPOSSIBILITY
CF_TH_12_premises = ['(A \\boxright \\bot)']
CF_TH_12_conclusions = ['(\\top \\boxright \\neg A)']
CF_TH_12_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
CF_TH_12_example = [
    CF_TH_12_premises,
    CF_TH_12_conclusions,
    CF_TH_12_settings,
]

# Create collections for different counterfactual example types
counterfactual_cm_examples = {
    "CF_CM_1": CF_CM_1_example,  # COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "CF_CM_2": CF_CM_2_example,  # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "CF_CM_3": CF_CM_3_example,  # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    "CF_CM_4": CF_CM_4_example,  # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    "CF_CM_5": CF_CM_5_example,  # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    "CF_CM_6": CF_CM_6_example,  # WEAKENED MONOTONICITY
    "CF_CM_7": CF_CM_7_example,  # COUNTERFACTUAL CONTRAPOSITION
    "CF_CM_8": CF_CM_8_example,  # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    "CF_CM_9": CF_CM_9_example,  # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    "CF_CM_10": CF_CM_10_example,  # TRANSITIVITY
    "CF_CM_11": CF_CM_11_example,  # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    "CF_CM_12": CF_CM_12_example,  # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    "CF_CM_13": CF_CM_13_example,  # SOBEL SEQUENCE
    "CF_CM_14": CF_CM_14_example,  # SOBEL SEQUENCE WITH POSSIBILITY
    "CF_CM_15": CF_CM_15_example,  # COUNTERFACTUAL EXCLUDED MIDDLE
    "CF_CM_16": CF_CM_16_example,  # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    "CF_CM_17": CF_CM_17_example,  # INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    "CF_CM_18": CF_CM_18_example,  # MUST FACTIVITY
    "CF_CM_19": CF_CM_19_example,  # COUNTERFACTUAL EXPORTATION
    "CF_CM_20": CF_CM_20_example,  # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    "CF_CM_21": CF_CM_21_example,  # COUNTERFACTUAL NEGATION DISTRIBUTION
}

counterfactual_th_examples = {
    "CF_TH_1": CF_TH_1_example,  # COUNTERFACTUAL IDENTITY
    "CF_TH_2": CF_TH_2_example,  # COUNTERFACTUAL MODUS PONENS
    "CF_TH_3": CF_TH_3_example,  # WEAKENED TRANSITIVITY
    "CF_TH_4": CF_TH_4_example,  # ANTECEDENT DISJUNCTION TO CONJUNCTION # TODO: fix discrepancy
    "CF_TH_5": CF_TH_5_example,  # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "CF_TH_6": CF_TH_6_example,  # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "CF_TH_7": CF_TH_7_example,  # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    "CF_TH_8": CF_TH_8_example,  # COUNTERFACTUAL CONSEQUENT WEAKENING
    "CF_TH_9": CF_TH_9_example,  # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    "CF_TH_10": CF_TH_10_example,  # MIGHT FACTIVITY
    "CF_TH_11": CF_TH_11_example,  # DEFINITION OF NEC
    "CF_TH_12": CF_TH_12_example,  # CONTRADICTION TO IMPOSSIBILITY
}

# Combined collection of all counterfactual examples
unit_tests = {**counterfactual_cm_examples, **counterfactual_th_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for counterfactual theory (includes modal for Box and Diamond operators)
counterfactual_registry = LogosOperatorRegistry()
counterfactual_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

counterfactual_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": counterfactual_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": counterfactual_theory,
}

# # Specify which examples to run by default when running this module directly
# # All examples included by default
# example_range = unit_tests

# Or set specific examples
example_range = {

    # Also test a countermodel that should pass
    "CF_CM_1": CF_CM_1_example,  # COUNTERFACTUAL ANTECEDENT STRENGTHENING

    # Test some failing theorem examples
    # "CF_TH_1": CF_TH_1_example,  # COUNTERFACTUAL IDENTITY
    # "CF_TH_2": CF_TH_2_example,  # COUNTERFACTUAL MODUS PONENS
    # "CF_TH_9": CF_TH_9_example,  # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    
}


def get_examples():
    """
    Get all counterfactual examples.
    
    Returns:
        dict: Dictionary containing all counterfactual examples
    """
    return {
        'countermodels': counterfactual_cm_examples,
        'theorems': counterfactual_th_examples,
        'all': unit_tests
    }

# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
