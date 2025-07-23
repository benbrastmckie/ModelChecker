"""
Examples Module for Imposition Theory

This module provides examples for Kit Fine's imposition semantic framework,
including both countermodels showing invalidity and theorems showing validity.

The imposition theory implements Fine's truthmaker semantics for counterfactuals
through the imposition operation, which imposes a state upon a world to create
alternative worlds. This enables a distinctive approach to counterfactual reasoning.

Example Categories:
------------------
1. Imposition Countermodels (IM_CM_*):
   - Antecedent strengthening failures
   - Transitivity failures  
   - Contraposition failures
   - Complex counterfactual patterns

2. Imposition Theorems (IM_TH_*):
   - Counterfactual identity
   - Counterfactual modus ponens
   - Weakened transitivity
   - Disjunction principles

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/examples.py
# or in development:
./dev_cli.py path/to/this/examples.py
```

To use a specific collection of examples, modify the example_range dictionary below.
"""

# Standard imports
import os
import sys

# Add current directory to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import imposition components
from .semantic import ImpositionSemantics
from .operators import imposition_operators

# Import default theory components for compatibility
from model_checker.theory_lib.default import (
    Proposition,
    ModelStructure,
)


#####################
### COUNTERMODELS ###
#####################

# IM_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_1_premises = ['\\neg A', '(A \\imposition C)']
IM_CM_1_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 2,
    'expectation' : True,
}
IM_CM_1_example = [
    IM_CM_1_premises,
    IM_CM_1_conclusions,
    IM_CM_1_settings,
]

# IM_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_2_premises = ['\\neg A', '(A \\could C)']
IM_CM_2_conclusions = ['((A \\wedge B) \\could C)']
IM_CM_2_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_2_example = [
    IM_CM_2_premises,
    IM_CM_2_conclusions,
    IM_CM_2_settings,
]

# IM_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
IM_CM_3_premises = ['\\neg A', '(A \\imposition C)', '\\Diamond (A \\wedge B)']
IM_CM_3_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_3_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_3_example = [
    IM_CM_3_premises,
    IM_CM_3_conclusions,
    IM_CM_3_settings,
]

# IM_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
IM_CM_4_premises = ['\\neg A','(A \\imposition C)']
IM_CM_4_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_4_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_4_example = [
    IM_CM_4_premises,
    IM_CM_4_conclusions,
    IM_CM_4_settings,
]

# IM_CM_5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
IM_CM_5_premises = ['(A \\imposition C)','(B \\imposition C)']
IM_CM_5_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_5_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_5_example = [
    IM_CM_5_premises,
    IM_CM_5_conclusions,
    IM_CM_5_settings,
]

# IM_CM_6: WEAKENED MONOTONICITY
IM_CM_6_premises = ['\\neg A', '(A \\imposition B)','(A \\imposition C)']
IM_CM_6_conclusions = ['((A \\wedge B) \\imposition C)']
IM_CM_6_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_6_example = [
    IM_CM_6_premises,
    IM_CM_6_conclusions,
    IM_CM_6_settings,
]

# IM_CM_7: COUNTERFACTUAL CONTRAPOSITION
IM_CM_7_premises = ['(A \\imposition B)']
IM_CM_7_conclusions = ['(\\neg B \\imposition \\neg A)']
IM_CM_7_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_7_example = [
    IM_CM_7_premises,
    IM_CM_7_conclusions,
    IM_CM_7_settings,
]

# IM_CM_8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
IM_CM_8_premises = ['\\neg B','(A \\imposition B)']
IM_CM_8_conclusions = ['(\\neg B \\imposition \\neg A)']
IM_CM_8_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_8_example = [
    IM_CM_8_premises,
    IM_CM_8_conclusions,
    IM_CM_8_settings,
]

# IM_CM_9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
IM_CM_9_premises = ['\\neg A','\\neg B','(A \\imposition B)']
IM_CM_9_conclusions = ['(\\neg B \\imposition \\neg A)']
IM_CM_9_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_9_example = [
    IM_CM_9_premises,
    IM_CM_9_conclusions,
    IM_CM_9_settings,
]

# IM_CM_10: TRANSITIVITY
IM_CM_10_premises = ['(A \\imposition B)','(B \\imposition C)']
IM_CM_10_conclusions = ['(A \\imposition C)']
IM_CM_10_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_10_example = [
    IM_CM_10_premises,
    IM_CM_10_conclusions,
    IM_CM_10_settings,
]

# IM_CM_11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
IM_CM_11_premises = ['\\neg A','(A \\imposition B)','(B \\imposition C)']
IM_CM_11_conclusions = ['(A \\imposition C)']
IM_CM_11_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_11_example = [
    IM_CM_11_premises,
    IM_CM_11_conclusions,
    IM_CM_11_settings,
]

# IM_CM_12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
IM_CM_12_premises = ['\\neg A','\\neg B','(A \\imposition B)','(B \\imposition C)']
IM_CM_12_conclusions = ['(A \\imposition C)']
IM_CM_12_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_12_example = [
    IM_CM_12_premises,
    IM_CM_12_conclusions,
    IM_CM_12_settings,
]

# IM_CM_13: SOBEL SEQUENCE
IM_CM_13_premises = [
    '(A \\imposition X)',
    '\\neg ((A \\wedge B) \\imposition X)',
    '(((A \\wedge B) \\wedge C) \\imposition X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\imposition X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\imposition X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\imposition X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\imposition X)',
]
IM_CM_13_conclusions = []
IM_CM_13_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_13_example = [
    IM_CM_13_premises,
    IM_CM_13_conclusions,
    IM_CM_13_settings,
]

# IM_CM_14: SOBEL SEQUENCE WITH POSSIBILITY
IM_CM_14_premises = [
    '\\Diamond A',
    '(A \\imposition X)',
    '\\Diamond (A \\wedge B)',
    '\\neg ((A \\wedge B) \\imposition X)',
    '\\Diamond ((A \\wedge B) \\wedge C)',
    '(((A \\wedge B) \\wedge C) \\imposition X)',
    '\\Diamond (((A \\wedge B) \\wedge C) \\wedge D)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\imposition X)',
    '\\Diamond ((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\imposition X)',
    '\\Diamond (((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\imposition X)',
    '\\Diamond ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\imposition X)',
]
IM_CM_14_conclusions = []
IM_CM_14_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_14_example = [
    IM_CM_14_premises,
    IM_CM_14_conclusions,
    IM_CM_14_settings,
]

# IM_CM_15: COUNTERFACTUAL EXCLUDED MIDDLE
IM_CM_15_premises = ['\\neg A']
IM_CM_15_conclusions = ['(A \\imposition B)','(A \\imposition \\neg B)']
IM_CM_15_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_15_example = [
    IM_CM_15_premises,
    IM_CM_15_conclusions,
    IM_CM_15_settings,
]

# IM_CM_16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
IM_CM_16_premises = ['\\neg A','(A \\imposition (B \\vee C))']
IM_CM_16_conclusions = ['(A \\imposition B)','(A \\imposition C)']
IM_CM_16_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_16_example = [
    IM_CM_16_premises,
    IM_CM_16_conclusions,
    IM_CM_16_settings,
]

# IM_CM_17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
IM_CM_17_premises = ['(A \\imposition C)','(B \\imposition C)']
IM_CM_17_conclusions = ['((A \\vee B) \\imposition C)']
IM_CM_17_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_17_example = [
    IM_CM_17_premises,
    IM_CM_17_conclusions,
    IM_CM_17_settings,
]

# IM_CM_18: MUST FACTIVITY
IM_CM_18_premises = ['A','B']
IM_CM_18_conclusions = ['(A \\imposition B)']
IM_CM_18_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_18_example = [
    IM_CM_18_premises,
    IM_CM_18_conclusions,
    IM_CM_18_settings,
]

# IM_CM_19: COUNTERFACTUAL EXPORTATION
IM_CM_19_premises = ['((A \\wedge B) \\imposition C)']
IM_CM_19_conclusions = ['(A \\imposition (B \\imposition C))']
IM_CM_19_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_19_example = [
    IM_CM_19_premises,
    IM_CM_19_conclusions,
    IM_CM_19_settings,
]

# IM_CM_20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
IM_CM_20_premises = ['((A \\wedge B) \\imposition C)','\\Diamond (A \\wedge B)']
IM_CM_20_conclusions = ['(A \\imposition (B \\imposition C))']
IM_CM_20_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 3,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_20_example = [
    IM_CM_20_premises,
    IM_CM_20_conclusions,
    IM_CM_20_settings,
]

# IM_CM_21: COUNTERFACTUAL NEGATION DISTRIBUTION
IM_CM_21_premises = ['\\neg A','\\neg (A \\imposition B)']
IM_CM_21_conclusions = ['(A \\imposition \\neg B)']
IM_CM_21_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_21_example = [
    IM_CM_21_premises,
    IM_CM_21_conclusions,
    IM_CM_21_settings,
]


##################
### THEOREMS  ###
##################

# IM_TH_1: COUNTERFACTUAL IDENTITY
IM_TH_1_premises = []
IM_TH_1_conclusions = ['(A \\imposition A)']
IM_TH_1_settings = {
    'N' : 2,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_1_example = [
    IM_TH_1_premises,
    IM_TH_1_conclusions,
    IM_TH_1_settings,
]

# IM_TH_2: COUNTERFACTUAL MODUS PONENS
IM_TH_2_premises = ['A','(A \\imposition B)']
IM_TH_2_conclusions = ['B']
IM_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_2_example = [
    IM_TH_2_premises,
    IM_TH_2_conclusions,
    IM_TH_2_settings,
]

# IM_TH_3: WEAKENED TRANSITIVITY
IM_TH_3_premises = ['(A \\imposition B)','((A \\wedge B) \\imposition C)']
IM_TH_3_conclusions = ['(A \\imposition C)']
IM_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
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
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
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
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
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
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_6_example = [
    IM_TH_6_premises,
    IM_TH_6_conclusions,
    IM_TH_6_settings,
]

# IM_TH_7: COUNTERFACTUAL DISJUNCTION INTRODUCTION
IM_TH_7_premises = [
    '(A \\imposition C)',
    '(B \\imposition C)',
    '((A \\wedge B) \\imposition C)',
]
IM_TH_7_conclusions = ['((A \\vee B) \\imposition C)']
IM_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_7_example = [
    IM_TH_7_premises,
    IM_TH_7_conclusions,
    IM_TH_7_settings,
]

# IM_TH_8: COUNTERFACTUAL CONSEQUENT WEAKENING
IM_TH_8_premises = ['(A \\imposition (B \\wedge C))']
IM_TH_8_conclusions = ['(A \\imposition B)']
IM_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_8_example = [
    IM_TH_8_premises,
    IM_TH_8_conclusions,
    IM_TH_8_settings,
]

# IM_TH_9: COUNTERFACTUAL CONJUNCTION INTRODUCTION
IM_TH_9_premises = ['(A \\imposition B)','(A \\imposition C)']
IM_TH_9_conclusions = ['(A \\imposition (B \\wedge C))']
IM_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_9_example = [
    IM_TH_9_premises,
    IM_TH_9_conclusions,
    IM_TH_9_settings,
]

# IM_TH_10: MIGHT FACTIVITY
IM_TH_10_premises = ['A','B']
IM_TH_10_conclusions = ['(A \\could B)']
IM_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_10_example = [
    IM_TH_10_premises,
    IM_TH_10_conclusions,
    IM_TH_10_settings,
]

# IM_TH_11: DEFINITION OF NEC
IM_TH_11_premises = ['\\Box A']
IM_TH_11_conclusions = ['(\\top \\imposition A)']
IM_TH_11_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_11_example = [
    IM_TH_11_premises,
    IM_TH_11_conclusions,
    IM_TH_11_settings,
]

# IM_TH_12: CONTRADICTION TO IMPOSSIBILITY
IM_TH_12_premises = ['(A \\imposition \\bot)']
IM_TH_12_conclusions = ['(\\top \\imposition \\neg A)']
IM_TH_12_settings = {
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_12_example = [
    IM_TH_12_premises,
    IM_TH_12_conclusions,
    IM_TH_12_settings,
]


# Create collections for different imposition example types
imposition_cm_examples = {
    "IM_CM_1": IM_CM_1_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_2": IM_CM_2_example,   # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_3": IM_CM_3_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    "IM_CM_4": IM_CM_4_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    "IM_CM_5": IM_CM_5_example,   # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    "IM_CM_6": IM_CM_6_example,   # WEAKENED MONOTONICITY
    "IM_CM_7": IM_CM_7_example,   # COUNTERFACTUAL CONTRAPOSITION
    "IM_CM_8": IM_CM_8_example,   # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    "IM_CM_9": IM_CM_9_example,   # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    "IM_CM_10": IM_CM_10_example, # TRANSITIVITY
    "IM_CM_11": IM_CM_11_example, # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    "IM_CM_12": IM_CM_12_example, # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    "IM_CM_13": IM_CM_13_example, # SOBEL SEQUENCE
    "IM_CM_14": IM_CM_14_example, # SOBEL SEQUENCE WITH POSSIBILITY
    "IM_CM_15": IM_CM_15_example, # COUNTERFACTUAL EXCLUDED MIDDLE
    "IM_CM_16": IM_CM_16_example, # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    "IM_CM_17": IM_CM_17_example, # INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    "IM_CM_18": IM_CM_18_example, # MUST FACTIVITY
    "IM_CM_19": IM_CM_19_example, # COUNTERFACTUAL EXPORTATION
    "IM_CM_20": IM_CM_20_example, # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    "IM_CM_21": IM_CM_21_example, # COUNTERFACTUAL NEGATION DISTRIBUTION
}

imposition_th_examples = {
    "IM_TH_1": IM_TH_1_example,   # COUNTERFACTUAL IDENTITY
    "IM_TH_2": IM_TH_2_example,   # COUNTERFACTUAL MODUS PONENS
    "IM_TH_3": IM_TH_3_example,   # WEAKENED TRANSITIVITY
    "IM_TH_4": IM_TH_4_example,   # ANTECEDENT DISJUNCTION TO CONJUNCTION
    "IM_TH_5": IM_TH_5_example,   # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "IM_TH_6": IM_TH_6_example,   # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "IM_TH_7": IM_TH_7_example,   # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    "IM_TH_8": IM_TH_8_example,   # COUNTERFACTUAL CONSEQUENT WEAKENING
    "IM_TH_9": IM_TH_9_example,   # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    "IM_TH_10": IM_TH_10_example, # MIGHT FACTIVITY
    "IM_TH_11": IM_TH_11_example, # DEFINITION OF NEC
    # "IM_TH_12": IM_TH_12_example, # CONTRADICTION TO IMPOSSIBILITY
}

# Combined collection of all imposition examples
unit_tests = {**imposition_cm_examples, **imposition_th_examples}

# Aliases for main dictionary (backward compatibility)
test_example_range = unit_tests
all_imposition_examples = unit_tests

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Theory definition for imposition
imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": imposition_operators,
}

# Specify which theories to use
semantic_theories = {
    "Fine": imposition_theory,
}

# Default example range (curated subset for direct execution)
example_range = {

    # Countermodels
    "IM_CM_1": IM_CM_1_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_2": IM_CM_2_example,   # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_3": IM_CM_3_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    "IM_CM_4": IM_CM_4_example,   # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    "IM_CM_5": IM_CM_5_example,   # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    "IM_CM_6": IM_CM_6_example,   # WEAKENED MONOTONICITY
    "IM_CM_7": IM_CM_7_example,   # COUNTERFACTUAL CONTRAPOSITION
    "IM_CM_8": IM_CM_8_example,   # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    "IM_CM_9": IM_CM_9_example,   # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    "IM_CM_10": IM_CM_10_example, # TRANSITIVITY
    "IM_CM_11": IM_CM_11_example, # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    "IM_CM_12": IM_CM_12_example, # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    "IM_CM_13": IM_CM_13_example, # SOBEL SEQUENCE
    "IM_CM_14": IM_CM_14_example, # SOBEL SEQUENCE WITH POSSIBILITY
    "IM_CM_15": IM_CM_15_example, # COUNTERFACTUAL EXCLUDED MIDDLE
    "IM_CM_16": IM_CM_16_example, # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    "IM_CM_17": IM_CM_17_example, # INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    "IM_CM_18": IM_CM_18_example, # MUST FACTIVITY
    "IM_CM_19": IM_CM_19_example, # COUNTERFACTUAL EXPORTATION
    "IM_CM_20": IM_CM_20_example, # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    "IM_CM_21": IM_CM_21_example, # COUNTERFACTUAL NEGATION DISTRIBUTION

    # Theorems
    "IM_TH_1": IM_TH_1_example,   # COUNTERFACTUAL IDENTITY
    "IM_TH_2": IM_TH_2_example,   # COUNTERFACTUAL MODUS PONENS
    "IM_TH_3": IM_TH_3_example,   # WEAKENED TRANSITIVITY
    "IM_TH_4": IM_TH_4_example,   # ANTECEDENT DISJUNCTION TO CONJUNCTION
    "IM_TH_5": IM_TH_5_example,   # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "IM_TH_6": IM_TH_6_example,   # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "IM_TH_7": IM_TH_7_example,   # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    "IM_TH_8": IM_TH_8_example,   # COUNTERFACTUAL CONSEQUENT WEAKENING
    "IM_TH_9": IM_TH_9_example,   # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    "IM_TH_10": IM_TH_10_example, # MIGHT FACTIVITY
    "IM_TH_11": IM_TH_11_example, # DEFINITION OF NEC
    "IM_TH_12": IM_TH_12_example, # CONTRADICTION TO IMPOSSIBILITY
    
}


def get_examples():
    """
    Get all imposition examples.
    
    Returns:
        dict: Dictionary containing all imposition examples
    """
    return {
        'countermodels': imposition_cm_examples,
        'theorems': imposition_th_examples,
        'all': unit_tests
    }


# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
