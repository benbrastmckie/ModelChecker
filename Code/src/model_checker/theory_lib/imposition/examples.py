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

import os
import sys

from .operators import imposition_operators  # Use the OperatorCollection
from .semantic import ImpositionSemantics, ImpositionModelStructure as ModelStructure
from model_checker.theory_lib.logos.semantic import LogosProposition as Proposition






# Standard imports

# Add current directory to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import imposition components

# Import logos theory components for comparison
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


#####################
### COUNTERMODELS ###
#####################

# IM_TR_0: TEST DERIVED IMPOSITION CONSTRAINTS
# This tests whether all derived constraints from is_alternative are entailed
# by the base semantics. If no model is found, all constraints are entailed.
IM_TR_0_premises = []
IM_TR_0_conclusions = []
IM_TR_0_settings = {
    'N' : 4,
    'contingent' : False,
    'non_null' : False,
    'non_empty' : False,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_TR_0_example = [
    IM_TR_0_premises,
    IM_TR_0_conclusions,
    IM_TR_0_settings,
]

# IM_CM_0: COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_0_premises = ['\\neg A', '(A \\diamondright C)', '(A \\boxright C)']
IM_CM_0_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_0_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 2,
    'expectation' : True,
}
IM_CM_0_example = [
    IM_CM_0_premises,
    IM_CM_0_conclusions,
    IM_CM_0_settings,
]

# IM_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_1_premises = ['\\neg A', '(A \\boxright C)']
IM_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_1_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_1_example = [
    IM_CM_1_premises,
    IM_CM_1_conclusions,
    IM_CM_1_settings,
]

# IM_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_2_premises = ['\\neg A', '(A \\diamondright C)']
IM_CM_2_conclusions = ['((A \\wedge B) \\diamondright C)']
IM_CM_2_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_2_example = [
    IM_CM_2_premises,
    IM_CM_2_conclusions,
    IM_CM_2_settings,
]

# IM_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
IM_CM_3_premises = ['\\neg A', '(A \\boxright C)', '\\Diamond (A \\wedge B)']
IM_CM_3_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_3_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_3_example = [
    IM_CM_3_premises,
    IM_CM_3_conclusions,
    IM_CM_3_settings,
]

# IM_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
IM_CM_4_premises = ['\\neg A','(A \\boxright C)']
IM_CM_4_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_4_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_4_example = [
    IM_CM_4_premises,
    IM_CM_4_conclusions,
    IM_CM_4_settings,
]

# IM_CM_5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
IM_CM_5_premises = ['(A \\boxright C)','(B \\boxright C)']
IM_CM_5_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_5_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_5_example = [
    IM_CM_5_premises,
    IM_CM_5_conclusions,
    IM_CM_5_settings,
]

# IM_CM_6: WEAKENED MONOTONICITY
IM_CM_6_premises = ['\\neg A', '(A \\boxright B)','(A \\boxright C)']
IM_CM_6_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_6_settings = {
    'N' : 3,
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
IM_CM_7_premises = ['(A \\boxright B)']
IM_CM_7_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_7_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_7_example = [
    IM_CM_7_premises,
    IM_CM_7_conclusions,
    IM_CM_7_settings,
]

# IM_CM_8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
IM_CM_8_premises = ['\\neg B','(A \\boxright B)']
IM_CM_8_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_8_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_8_example = [
    IM_CM_8_premises,
    IM_CM_8_conclusions,
    IM_CM_8_settings,
]

# IM_CM_9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
IM_CM_9_premises = ['\\neg A','\\neg B','(A \\boxright B)']
IM_CM_9_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_9_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_9_example = [
    IM_CM_9_premises,
    IM_CM_9_conclusions,
    IM_CM_9_settings,
]

# IM_CM_10: TRANSITIVITY
IM_CM_10_premises = ['(A \\boxright B)','(B \\boxright C)']
IM_CM_10_conclusions = ['(A \\boxright C)']
IM_CM_10_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_10_example = [
    IM_CM_10_premises,
    IM_CM_10_conclusions,
    IM_CM_10_settings,
]

# IM_CM_11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
IM_CM_11_premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
IM_CM_11_conclusions = ['(A \\boxright C)']
IM_CM_11_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_11_example = [
    IM_CM_11_premises,
    IM_CM_11_conclusions,
    IM_CM_11_settings,
]

# IM_CM_12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
IM_CM_12_premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
IM_CM_12_conclusions = ['(A \\boxright C)']
IM_CM_12_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 10,
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
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)',
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
IM_CM_15_conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
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
IM_CM_16_premises = ['\\neg A','(A \\boxright (B \\vee C))']
IM_CM_16_conclusions = ['(A \\boxright B)','(A \\boxright C)']
IM_CM_16_settings = {
    'N' : 4,
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
IM_CM_17_premises = ['(A \\boxright C)','(B \\boxright C)']
IM_CM_17_conclusions = ['((A \\vee B) \\boxright C)']
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
IM_CM_18_conclusions = ['(A \\boxright B)']
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
IM_CM_19_premises = ['((A \\wedge B) \\boxright C)']
IM_CM_19_conclusions = ['(A \\boxright (B \\boxright C))']
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
IM_CM_20_premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
IM_CM_20_conclusions = ['(A \\boxright (B \\boxright C))']
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
IM_CM_21_premises = ['\\neg A','\\neg (A \\boxright B)']
IM_CM_21_conclusions = ['(A \\boxright \\neg B)']
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

# IM_CM_22: REVERSE DEFINITION OF NEC
IM_CM_22_premises = ['(\\top \\boxright A)']
IM_CM_22_conclusions = ['\\Box A']
IM_CM_22_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_22_example = [
    IM_CM_22_premises,
    IM_CM_22_conclusions,
    IM_CM_22_settings,
]

# IM_CM_23: CONTRADICTION TO IMPOSSIBILITY
IM_CM_23_premises = ['(A \\boxright \\bot)']
IM_CM_23_conclusions = ['(\\top \\boxright \\neg A)']
IM_CM_23_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_23_example = [
    IM_CM_23_premises,
    IM_CM_23_conclusions,
    IM_CM_23_settings,
]

# IM_CM_24: CONTRADICTION TO IMPOSSIBILITY
IM_CM_24_premises = ['(A \\boxright B)']
IM_CM_24_conclusions = ['\\Box (A \\boxright B)']
IM_CM_24_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_24_example = [
    IM_CM_24_premises,
    IM_CM_24_conclusions,
    IM_CM_24_settings,
]

# IM_CM_25: CONTRADICTION TO IMPOSSIBILITY
IM_CM_25_premises = ['A', '\\Diamond B', '\\neg \\Diamond (A \\wedge B)']
IM_CM_25_conclusions = ['(B \\boxright C)']
IM_CM_25_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_25_example = [
    IM_CM_25_premises,
    IM_CM_25_conclusions,
    IM_CM_25_settings,
]

# IM_CM_26: IMPOSITION TO LOGOS COUNTERFACTUAL
IM_CM_26_premises = ['(A \\boxright B)']
IM_CM_26_conclusions = ['(A \\boxrightlogos B)']
IM_CM_26_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_26_example = [
    IM_CM_26_premises,
    IM_CM_26_conclusions,
    IM_CM_26_settings,
]

# IM_CM_27: LOGOS TO IMPOSITION COUNTERFACTUAL
IM_CM_27_premises = ['(A \\boxrightlogos B)']
IM_CM_27_conclusions = ['(A \\boxright B)']
IM_CM_27_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_27_example = [
    IM_CM_27_premises,
    IM_CM_27_conclusions,
    IM_CM_27_settings,
]

# IM_CM_28: REVERSE FLIP DEFINITION OF NEC
IM_CM_28_premises = ['(\\neg A \\boxright \\bot)']
IM_CM_28_conclusions = ['\\Box A']
IM_CM_28_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_28_example = [
    IM_CM_28_premises,
    IM_CM_28_conclusions,
    IM_CM_28_settings,
]

# IM_CM_29: FLIP DEFINITION OF NEC
IM_CM_29_premises = ['\\Box A']
IM_CM_29_conclusions = ['(\\neg A \\boxright \\bot)']
IM_CM_29_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
IM_CM_29_example = [
    IM_CM_29_premises,
    IM_CM_29_conclusions,
    IM_CM_29_settings,
]




##################
### THEOREMS  ###
##################

# IM_TH_1: COUNTERFACTUAL IDENTITY
IM_TH_1_premises = []
IM_TH_1_conclusions = ['(A \\boxright A)']
IM_TH_1_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_1_example = [
    IM_TH_1_premises,
    IM_TH_1_conclusions,
    IM_TH_1_settings,
]

# IM_TH_2: COUNTERFACTUAL MODUS PONENS
IM_TH_2_premises = ['A','(A \\boxright B)']
IM_TH_2_conclusions = ['B']
IM_TH_2_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_2_example = [
    IM_TH_2_premises,
    IM_TH_2_conclusions,
    IM_TH_2_settings,
]

# IM_TH_3: WEAKENED TRANSITIVITY
IM_TH_3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
IM_TH_3_conclusions = ['(A \\boxright C)']
IM_TH_3_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_3_example = [
    IM_TH_3_premises,
    IM_TH_3_conclusions,
    IM_TH_3_settings,
]

# IM_TH_4: ANTECEDENT DISJUNCTION TO CONJUNCTION
IM_TH_4_premises = ['((A \\vee B) \\boxright C)']
IM_TH_4_conclusions = ['((A \\wedge B) \\boxright C)']
IM_TH_4_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_4_example = [
    IM_TH_4_premises,
    IM_TH_4_conclusions,
    IM_TH_4_settings,
]

# IM_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_5_premises = ['((A \\vee B) \\boxright C)']
IM_TH_5_conclusions = ['(A \\boxright C)']
IM_TH_5_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_5_example = [
    IM_TH_5_premises,
    IM_TH_5_conclusions,
    IM_TH_5_settings,
]

# IM_TH_6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_6_premises = ['((A \\vee B) \\boxright C)']
IM_TH_6_conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
IM_TH_6_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
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
    '(A \\boxright C)',
    '(B \\boxright C)',
    '((A \\wedge B) \\boxright C)',
]
IM_TH_7_conclusions = ['((A \\vee B) \\boxright C)']
IM_TH_7_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_7_example = [
    IM_TH_7_premises,
    IM_TH_7_conclusions,
    IM_TH_7_settings,
]

# IM_TH_8: COUNTERFACTUAL CONSEQUENT WEAKENING
IM_TH_8_premises = ['(A \\boxright (B \\wedge C))']
IM_TH_8_conclusions = ['(A \\boxright B)']
IM_TH_8_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_8_example = [
    IM_TH_8_premises,
    IM_TH_8_conclusions,
    IM_TH_8_settings,
]

# IM_TH_9: COUNTERFACTUAL CONJUNCTION INTRODUCTION
IM_TH_9_premises = ['(A \\boxright B)','(A \\boxright C)']
IM_TH_9_conclusions = ['(A \\boxright (B \\wedge C))']
IM_TH_9_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
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
IM_TH_10_conclusions = ['(A \\diamondright B)']
IM_TH_10_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 10,
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
IM_TH_11_conclusions = ['(\\top \\boxright A)']
IM_TH_11_settings = {
    'N' : 4,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : True,
    'non_null' : True,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : False,
}
IM_TH_11_example = [
    IM_TH_11_premises,
    IM_TH_11_conclusions,
    IM_TH_11_settings,
]



# Organize examples by category
countermodel_examples = {
    "IM_CM_0": IM_CM_0_example,   # COUNTERFACTUAL AND MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
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
    "IM_CM_22": IM_CM_22_example, # REVERSE DEFINITION OF NEC
    "IM_CM_23": IM_CM_23_example, # CONTRADICTION TO IMPOSSIBILITY
    "IM_CM_24": IM_CM_24_example, # NECESSITY OF COUNTERFACTUALS
    "IM_CM_25": IM_CM_25_example, # INCOMPATIBILITY TO COUNTERFACTUAL
    "IM_CM_26": IM_CM_26_example, # IMPOSITION TO LOGOS COUNTERFACTUAL
    "IM_CM_27": IM_CM_27_example, # LOGOS TO IMPOSITION COUNTERFACTUAL
    "IM_CM_28": IM_CM_28_example, # REVERSE FLIP DEFINITION OF NEC
}

theorem_examples = {
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
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

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
    "derive_imposition": False,
}

# Create operator registry for logos theory with counterfactual operators
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

# Translation dictionary from imposition to logos operators
imposition_to_logos = {
}

# Theory definition for imposition
imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": imposition_operators,  # Use the OperatorCollection
    "dictionary": {}  # No translation needed when using imposition theory
}

# Theory definition for logos
logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": logos_registry.get_operators(),  # Returns static dict
    "dictionary": imposition_to_logos  # Translation from imposition to logos operators
}

# Specify which theories to use for comparison
# NOTE: The translation dictionary is empty as operator names are now consistent
semantic_theories = {
    "Fine": imposition_theory,
    # "Brast-McKie": logos_theory,
}

# Default example range (curated subset for direct execution)
example_range = {
    
    # COUNTERMODELS
    # "IM_CM_0": IM_CM_0_example,    # COUNTERFACTUAL AND MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_1": IM_CM_1_example,    # COUNTERFACTUAL ANTECEDENT STRENGTHENING
    # "IM_CM_2": IM_CM_2_example,    # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    # "IM_CM_3": IM_CM_3_example,    # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    # "IM_CM_4": IM_CM_4_example,    # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    # "IM_CM_5": IM_CM_5_example,    # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    # "IM_CM_6": IM_CM_6_example,    # WEAKENED MONOTONICITY
    # "IM_CM_7": IM_CM_7_example,    # COUNTERFACTUAL CONTRAPOSITION
    # "IM_CM_8": IM_CM_8_example,    # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    # "IM_CM_9": IM_CM_9_example,    # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    # "IM_CM_10": IM_CM_10_example,  # TRANSITIVITY
    # "IM_CM_11": IM_CM_11_example,  # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    # "IM_CM_12": IM_CM_12_example,  # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    # "IM_CM_13": IM_CM_13_example,  # SOBEL SEQUENCE
    # "IM_CM_14": IM_CM_14_example,  # SOBEL SEQUENCE WITH POSSIBILITY
    # "IM_CM_15": IM_CM_15_example,  # COUNTERFACTUAL EXCLUDED MIDDLE
    # "IM_CM_16": IM_CM_16_example,  # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    # "IM_CM_17": IM_CM_17_example,  # INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    # "IM_CM_18": IM_CM_18_example,  # MUST FACTIVITY
    # "IM_CM_19": IM_CM_19_example,  # COUNTERFACTUAL EXPORTATION
    # "IM_CM_20": IM_CM_20_example,  # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    # "IM_CM_21": IM_CM_21_example,  # COUNTERFACTUAL NEGATION DISTRIBUTION
    # "IM_CM_22": IM_CM_22_example,  # REVERSE DEFINITION OF NEC
    # "IM_CM_23": IM_CM_23_example,  # CONTRADICTION TO IMPOSSIBILITY
    # "IM_CM_24": IM_CM_24_example,  # NECESSITY OF COUNTERFACTUALS
    # "IM_CM_25": IM_CM_25_example,  # INCOMPATIBILITY TO COUNTERFACTUAL
    # "IM_CM_26": IM_CM_26_example,  # IMPOSITION TO LOGOS COUNTERFACTUAL
    # "IM_CM_27": IM_CM_27_example,  # LOGOS TO IMPOSITION COUNTERFACTUAL
    # "IM_CM_28": IM_CM_28_example,  # REVERSE FLIP DEFINITION OF NEC
    # "IM_CM_29": IM_CM_29_example,  # FLIP DEFINITION OF NEC
    
    # THEOREMS
    # "IM_TH_1": IM_TH_1_example,    # COUNTERFACTUAL IDENTITY
    # "IM_TH_2": IM_TH_2_example,    # COUNTERFACTUAL MODUS PONENS
    # "IM_TH_3": IM_TH_3_example,    # WEAKENED TRANSITIVITY
    # "IM_TH_4": IM_TH_4_example,    # ANTECEDENT DISJUNCTION TO CONJUNCTION
    "IM_TH_5": IM_TH_5_example,    # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    # "IM_TH_6": IM_TH_6_example,    # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    # "IM_TH_7": IM_TH_7_example,    # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    # "IM_TH_8": IM_TH_8_example,    # COUNTERFACTUAL CONSEQUENT WEAKENING
    # "IM_TH_9": IM_TH_9_example,    # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    # "IM_TH_10": IM_TH_10_example,  # MIGHT FACTIVITY
    # "IM_TH_11": IM_TH_11_example,  # DEFINITION OF NEC
    
    # SPECIAL
    # "IM_TR_0": IM_TR_0_example,  # NO PREMISES OR CONCLUSIONS
    
}



# The report will be printed by ModelRunner after all examples complete
# No atexit registration needed - the runner controls when reports print
