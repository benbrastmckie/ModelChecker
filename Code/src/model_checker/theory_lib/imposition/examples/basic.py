"""
Basic imposition theory examples.

This module contains the fundamental examples for imposition theory,
including basic countermodels and theorems that demonstrate core
properties of Fine's imposition semantics.
"""

from typing import Dict, List, Any


# Basic countermodels (IM_CM_0 through IM_CM_9)

# EXAMPLE IM_CM_0: COUNTERFACTUAL AND MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_0_premises = ['\\neg A', '(A \\diamondright C)', '(A \\boxright C)']
IM_CM_0_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_0_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_0_example = [
    IM_CM_0_premises,
    IM_CM_0_conclusions,
    IM_CM_0_settings,
]

# EXAMPLE IM_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_1_premises = ['\\neg A', '(A \\boxright C)']
IM_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_1_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_1_example = [
    IM_CM_1_premises,
    IM_CM_1_conclusions,
    IM_CM_1_settings,
]

# EXAMPLE IM_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
IM_CM_2_premises = ['\\neg A', '(A \\diamondright C)']
IM_CM_2_conclusions = ['((A \\wedge B) \\diamondright C)']
IM_CM_2_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_2_example = [
    IM_CM_2_premises,
    IM_CM_2_conclusions,
    IM_CM_2_settings,
]

# EXAMPLE IM_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
IM_CM_3_premises = ['\\neg A', '(A \\boxright C)', '\\Diamond (A \\wedge B)']
IM_CM_3_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_3_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_3_example = [
    IM_CM_3_premises,
    IM_CM_3_conclusions,
    IM_CM_3_settings,
]

# EXAMPLE IM_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
IM_CM_4_premises = ['\\neg A','(A \\boxright C)']
IM_CM_4_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_4_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_4_example = [
    IM_CM_4_premises,
    IM_CM_4_conclusions,
    IM_CM_4_settings,
]

# EXAMPLE IM_CM_5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
IM_CM_5_premises = ['(A \\boxright C)','(B \\boxright C)']
IM_CM_5_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_5_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_5_example = [
    IM_CM_5_premises,
    IM_CM_5_conclusions,
    IM_CM_5_settings,
]

# EXAMPLE IM_CM_6: WEAKENED MONOTONICITY
IM_CM_6_premises = ['\\neg A', '(A \\boxright B)','(A \\boxright C)']
IM_CM_6_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_6_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_6_example = [
    IM_CM_6_premises,
    IM_CM_6_conclusions,
    IM_CM_6_settings,
]

# EXAMPLE IM_CM_7: COUNTERFACTUAL CONTRAPOSITION
IM_CM_7_premises = ['(A \\boxright B)']
IM_CM_7_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_7_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_7_example = [
    IM_CM_7_premises,
    IM_CM_7_conclusions,
    IM_CM_7_settings,
]

# EXAMPLE IM_CM_8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
IM_CM_8_premises = ['\\neg A', '(A \\boxright B)']
IM_CM_8_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_8_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_8_example = [
    IM_CM_8_premises,
    IM_CM_8_conclusions,
    IM_CM_8_settings,
]

# EXAMPLE IM_CM_9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
IM_CM_9_premises = ['\\neg A', '\\neg B', '(A \\boxright B)']
IM_CM_9_conclusions = ['(\\neg B \\boxright \\neg A)']
IM_CM_9_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_CM_9_example = [
    IM_CM_9_premises,
    IM_CM_9_conclusions,
    IM_CM_9_settings,
]


# Basic theorems (IM_TH_1 through IM_TH_5)

# EXAMPLE IM_TH_1: COUNTERFACTUAL IDENTITY
IM_TH_1_premises = []
IM_TH_1_conclusions = ['(A \\boxright A)']
IM_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_1_example = [
    IM_TH_1_premises,
    IM_TH_1_conclusions,
    IM_TH_1_settings,
]

# EXAMPLE IM_TH_2: COUNTERFACTUAL MODUS PONENS
IM_TH_2_premises = ['A','(A \\boxright B)']
IM_TH_2_conclusions = ['B']
IM_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_2_example = [
    IM_TH_2_premises,
    IM_TH_2_conclusions,
    IM_TH_2_settings,
]

# EXAMPLE IM_TH_3: WEAKENED TRANSITIVITY
IM_TH_3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
IM_TH_3_conclusions = ['(A \\boxright C)']
IM_TH_3_settings = {
    'N': 4,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_3_example = [
    IM_TH_3_premises,
    IM_TH_3_conclusions,
    IM_TH_3_settings,
]

# EXAMPLE IM_TH_4: ANTECEDENT DISJUNCTION TO CONJUNCTION
IM_TH_4_premises = ['((A \\vee B) \\boxright C)']
IM_TH_4_conclusions = ['((A \\wedge B) \\boxright C)']
IM_TH_4_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_4_example = [
    IM_TH_4_premises,
    IM_TH_4_conclusions,
    IM_TH_4_settings,
]

# EXAMPLE IM_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_5_premises = ['((A \\vee B) \\boxright C)']
IM_TH_5_conclusions = ['(A \\boxright C)']
IM_TH_5_settings = {
    'N': 4,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_5_example = [
    IM_TH_5_premises,
    IM_TH_5_conclusions,
    IM_TH_5_settings,
]


# Organize basic examples by category
basic_countermodels = {
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
}

basic_theorems = {
    "IM_TH_1": IM_TH_1_example,   # COUNTERFACTUAL IDENTITY
    "IM_TH_2": IM_TH_2_example,   # COUNTERFACTUAL MODUS PONENS
    "IM_TH_3": IM_TH_3_example,   # WEAKENED TRANSITIVITY
    "IM_TH_4": IM_TH_4_example,   # ANTECEDENT DISJUNCTION TO CONJUNCTION
    "IM_TH_5": IM_TH_5_example,   # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
}

# Combined basic examples
basic_examples = {**basic_countermodels, **basic_theorems}