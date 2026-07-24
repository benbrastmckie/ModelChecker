"""
Complex imposition theory examples.

This module contains more advanced examples for imposition theory,
including complex patterns like Sobel sequences, transitivity cases,
and advanced theorem demonstrations.
"""

from typing import Dict, List, Any


# Complex countermodels (IM_CM_10 through IM_CM_28)

# EXAMPLE IM_CM_10: TRANSITIVITY
IM_CM_10_premises = ['(A \\boxright B)','(B \\boxright C)']
IM_CM_10_conclusions = ['(A \\boxright C)']
IM_CM_10_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_10_example = [
    IM_CM_10_premises,
    IM_CM_10_conclusions,
    IM_CM_10_settings,
]

# EXAMPLE IM_CM_11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
IM_CM_11_premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
IM_CM_11_conclusions = ['(A \\boxright C)']
IM_CM_11_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_11_example = [
    IM_CM_11_premises,
    IM_CM_11_conclusions,
    IM_CM_11_settings,
]

# EXAMPLE IM_CM_12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
IM_CM_12_premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
IM_CM_12_conclusions = ['(A \\boxright C)']
IM_CM_12_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_12_example = [
    IM_CM_12_premises,
    IM_CM_12_conclusions,
    IM_CM_12_settings,
]

# EXAMPLE IM_CM_13: SOBEL SEQUENCE
IM_CM_13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)',
]
IM_CM_13_conclusions = ['\\bot']
IM_CM_13_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_13_example = [
    IM_CM_13_premises,
    IM_CM_13_conclusions,
    IM_CM_13_settings,
]

# EXAMPLE IM_CM_14: SOBEL SEQUENCE WITH POSSIBILITY
IM_CM_14_premises = [
    '\\Diamond A',
    '\\Diamond B',
    '\\Diamond C',
    '\\Diamond D',
    '\\Diamond E',
    '\\Diamond F',
    '\\Diamond G',
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)',
]
IM_CM_14_conclusions = ['\\bot']
IM_CM_14_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_14_example = [
    IM_CM_14_premises,
    IM_CM_14_conclusions,
    IM_CM_14_settings,
]

# EXAMPLE IM_CM_15: COUNTERFACTUAL EXCLUDED MIDDLE
IM_CM_15_premises = []
IM_CM_15_conclusions = ['((A \\boxright B) \\vee (A \\boxright \\neg B))']
IM_CM_15_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_15_example = [
    IM_CM_15_premises,
    IM_CM_15_conclusions,
    IM_CM_15_settings,
]

# EXAMPLE IM_CM_16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
IM_CM_16_premises = ['(A \\boxright (B \\vee C))']
IM_CM_16_conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']
IM_CM_16_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_16_example = [
    IM_CM_16_premises,
    IM_CM_16_conclusions,
    IM_CM_16_settings,
]

# EXAMPLE IM_CM_17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
IM_CM_17_premises = ['(A \\boxright C)','(B \\boxright C)']
IM_CM_17_conclusions = ['((A \\vee B) \\boxright C)']
IM_CM_17_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_17_example = [
    IM_CM_17_premises,
    IM_CM_17_conclusions,
    IM_CM_17_settings,
]

# EXAMPLE IM_CM_18: MUST FACTIVITY
IM_CM_18_premises = ['(\\top \\boxright A)']
IM_CM_18_conclusions = ['\\Box A']
IM_CM_18_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_18_example = [
    IM_CM_18_premises,
    IM_CM_18_conclusions,
    IM_CM_18_settings,
]

# EXAMPLE IM_CM_19: COUNTERFACTUAL EXPORTATION
IM_CM_19_premises = ['((A \\wedge B) \\boxright C)']
IM_CM_19_conclusions = ['(A \\boxright (B \\boxright C))']
IM_CM_19_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_19_example = [
    IM_CM_19_premises,
    IM_CM_19_conclusions,
    IM_CM_19_settings,
]

# EXAMPLE IM_CM_20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
IM_CM_20_premises = ['\\Diamond A','\\Diamond B','\\Diamond C','((A \\wedge B) \\boxright C)']
IM_CM_20_conclusions = ['(A \\boxright (B \\boxright C))']
IM_CM_20_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_20_example = [
    IM_CM_20_premises,
    IM_CM_20_conclusions,
    IM_CM_20_settings,
]

# EXAMPLE IM_CM_21: COUNTERFACTUAL NEGATION DISTRIBUTION
IM_CM_21_premises = ['(\\neg A \\boxright \\neg B)']
IM_CM_21_conclusions = ['(B \\boxright A)']
IM_CM_21_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_21_example = [
    IM_CM_21_premises,
    IM_CM_21_conclusions,
    IM_CM_21_settings,
]

# EXAMPLE IM_CM_22: REVERSE DEFINITION OF NEC
IM_CM_22_premises = ['(\\top \\boxright A)']
IM_CM_22_conclusions = ['\\Box A']
IM_CM_22_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_22_example = [
    IM_CM_22_premises,
    IM_CM_22_conclusions,
    IM_CM_22_settings,
]

# EXAMPLE IM_CM_23: CONTRADICTION TO IMPOSSIBILITY
IM_CM_23_premises = ['(\\bot \\boxright A)']
IM_CM_23_conclusions = ['\\neg \\Diamond A']
IM_CM_23_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_23_example = [
    IM_CM_23_premises,
    IM_CM_23_conclusions,
    IM_CM_23_settings,
]

# EXAMPLE IM_CM_24: NECESSITY OF COUNTERFACTUALS
IM_CM_24_premises = ['(A \\boxright B)']
IM_CM_24_conclusions = ['\\Box (A \\boxright B)']
IM_CM_24_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_24_example = [
    IM_CM_24_premises,
    IM_CM_24_conclusions,
    IM_CM_24_settings,
]

# EXAMPLE IM_CM_25: INCOMPATIBILITY TO COUNTERFACTUAL
IM_CM_25_premises = ['\\neg \\Diamond (A \\wedge B)']
IM_CM_25_conclusions = ['(A \\boxright \\neg B)']
IM_CM_25_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': False,  # This is actually a valid argument, not a countermodel
}

IM_CM_25_example = [
    IM_CM_25_premises,
    IM_CM_25_conclusions,
    IM_CM_25_settings,
]

# EXAMPLE IM_CM_26: IMPOSITION TO LOGOS COUNTERFACTUAL
IM_CM_26_premises = ['(A \\boxright B)']
IM_CM_26_conclusions = ['(A \\rightarrow B)']
IM_CM_26_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': False,  # This is actually a valid argument, not a countermodel
}

IM_CM_26_example = [
    IM_CM_26_premises,
    IM_CM_26_conclusions,
    IM_CM_26_settings,
]

# EXAMPLE IM_CM_27: LOGOS TO IMPOSITION COUNTERFACTUAL
IM_CM_27_premises = ['(A \\rightarrow B)']
IM_CM_27_conclusions = ['(A \\boxright B)']
IM_CM_27_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}

IM_CM_27_example = [
    IM_CM_27_premises,
    IM_CM_27_conclusions,
    IM_CM_27_settings,
]

# EXAMPLE IM_CM_28: REVERSE FLIP DEFINITION OF NEC
IM_CM_28_premises = ['\\neg (\\bot \\boxright \\neg A)']
IM_CM_28_conclusions = ['\\Box A']
IM_CM_28_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': False,  # This is actually a valid argument, not a countermodel
}

IM_CM_28_example = [
    IM_CM_28_premises,
    IM_CM_28_conclusions,
    IM_CM_28_settings,
]


# Complex theorems (IM_TH_6 through IM_TH_11)

# EXAMPLE IM_TH_6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
IM_TH_6_premises = ['((A \\vee B) \\boxright C)']
IM_TH_6_conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
IM_TH_6_settings = {
    'N': 4,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_6_example = [
    IM_TH_6_premises,
    IM_TH_6_conclusions,
    IM_TH_6_settings,
]

# EXAMPLE IM_TH_7: COUNTERFACTUAL DISJUNCTION INTRODUCTION
IM_TH_7_premises = [
    '((A \\boxright C) \\wedge (B \\boxright C))',
    '\\Diamond A',
    '\\Diamond B',
]
IM_TH_7_conclusions = ['((A \\vee B) \\boxright C)']
IM_TH_7_settings = {
    'N': 4,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'expectation': True,  # This actually has a countermodel, not a valid argument
}

IM_TH_7_example = [
    IM_TH_7_premises,
    IM_TH_7_conclusions,
    IM_TH_7_settings,
]

# EXAMPLE IM_TH_8: COUNTERFACTUAL CONSEQUENT WEAKENING
IM_TH_8_premises = ['(A \\boxright (B \\wedge C))']
IM_TH_8_conclusions = ['(A \\boxright B)']
IM_TH_8_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_8_example = [
    IM_TH_8_premises,
    IM_TH_8_conclusions,
    IM_TH_8_settings,
]

# EXAMPLE IM_TH_9: COUNTERFACTUAL CONJUNCTION INTRODUCTION
IM_TH_9_premises = ['(A \\boxright B)','(A \\boxright C)']
IM_TH_9_conclusions = ['(A \\boxright (B \\wedge C))']
IM_TH_9_settings = {
    'N': 4,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_9_example = [
    IM_TH_9_premises,
    IM_TH_9_conclusions,
    IM_TH_9_settings,
]

# EXAMPLE IM_TH_10: MIGHT FACTIVITY
IM_TH_10_premises = ['A','B']
IM_TH_10_conclusions = ['(A \\diamondright B)']
IM_TH_10_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_10_example = [
    IM_TH_10_premises,
    IM_TH_10_conclusions,
    IM_TH_10_settings,
]

# EXAMPLE IM_TH_11: DEFINITION OF NEC
IM_TH_11_premises = ['\\Box A']
IM_TH_11_conclusions = ['(\\top \\boxright A)']
IM_TH_11_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TH_11_example = [
    IM_TH_11_premises,
    IM_TH_11_conclusions,
    IM_TH_11_settings,
]


# Organize complex examples by category
complex_countermodels = {
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

complex_theorems = {
    "IM_TH_6": IM_TH_6_example,   # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    "IM_TH_7": IM_TH_7_example,   # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    "IM_TH_8": IM_TH_8_example,   # COUNTERFACTUAL CONSEQUENT WEAKENING
    "IM_TH_9": IM_TH_9_example,   # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    "IM_TH_10": IM_TH_10_example, # MIGHT FACTIVITY
    "IM_TH_11": IM_TH_11_example, # DEFINITION OF NEC
}

# Combined complex examples
complex_examples = {**complex_countermodels, **complex_theorems}