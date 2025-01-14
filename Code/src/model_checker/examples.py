"""
INSTRUCTIONS: this module defines the semantic_theories and example_range.
From the ../Code/ directory, run: python -m src.model_checker src/model_checker/example.py
"""

##########################
### DEFINE THE IMPORTS ###
##########################

from src.model_checker.semantic import (
    Semantics,
    ImpositionSemantics,
    Proposition,
)

from src.model_checker.defined import (
    ConditionalOperator, BiconditionalOperator, # extensional defined
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    MightCounterfactualOperator, # counterfactual
    MightImpositionOperator,
)

from src.model_checker.primitive import (
    AndOperator, NegationOperator, OrOperator, # extensional
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    NecessityOperator, PossibilityOperator, # modal
    CounterfactualOperator, # counterfactual
    ImpositionOperator, # counterfactual
)

from src.model_checker import syntactic



####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

default_operators = syntactic.OperatorCollection(
    AndOperator, NegationOperator, OrOperator, # extensional
    ConditionalOperator, BiconditionalOperator, # extensional defined
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    NecessityOperator, PossibilityOperator, # modal
    CounterfactualOperator, MightCounterfactualOperator, # counterfactual
    ImpositionOperator, MightImpositionOperator, # Fine
)

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "operators": default_operators,
}

imposition_dictionary = {
    "\\boxright" : "\\imposition",
    "\\circleright" : "\\could",
}

imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "operators": default_operators,
    "dictionary": imposition_dictionary,
}

semantic_theories = {
    "Brast-McKie" : default_theory,
    "Fine" : imposition_theory,
}



#######################
### DEFINE SETTINGS ###
#######################

general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "save_output": False,
}

example_settings = {
    'N' : 3,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'max_time' : 1,
}

#####################
### COUNTERMODELS ###
#####################

# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_1_premises = ['(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# CF_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_2_premises = ['(A \\circleright C)']
CF_CM_2_conclusions = ['((A \\wedge B) \\circleright C)']
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    example_settings,
]

# CF_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
CF_CM_3_premises = ['(A \\boxright C)', '\\Diamond (A \\wedge B)']
CF_CM_3_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_3_example = [
    CF_CM_3_premises,
    CF_CM_3_conclusions,
    example_settings,
]

# CF_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# N = 4
CF_CM_4_premises = ['\\neg A','(A \\boxright C)']
CF_CM_4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_4_example = [
    CF_CM_4_premises,
    CF_CM_4_conclusions,
    example_settings,
]

# CF_CM_5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# N = 4
CF_CM_5_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM_5_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_5_example = [
    CF_CM_5_premises,
    CF_CM_5_conclusions,
    example_settings,
]

# CF_CM_6: WEAKENED MONOTONICITY
# N = 3
CF_CM_6_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_CM_6_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_6_example = [
    CF_CM_6_premises,
    CF_CM_6_conclusions,
    example_settings,
]
# settings['contingent'] = False

# CF_CM_7: COUNTERFACTUAL CONTRAPOSITION
# N = 3
CF_CM_7_premises = ['(A \\boxright B)']
CF_CM_7_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_7_example = [
    CF_CM_7_premises,
    CF_CM_7_conclusions,
    example_settings,
]

# CF_CM_8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# N = 4
CF_CM_8_premises = ['\\neg B','(A \\boxright B)']
CF_CM_8_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_8_example = [
    CF_CM_8_premises,
    CF_CM_8_conclusions,
    example_settings,
]

# CF_CM_9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
CF_CM_9_premises = ['\\neg A','\\neg B','(A \\boxright B)']
CF_CM_9_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_9_example = [
    CF_CM_9_premises,
    CF_CM_9_conclusions,
    example_settings,
]

# CF_CM_10: TRANSITIVITY
# N = 3
CF_CM_10_premises = ['(A \\boxright B)','(B \\boxright C)']
CF_CM_10_conclusions = ['(A \\boxright C)']
CF_CM_10_example = [
    CF_CM_10_premises,
    CF_CM_10_conclusions,
    example_settings,
]

# CF_CM_11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# N = 3
CF_CM_11_premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
CF_CM_11_conclusions = ['(A \\boxright C)']
CF_CM_11_example = [
    CF_CM_11_premises,
    CF_CM_11_conclusions,
    example_settings,
]

# CF_CM_12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
CF_CM_12_premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
CF_CM_12_conclusions = ['(A \\boxright C)']
CF_CM_12_example = [
    CF_CM_12_premises,
    CF_CM_12_conclusions,
    example_settings,
]

# CF_CM_13: SOBEL SEQUENCE
# N = 3
CF_CM_13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
]
CF_CM_13_conclusions = []
CF_CM_13_example = [
    CF_CM_13_premises,
    CF_CM_13_conclusions,
    example_settings,
]

# CF_CM_14: SOBEL SEQUENCE WITH POSSIBILITY (N = 3)
# N = 3
CF_CM_14_premises = [
    '\\Diamond A',
    '(A \\boxright X)',
    '\\Diamond (A \\wedge B)',
    '\\neg ((A \\wedge B) \\boxright X)', # N = 4: 155.4 seconds on the MIT servers; .1587 seconds in old version; and now .0122 seconds
    '\\Diamond ((A \\wedge B) \\wedge C)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\Diamond (((A \\wedge B) \\wedge C) \\wedge D)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '\\Diamond ((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)', # ? seconds
    '\\Diamond (((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)', # ? seconds
    '\\Diamond ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # ? seconds
]
CF_CM_14_conclusions = []
CF_CM_14_example = [
    CF_CM_14_premises,
    CF_CM_14_conclusions,
    example_settings,
]

# CF_CM_15: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
CF_CM_15_premises = ['\\neg A']
CF_CM_15_conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
CF_CM_15_example = [
    CF_CM_15_premises,
    CF_CM_15_conclusions,
    example_settings,
]

# CF_CM_16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
CF_CM_16_premises = ['\\neg A','(A \\boxright (B \\vee C))']
CF_CM_16_conclusions = ['(A \\boxright B)','(A \\boxright C)']
CF_CM_16_example = [
    CF_CM_16_premises,
    CF_CM_16_conclusions,
    example_settings,
]

# CF_CM_17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# N = 4
CF_CM_17_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM_17_conclusions = ['((A \\vee B) \\boxright C)']
CF_CM_17_example = [
    CF_CM_17_premises,
    CF_CM_17_conclusions,
    example_settings,
]

# CF_CM_18: MUST FACTIVITY
# N = 3
CF_CM_18_premises = ['A','B']
CF_CM_18_conclusions = ['(A \\boxright B)']
CF_CM_18_example = [
    CF_CM_18_premises,
    CF_CM_18_conclusions,
    example_settings,
]

# CF_CM_19: COUNTERFACTUAL EXPORTATION
# N = 3
CF_CM_19_premises = ['((A \\wedge B) \\boxright C)']
CF_CM_19_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM_19_example = [
    CF_CM_19_premises,
    CF_CM_19_conclusions,
    example_settings,
]

# CF_CM_20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
CF_CM_20_premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
CF_CM_20_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM_20_example = [
    CF_CM_20_premises,
    CF_CM_20_conclusions,
    example_settings,
]

# CF_CM_21:
# N = 3
CF_CM_21_premises = ['\\neg A','\\neg (A \\boxright B)']
CF_CM_21_conclusions = ['(A \\boxright \\neg B)']
CF_CM_21_example = [
    CF_CM_21_premises,
    CF_CM_21_conclusions,
    example_settings,
]




############################
### LOGICAL CONSEQUENCES ###
############################

# CF_TH_1: COUNTERFACTUAL IDENTITY
# N = 3
CF_TH_1_premises = []
CF_TH_1_conclusions = ['(A \\boxright A)']
CF_TH_1_example = [
    CF_TH_1_premises,
    CF_TH_1_conclusions,
    example_settings,
]

# CF_TH_2: COUNTERFACTUAL MODUS PONENS
# N = 3
CF_TH_2_premises = ['A','(A \\boxright B)']
CF_TH_2_conclusions = ['B']
CF_TH_2_example = [
    CF_TH_2_premises,
    CF_TH_2_conclusions,
    example_settings,
]

# CF_TH_3: WEAKENED TRANSITIVITY
# N = 3
CF_TH_3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
CF_TH_3_conclusions = ['(A \\boxright C)']
CF_TH_3_example = [
    CF_TH_3_premises,
    CF_TH_3_conclusions,
    example_settings,
]

# CF_TH_4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
CF_TH_4_premises = ['((A \\vee B) \\boxright C)']
CF_TH_4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_TH_4_example = [
    CF_TH_4_premises,
    CF_TH_4_conclusions,
    example_settings,
]

# CF_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
CF_TH_5_premises = ['((A \\vee B) \\boxright C)']
CF_TH_5_conclusions = ['(A \\boxright C)']
CF_TH_5_example = [
    CF_TH_5_premises,
    CF_TH_5_conclusions,
    example_settings,
]

# CF_TH_6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
CF_TH_6_premises = ['((A \\vee B) \\boxright C)']
CF_TH_6_conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
CF_TH_6_example = [
    CF_TH_6_premises,
    CF_TH_6_conclusions,
    example_settings,
]

# CF_TH_7:
# N = 3
CF_TH_7_premises = [
    '(A \\boxright C)',
    '(B \\boxright C)',
    '((A \\wedge B) \\boxright C)',
]
CF_TH_7_conclusions = ['((A \\vee B) \\boxright C)']
CF_TH_7_example = [
    CF_TH_7_premises,
    CF_TH_7_conclusions,
    example_settings,
]


# CF_TH_8:
# N = 3
CF_TH_8_premises = ['(A \\boxright (B \\wedge C))']
CF_TH_8_conclusions = ['(A \\boxright B)']
CF_TH_8_example = [
    CF_TH_8_premises,
    CF_TH_8_conclusions,
    example_settings,
]

# CF_TH_9:
# N = 3
CF_TH_9_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_TH_9_conclusions = ['(A \\boxright (B \\wedge C))']
CF_TH_9_example = [
    CF_TH_9_premises,
    CF_TH_9_conclusions,
    example_settings,
]

# # CF_TH__T10: FACTIVITY MIGHT
CF_TH_10_premises = ['A','B']
CF_TH_10_conclusions = ['(A \\circleright B)']
CF_TH_10_example = [
    CF_TH_10_premises,
    CF_TH_10_conclusions,
    example_settings,
]

# # CF_TH__T11: DEFINITION OF NEC
# N = 4
CF_TH_11_premises = ['(\\neg A \\boxright \\bot)']
CF_TH_11_conclusions = ['(\\top \\boxright A)']
CF_TH_11_example = [
    CF_TH_11_premises,
    CF_TH_11_conclusions,
    example_settings,
]



##################################
### DEFINE EXAMPLES TO COMPUTE ###
##################################

example_range = {
    # Countermodels
    "CF_CM_1" : CF_CM_1_example,
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
    # Theorems
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
}

# Run comparison
# run_comparison(default_theory, imposition_theory, settings, CF_examples)
# run_comparison(default_theory, imposition_theory, settings, CM_examples)

# Store output in a file
# save_comparisons(default_theory, imposition_theory, settings, CF_examples)
# save_comparisons(default_theory, imposition_theory, settings, CM_examples)

