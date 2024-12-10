from example_builder import (
    make_model_for,
    find_max_N,
    run_comparison,
    save_comparisons,
)
 
from semantic import (
    Semantics,
    ImpositionSemantics,
    Proposition,
)

from defined_operators import (
    ConditionalOperator, BiconditionalOperator, # extensional defined
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    MightCounterfactualOperator, # counterfactual
    MightImpositionOperator,
)

from primitive_operators import (
    AndOperator, NegationOperator, OrOperator, # extensional
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    NecessityOperator, PossibilityOperator, # modal
    CounterfactualOperator, # counterfactual
    ImpositionOperator, # counterfactual
)

import syntactic

######################
### SETUP LANGUAGE ###
######################

operators = syntactic.OperatorCollection(
    AndOperator, NegationOperator, OrOperator, # extensional
    ConditionalOperator, BiconditionalOperator, # extensional defined
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    NecessityOperator, PossibilityOperator, # modal
    CounterfactualOperator, MightCounterfactualOperator, # counterfactual
    ImpositionOperator, MightImpositionOperator, # Fine
)


################
### DEFAULTS ###
################

settings = {
    'N' : 3,
    'contingent' : True,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : True,
    'print_impossible' : True,
    'max_time' : 1,
}


############################
##### REMAINING ISSUES #####
############################

# # DOES NOT FIND MODEL
# # THIS WAS EXTRA HARD BEFORE ALSO
# N = 4
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']




#############################
### WORKING COUNTERMODELS ###
#############################

# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM1_premises = ['(A \\boxright C)']
CF_CM1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM1_example = [
    CF_CM1_premises,
    CF_CM1_conclusions,
]

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM2_premises = ['(A \\circleright C)']
CF_CM2_conclusions = ['((A \\wedge B) \\circleright C)']
CF_CM2_example = [
    CF_CM2_premises,
    CF_CM2_conclusions,
]

# # CF_CM3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
CF_CM3_premises = ['(A \\boxright C)', '\\Diamond (A \\wedge B)']
CF_CM3_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM3_example = [
    CF_CM3_premises,
    CF_CM3_conclusions,
]

# # CF_CM4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# N = 4
CF_CM4_premises = ['\\neg A','(A \\boxright C)']
CF_CM4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM4_example = [
    CF_CM4_premises,
    CF_CM4_conclusions,
]

# # CF_CM5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# N = 4
CF_CM5_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM5_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM5_example = [
    CF_CM5_premises,
    CF_CM5_conclusions,
]

# # CF_CM6: WEAKENED MONOTONICITY
# N = 3
CF_CM6_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_CM6_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM6_example = [
    CF_CM6_premises,
    CF_CM6_conclusions,
]
# settings['contingent'] = False

# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION
# N = 3
CF_CM7_premises = ['(A \\boxright B)']
CF_CM7_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM7_example = [
    CF_CM7_premises,
    CF_CM7_conclusions,
]

# # CF_CM8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# N = 4
CF_CM8_premises = ['\\neg B','(A \\boxright B)']
CF_CM8_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM8_example = [
    CF_CM8_premises,
    CF_CM8_conclusions,
]

# # CF_CM9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
CF_CM9_premises = ['\\neg A','\\neg B','(A \\boxright B)']
CF_CM9_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM9_example = [
    CF_CM9_premises,
    CF_CM9_conclusions,
]

# # CF_CM10: TRANSITIVITY
# N = 3
CF_CM10_premises = ['(A \\boxright B)','(B \\boxright C)']
CF_CM10_conclusions = ['(A \\boxright C)']
CF_CM10_example = [
    CF_CM10_premises,
    CF_CM10_conclusions,
]

# # CF_CM11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# N = 3
CF_CM11_premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
CF_CM11_conclusions = ['(A \\boxright C)']
CF_CM11_example = [
    CF_CM11_premises,
    CF_CM11_conclusions,
]

# # CF_CM12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
CF_CM12_premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
CF_CM12_conclusions = ['(A \\boxright C)']
CF_CM12_example = [
    CF_CM12_premises,
    CF_CM12_conclusions,
]

# # CF_CM13: SOBEL SEQUENCE
# N = 3
CF_CM13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
]
CF_CM13_conclusions = []
CF_CM13_example = [
    CF_CM13_premises,
    CF_CM13_conclusions,
]

# # CF_CM14: SOBEL SEQUENCE WITH POSSIBILITY (N = 3)
# N = 3
CF_CM14_premises = [
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
CF_CM14_conclusions = []
CF_CM14_example = [
    CF_CM14_premises,
    CF_CM14_conclusions,
]

# # CF_CM15: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
CF_CM15_premises = ['\\neg A']
CF_CM15_conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
CF_CM15_example = [
    CF_CM15_premises,
    CF_CM15_conclusions,
]

# # CF_CM16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
CF_CM16_premises = ['\\neg A','(A \\boxright (B \\vee C))']
CF_CM16_conclusions = ['(A \\boxright B)','(A \\boxright C)']
CF_CM16_example = [
    CF_CM16_premises,
    CF_CM16_conclusions,
]

# # CF_CM17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# N = 4
CF_CM17_premises = ['(A \\boxright C)','(B \\boxright C)']
CF_CM17_conclusions = ['((A \\vee B) \\boxright C)']
CF_CM17_example = [
    CF_CM17_premises,
    CF_CM17_conclusions,
]

# # CF_CM18: MUST FACTIVITY
# N = 3
CF_CM18_premises = ['A','B']
CF_CM18_conclusions = ['(A \\boxright B)']
CF_CM18_example = [
    CF_CM18_premises,
    CF_CM18_conclusions,
]

# # CF_CM19: COUNTERFACTUAL EXPORTATION
# N = 3
CF_CM19_premises = ['((A \\wedge B) \\boxright C)']
CF_CM19_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM19_example = [
    CF_CM19_premises,
    CF_CM19_conclusions,
]

# # CF_CM20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
CF_CM20_premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
CF_CM20_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM20_example = [
    CF_CM20_premises,
    CF_CM20_conclusions,
]

# # CF_CM21:
# N = 3
CF_CM21_premises = ['\\neg A','\\neg (A \\boxright B)']
CF_CM21_conclusions = ['(A \\boxright \\neg B)']
CF_CM21_example = [
    CF_CM21_premises,
    CF_CM21_conclusions
]




####################################
### WORKING LOGICAL CONSEQUENCES ###
####################################

# # CF_T1: COUNTERFACTUAL IDENTITY
# N = 3
CF_T1_premises = []
CF_T1_conclusions = ['(A \\boxright A)']
CF_T1_example = [
    CF_T1_premises,
    CF_T1_conclusions
]

# # CF_T2: COUNTERFACTUAL MODUS PONENS
# N = 3
CF_T2_premises = ['A','(A \\boxright B)']
CF_T2_conclusions = ['B']
CF_T2_example = [
    CF_T2_premises,
    CF_T2_conclusions
]

# # CF_T3: WEAKENED TRANSITIVITY
# N = 3
CF_T3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
CF_T3_conclusions = ['(A \\boxright C)']
CF_T3_example = [
    CF_T3_premises,
    CF_T3_conclusions
]

# # CF_T4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
CF_T4_premises = ['((A \\vee B) \\boxright C)']
CF_T4_conclusions = ['((A \\wedge B) \\boxright C)']
CF_T4_example = [
    CF_T4_premises,
    CF_T4_conclusions
]

# # CF_T5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
CF_T5_premises = ['((A \\vee B) \\boxright C)']
CF_T5_conclusions = ['(A \\boxright C)']
CF_T5_example = [
    CF_T5_premises,
    CF_T5_conclusions
]

# # CF_T6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
CF_T6_premises = ['((A \\vee B) \\boxright C)']
CF_T6_conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
CF_T6_example = [
    CF_T6_premises,
    CF_T6_conclusions
]

# # CF_T7:
# N = 3
CF_T7_premises = [
    '(A \\boxright C)',
    '(B \\boxright C)',
    '((A \\wedge B) \\boxright C)',
]
CF_T7_conclusions = ['((A \\vee B) \\boxright C)']
CF_T7_example = [
    CF_T7_premises,
    CF_T7_conclusions
]


# # CF_T8:
# N = 3
CF_T8_premises = ['(A \\boxright (B \\wedge C))']
CF_T8_conclusions = ['(A \\boxright B)']
CF_T8_example = [
    CF_T8_premises,
    CF_T8_conclusions
]

# # CF_T9:
# N = 3
CF_T9_premises = ['(A \\boxright B)','(A \\boxright C)']
CF_T9_conclusions = ['(A \\boxright (B \\wedge C))']
CF_T9_example = [
    CF_T9_premises,
    CF_T9_conclusions
]

# # # CF_T_T10: FACTIVITY MIGHT
# N = 4
CF_T10_premises = ['A','B']
CF_T10_conclusions = ['(A \\circleright B)']
CF_T10_example = [
    CF_T10_premises,
    CF_T10_conclusions
]

# # # CF_T_T11: DEFINITION OF NEC
# N = 4
CF_T11_premises = ['(\\neg A \\boxright \\bot)']
CF_T11_conclusions = ['(\\top \\boxright A)']
CF_T11_example = [
    CF_T11_premises,
    CF_T11_conclusions,
]




#########################################
### GENERATE Z3 CONSTRAINTS AND PRINT ###
#########################################

### NOTE: run below for individual tests

premises, conclusions = CF_CM2_example
# premises, conclusions = CF_T10_example
model_structure = make_model_for(
    settings,
    premises,
    conclusions,
    Semantics,
    Proposition,
    operators,
)
model_structure.print_all()

# premises, conclusions = CF_T10_example
# max_N = find_max_N(
#     settings,
#     premises,
#     conclusions,
#     Semantics,
#     Proposition,
#     operators,
# )

CF_examples = {
    "CF_T1" : CF_T1_example,
    "CF_T2" : CF_T2_example,
    "CF_T3" : CF_T3_example,
    "CF_T4" : CF_T4_example,
    "CF_T5" : CF_T5_example,
    "CF_T6" : CF_T6_example,
    "CF_T7" : CF_T7_example,
    "CF_T8" : CF_T8_example,
    "CF_T9" : CF_T9_example,
    "CF_T10" : CF_T10_example,
    "CF_T11" : CF_T11_example,
}

CM_examples = {
    "CF_CM1" : CF_CM1_example,
    "CF_CM2" : CF_CM2_example,
    "CF_CM3" : CF_CM3_example,
    "CF_CM4" : CF_CM4_example,
    "CF_CM5" : CF_CM5_example,
    "CF_CM6" : CF_CM6_example,
    "CF_CM7" : CF_CM7_example,
    "CF_CM8" : CF_CM8_example,
    "CF_CM9" : CF_CM9_example,
    "CF_CM10" : CF_CM10_example,
    "CF_CM11" : CF_CM11_example,
    "CF_CM12" : CF_CM12_example,
    "CF_CM13" : CF_CM13_example,
    "CF_CM14" : CF_CM14_example,
    "CF_CM15" : CF_CM15_example,
    "CF_CM16" : CF_CM16_example,
    "CF_CM17" : CF_CM17_example,
    "CF_CM18" : CF_CM18_example,
    "CF_CM19" : CF_CM19_example,
    "CF_CM20" : CF_CM20_example,
    "CF_CM21" : CF_CM21_example,
}

default_theory = [
    Semantics,
    Proposition,
    operators,
]

imposition_theory = [
    ImpositionSemantics,
    Proposition,
    operators,
]

# # Run comparison
# run_comparison(default_theory, imposition_theory, settings, CF_examples)
# run_comparison(default_theory, imposition_theory, settings, CM_examples)

# # Store output in a file
# save_comparisons(default_theory, imposition_theory, settings, CF_examples)
# save_comparisons(default_theory, imposition_theory, settings, CM_examples)
