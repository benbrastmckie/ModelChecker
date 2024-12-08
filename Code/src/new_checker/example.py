from example_builder import (
    compare_semantics,
    make_model_for,
    find_max_N,
    translate,
)
 
from semantic import (
    Semantics,
    ImpositionSemantics,
    Proposition,
)

from defined_operators import (
    ConditionalOperator, BiconditionalOperator, # extensional defined
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    DefNecessityOperator, DefPossibilityOperator, DefPossibilityOperator2, # modal defined
    MightCounterfactualOperator, # counterfactual
    MightImpositionOperator,
    # CircNecessityOperator, CircPossibilityOperator, # circular (for testing)
    # CircNecessityOperator1, CircPossibilityOperator1,
    # CircNecessityOperator2, CircPossibilityOperator2, 
)

from primitive_operators import (
    AndOperator, NegationOperator, OrOperator, # extensional
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    NecessityOperator, # modal
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
    NecessityOperator, # modal
    DefNecessityOperator, DefPossibilityOperator, DefPossibilityOperator2, # modal defined
    CounterfactualOperator, MightCounterfactualOperator, # counterfactual
    ImpositionOperator, MightImpositionOperator, # Fine
    # CircNecessityOperator, CircPossibilityOperator, # circular (for testing)
    # CircNecessityOperator1, CircPossibilityOperator1,
    # CircNecessityOperator2, CircPossibilityOperator2, 
)


################
### DEFAULTS ###
################

settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'disjoint' : False,
    'print_impossible' : True,
    'optimize' : True,
    'max_time' : 1,
}


#####################
### EXAMPLE STOCK ###
#####################

# premises = ["\\neg (\\bot \\vee B)", "(\\top \\wedge D)"]
# premises = ["A", "((\\neg \\top \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["(A \\rightarrow B)", "A"]
# premises = ["(A \\rightarrow (B \\rightarrow C))", "D"]
# premises = ["(A \\leftrightarrow B)", "\\Diamond A"]
# premises = ["\\Diamond B"]
# premises = ["\\Box A", "(A \\leftrightarrow B)"]
# premises = ["\\Box \\Box A"]
# premises = ["\\necessary \\neg \\neg A", "\\neg \\neg \\neg \\necessary B", "B"]
# premises = ["(\\neg \\top \\boxright B)"]
# premises = ["(\\neg \\top \\boxright B)"]
# premises = ["A", "(A \\boxright (B \\wedge C))"]
# premises = ["A", "(A \\wedge B)"]
# premises = ["A"]
# premises = ["(D \\leftrightarrow A)"]
# premises = ["(\\neg D \\leftrightarrow \\bot)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow \\top)"]
# premises = ["A", "(A \\equiv B)"]
# premises = ["A", "(A \\leq B)"]
# premises = ["(\\neg A \\boxright B)", "((A \\wedge B) \\boxright C)"]
# premises = ["(A \\boxright B)", "(B \\boxright C)", "A"]
# premises = ["(A \\wedge B)", "((A \\wedge B) \\boxright C)"]
# premises = ["A", "\\neg A"]

# conclusions = ["\\neg E"]
# conclusions = ["B"]
# conclusions = ["B"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]
# conclusions = ["C"]





########################
##### OTHER ISSUES #####
########################

# # DOES NOT FIND MODEL
# # THIS WAS EXTRA HARD BEFORE ALSO
# N = 4
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']
# settings['continget'] = True




#############################
### WORKING COUNTERMODELS ###
#############################

# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
CF_CM1_premises = ['(A \\boxright C)']
CF_CM1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM1_example = [
    CF_CM1_premises,
    CF_CM1_conclusions,
]
# settings['continget'] = True

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
CF_CM2_premises = ['(A \\circleright C)']
CF_CM2_conclusions = ['((A \\wedge B) \\circleright C)']
CF_CM2_example = [
    CF_CM2_premises,
    CF_CM2_conclusions,
]
# settings['continget'] = True

# # CF_CM3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# N = 3
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
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
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
# settings['continget'] = True

# # CF_CM18: MUST FACTIVITY
# N = 3
CF_CM18_premises = ['A','B']
CF_CM18_conclusions = ['(A \\boxright B)']
CF_CM18_example = [
    CF_CM18_premises,
    CF_CM18_conclusions,
]
# settings['continget'] = True

# # CF_CM19: COUNTERFACTUAL EXPORTATION
# N = 3
CF_CM19_premises = ['((A \\wedge B) \\boxright C)']
CF_CM19_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM19_example = [
    CF_CM19_premises,
    CF_CM19_conclusions,
]
# settings['continget'] = True

# # CF_CM20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
CF_CM20_premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
CF_CM20_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM20_example = [
    CF_CM20_premises,
    CF_CM20_conclusions,
]
# settings['continget'] = True

# # CF_CM21:
# N = 3
CF_CM21_premises = ['\\neg A','\\neg (A \\boxright B)']
CF_CM21_conclusions = ['(A \\boxright \\neg B)']
CF_CM21_example = [
    CF_CM21_premises,
    CF_CM21_conclusions
]
# settings['continget'] = True





####################################
### WORKING LOGICAL CONSEQUENCES ###
####################################

# # CF1: COUNTERFACTUAL IDENTITY
# N = 3
# premises = []
# conclusions = ['(A \\boxright A)']
# settings['continget'] = False

# # CF2: COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['A','(A \\boxright B)']
# conclusions = ['B']
# settings['continget'] = False

# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# settings['continget'] = False

# # CF4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# settings['continget'] = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# settings['continget'] = False

# # CF6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
# settings['continget'] = False

# # CF7:
# N = 3
# premises = [
#     '(A \\boxright C)',
#     '(B \\boxright C)',
#     '((A \\wedge B) \\boxright C)',
# ]
# conclusions = ['((A \\vee B) \\boxright C)']
# settings['continget'] = False

# # CF8:
# N = 3
# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']
# settings['continget'] = False

# # CF9:
# N = 3
# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']
# settings['continget'] = False

# # # CF_T10: FACTIVITY MIGHT
# N = 4
# premises = ['A','B']
# conclusions = ['(A \\circleright B)']
# settings['continget'] = False

# # # CF_T11: DEFINITION OF NEC
# N = 4
# premises = ['(\\neg A \\boxright \\bot)']
# conclusions = ['(\\top \\boxright A)']
# settings['continget'] = False




#########################################
### GENERATE Z3 CONSTRAINTS AND PRINT ###
#########################################

# model_structure = make_model_for(
#     premises,
#     conclusions,
#     ImpositionSemantics,
#     Proposition,
#     operators,
#     settings,
# )
# model_structure.print_all()

# max_N = find_max_N(
#     premises,
#     conclusions,
#     Semantics,
#     Proposition,
#     operators,
#     settings,
# )

CM_examples = [
    CF_CM1_example,
    CF_CM2_example,
    CF_CM3_example,
    CF_CM4_example,
    CF_CM5_example,
    CF_CM6_example,
    CF_CM7_example,
    CF_CM8_example,
    CF_CM9_example,
    CF_CM10_example,
    CF_CM11_example,
    CF_CM12_example,
    CF_CM13_example,
    CF_CM14_example,
    CF_CM15_example,
    CF_CM16_example,
    CF_CM17_example,
    CF_CM18_example,
    CF_CM19_example,
    CF_CM20_example,
    CF_CM21_example,
]

for example in CM_examples:
    print(f"Example: {str(example)}")
    premises, conclusions = example
    print(f"  Premises:")
    for prem in premises:
        print(f"    {prem}")
    print(f"  Conclusions:")
    for con in conclusions:
        print(f"    {con}")

    dictionary = {
        '\\boxright' : '\\imposition',
        '\\circleright' : '\\could',
    }

    alt_premises, alt_conclusions = translate(premises, conclusions, dictionary)

    default_theory = [
        premises,
        conclusions,
        Semantics,
        Proposition,
        operators,
        settings,
    ]
    imposition_theory = [
        alt_premises,
        alt_conclusions,
        ImpositionSemantics,
        Proposition,
        operators,
        settings,
    ]
    theory_list = [
        default_theory,
        imposition_theory,
    ]
    compare_semantics(theory_list)


