import cProfile
import pstats

from hidden_helpers import bitvec_to_substates

from semantic import (
    Semantics,
    Proposition,
)

from defined_operators import (
    ConditionalOperator, BiconditionalOperator, # extensional defined
    DefEssenceOperator, DefGroundOperator, # constitutive defined
    DefNecessityOperator, DefPossibilityOperator, DefPossibilityOperator2, # modal defined
    MightCounterfactualOperator, # counterfactual
    MightImpositionOperator,
    CircNecessityOperator, CircPossibilityOperator, # circular (for testing)
    CircNecessityOperator1, CircPossibilityOperator1,
    CircNecessityOperator2, CircPossibilityOperator2, 
)

from primitive_operators import (
    AndOperator, NegationOperator, OrOperator, # extensional
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    NecessityOperator, # modal
    CounterfactualOperator, # counterfactual
    ImpositionOperator, # counterfactual
)

from model_builder import(
    ModelConstraints,
    ModelStructure,
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
    'max_time' : 1,
}


#####################
### EXAMPLE STOCK ###
#####################

# premises = ["\\neg (\\bot \\vee B)", "(\\top \\wedge D)"]
# premises = ["A", "((\\neg \\top \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["(A \\rightarrow B)", "A"]
# premises = ["(A \\rightarrow (B \\rightarrow C))", "D"]
# premises = ["(A \\leftrightarrow B)", "\\possible A"]
# premises = ["\\possible B"]
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

# CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
N = 5
premises = ['(A \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']
settings['continget'] = True

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
# premises = ['(A \\circleright C)']
# conclusions = ['((A \\wedge B) \\circleright C)']
# settings['continget'] = True

# # CF_CM3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# N = 3
# premises = ['(A \\boxright C)', '\\possible (A \\wedge B)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # CF_CM4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# N = 4
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # CF_CM5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# N = 4
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # CF_CM6: WEAKENED MONOTONICITY
# N = 3
# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# settings['contingent'] = False

# # IMP_CM6: WEAKENED MONOTONIC IMPOSITION
# N = 3
# premises = ['(A \\imposition B)','(A \\imposition C)']
# conclusions = ['((A \\wedge B) \\imposition C)']
# settings['contingent'] = False

# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # CF_CM8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
# N = 4
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # CF_CM9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # CF_CM10: TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # CF_CM11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# N = 3
# premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # CF_CM12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # CF_CM13: SOBEL SEQUENCE
# N = 3
# premises = [
#     '(A \\boxright X)',
#     '\\neg ((A \\wedge B) \\boxright X)',
#     '(((A \\wedge B) \\wedge C) \\boxright X)',
#     '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
#     '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
#     '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
#     '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
# ]
# conclusions = []

# # CF_CM14: SOBEL SEQUENCE WITH POSSIBILITY (N = 3)
# N = 3
# premises = [
#     '\\possible A',
#     '(A \\boxright X)',
#     '\\possible (A \\wedge B)',
#     '\\neg ((A \\wedge B) \\boxright X)', # N = 4: 155.4 seconds on the MIT servers; .1587 seconds in old version; and now .0122 seconds
#     '\\possible ((A \\wedge B) \\wedge C)',
#     '(((A \\wedge B) \\wedge C) \\boxright X)',
#     '\\possible (((A \\wedge B) \\wedge C) \\wedge D)',
#     '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
#     '\\possible ((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E)',
#     '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)', # ? seconds
#     '\\possible (((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F)',
#     '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)', # ? seconds
#     '\\possible ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G)',
#     '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # ? seconds
# ]
# conclusions = []

# # CF_CM15: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# # CF_CM16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']

# # CF_CM17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']
# settings['continget'] = True

# # CF_CM18: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']
# settings['continget'] = True

# # CF_CM19: COUNTERFACTUAL EXPORTATION
# N = 3
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']
# settings['continget'] = True

# # CF_CM20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
# premises = ['((A \\wedge B) \\boxright C)','\\possible (A \\wedge B)']
# conclusions = ['(A \\boxright (B \\boxright C))']
# settings['continget'] = True

# # CF_CM21
# N = 3
# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']
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




#########################################
### GENERATE Z3 CONSTRAINTS AND PRINT ###
#########################################

syntax = syntactic.Syntax(premises, conclusions, operators)

semantics = Semantics(N)

model_constraints = ModelConstraints(
    syntax,
    semantics,
    Proposition,
    settings,
)

model_structure = ModelStructure(model_constraints, settings['max_time'])

model_structure.print_all()

