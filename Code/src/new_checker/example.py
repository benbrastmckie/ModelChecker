import example_builder

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

N = 3
contingent_bool = False
disjoint_bool = False


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
# contingent_bool = True
# disjoint_bool = False




#############################
### WORKING COUNTERMODELS ###
#############################

# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 5
# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # IMP_CM1: IMPOSITION ANTECEDENT STRENGTHENING
# N = 4
# premises = ['(A \\imposition C)']
# conclusions = ['((A \\wedge B) \\imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
# premises = ['(A \\circleright C)']
# conclusions = ['((A \\wedge B) \\circleright C)']
# contingent_bool = True
# disjoint_bool = False

# # IMP_CM2: MIGHT IMPOSITION ANTECEDENT STRENGTHENING
# N = 4
# premises = ['(A \\could C)']
# conclusions = ['((A \\wedge B) \\could C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# N = 3
# premises = ['(A \\boxright C)', '\\possible (A \\wedge B)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# N = 4
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# CF_CM5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
N = 4
premises = ['(A \\boxright C)','(B \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']
contingent_bool = True
disjoint_bool = False

# # CF_CM6: WEAKENED MONOTONICITY
# N = 3
# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # IMP_CM6: WEAKENED MONOTONIC IMPOSITION
# N = 3
# premises = ['(A \\imposition B)','(A \\imposition C)']
# conclusions = ['((A \\wedge B) \\imposition C)']
# contingent_bool = False
# disjoint_bool = False

# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']
# # contingent_bool = True
# # disjoint_bool = False

# # CF_CM8: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
# N = 4
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM9: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM10: TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM11: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# N = 3
# premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM12: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

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
# contingent_bool = True
# disjoint_bool = False

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
# contingent_bool = True
# disjoint_bool = False

# # CF_CM15: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM16: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM17: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM18: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM19: COUNTERFACTUAL EXPORTATION
# N = 3
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM20: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
# premises = ['((A \\wedge B) \\boxright C)','\\possible (A \\wedge B)']
# conclusions = ['(A \\boxright (B \\boxright C))']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM21
# N = 3
# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']
# contingent_bool = True
# disjoint_bool = False





####################################
### WORKING LOGICAL CONSEQUENCES ###
####################################

# # CF1: COUNTERFACTUAL IDENTITY
# N = 3
# premises = []
# conclusions = ['(A \\boxright A)']
# contingent_bool = False
# disjoint_bool = False

# # CF2: COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['A','(A \\boxright B)']
# conclusions = ['B']
# contingent_bool = False
# disjoint_bool = False

# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
# contingent_bool = False
# disjoint_bool = False

# # CF7:
# N = 3
# premises = [
#     '(A \\boxright C)',
#     '(B \\boxright C)',
#     '((A \\wedge B) \\boxright C)',
# ]
# conclusions = ['((A \\vee B) \\boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF8:
# N = 3
# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']
# contingent_bool = False
# disjoint_bool = False

# # CF9:
# N = 3
# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']
# contingent_bool = False
# disjoint_bool = False


# # # CF_T10: FACTIVITY MIGHT
# N = 4
# premises = ['A','B']
# conclusions = ['(A \\circleright B)']
# contingent_bool = False
# disjoint_bool = False

##################################
#### CONSTITUTIVE NOT WORKING ####
##################################

# None?

##############################
#### CONSTITUTIVE WORKING ####
##############################

# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(\\neg A \\leq \\neg B)"]

# premises = ["(\\neg A \\leq \\neg B)"]
# conclusions = ["(A \\sqsubseteq B)"]

# premises = ["(A \\leq B)"]
# conclusions = ["(\\neg A \\sqsubseteq \\neg B)"]

# premises = ["(\\neg A \\sqsubseteq \\neg B)"]
# conclusions = ["(A \\leq B)"]

# premises = ["(\\neg A \\ground \\neg B)"]
# conclusions = ["(A \\essence B)"]

# premises = ["(A \\ground B)"]
# conclusions = ["(\\neg A \\essence \\neg B)"]

# premises = ["(\\neg A \\ground \\neg B)"]
# conclusions = ["(A \\sqsubseteq B)"]

# premises = ["(A \\ground B)"]
# conclusions = ["(\\neg A \\sqsubseteq \\neg B)"]

# premises = ["(A \\essence B)"]
# conclusions = ["(\\neg A \\leq \\neg B)"]

# premises = ["(\\neg A \\essence \\neg B)"]
# conclusions = ["(A \\leq B)"]

# premises = ["A", "(B \\sqsubseteq A)"]
# conclusions = ["\\neg B"]

# premises = ["(A \\essence B)"]
# conclusions = ["(A \\sqsubseteq B)"]

# premises = ["(A \\ground B)"]
# conclusions = ["(A \\leq B)"]

# premises = ["(A \\essence B)"]
# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(\\neg A \\ground \\neg B)"]

# premises = ["(\\neg A \\essence \\neg B)"]
# premises = ["(\\neg A \\sqsubseteq \\neg B)"]
# premises = ["(A \\leq B)"]
# conclusions = ["(A \\ground B)"]

# premises = ["(A \\leq B)"]
# conclusions = ["(\\neg A \\essence \\neg B)"]

# premises = ["(\\neg A \\leq \\neg B)"]
# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(A \\essence B)"]

# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(A \\essence B)"]

# # ESSENCE MODUS TOLLENS
# N = 3
# premises = ["A", "(B \\essence A)"]
# conclusions = ["\\neg B"]
# contingent_bool = False
# disjoint_bool = False




###############################
### GENERATE Z3 CONSTRAINTS ###
###############################

optimize = True
max_time = 1

syntax = syntactic.Syntax(premises, conclusions, operators)

model_structure = example_builder.make_model_for(
    N,
    syntax,
    Semantics,
    Proposition,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=True,
    optimize,
    max_time,
)
model_structure.print_all()


# ########################################
# ### SOLVE, STORE, AND PRINT Z3 MODEL ###
# ########################################
#
# semantics = Semantics(N)
#
# model_constraints = ModelConstraints(
#     syntax,
#     semantics,
#     Proposition,
#     contingent=contingent_bool,
#     non_null=True,
#     disjoint=disjoint_bool,
#     print_impossible=True,
# )
#
# model_structure = ModelStructure(model_constraints, max_time=1)
#
# model_structure.print_all()

