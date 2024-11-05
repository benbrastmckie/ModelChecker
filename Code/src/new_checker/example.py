from hidden_helpers import bitvec_to_substates

# B: when we develop the API, these will reference the users script
from exposed_things import (
    Semantics,
    Proposition,
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    EssenceOperator,
    GroundOperator,
    CounterfactualOperator,
    DefEssenceOperator,
    DefGroundOperator,
    ConditionalOperator,
    BiconditionalOperator,

)

# NOTE: go in API
from hidden_things import(
    ModelConstraints,
    ModelStructure,
)

import syntactic

### SETUP LANGUAGE ###

operators = syntactic.OperatorCollection(
    AndOperator,
    NegationOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    GroundOperator,
    DefEssenceOperator,
    DefGroundOperator,
    EssenceOperator,
    ConditionalOperator,
    BiconditionalOperator,
    CounterfactualOperator,
)



################
### DEFAULTS ###
################

N = 3
contingent_bool=False,
non_null_bool=True,
disjoint_bool=False,
print_impossible=True,



#####################
### EXAMPLE STOCK ###
#####################

# premises = ["\\neg (\\bot \\vee B)", "(C \\wedge D)"]
# premises = ["A", "((\\neg \\top \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow B)"]
# premises = ["A", "(A \\boxright (B \\wedge C))"]
# premises = ["A", "(A \\wedge B)"]
# premises = ["A"]
# premises = ["(D \\leftrightarrow A)"]
# premises = ["(\\neg D \\leftrightarrow \\bot)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow \\top)"]
# premises = ["A", "(A \\equiv B)"]
# premises = ["A", "(A \\leq B)"]
# premises = ["(A \\boxright B)", "((A \\wedge B) \\boxright C)"]
# premises = ["(A \\boxright B)", "(B \\boxright C)", "A"]
# premises = ["(A \\wedge B)", "((A \\wedge B) \\boxright C)"]
# premises = ["A", "\\neg A"]

# conclusions = ["\\neg C"]
# conclusions = ["B"]
# conclusions = ["\\neg B"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]
# conclusions = ["C"]

##### Transitivity (model desired)
premises = ["(A \\boxright B)", "(B \\boxright C)"]
conclusions = ["(A \\boxright C)"]

##### Weakened Transitivity (no model desired)
# premises = ["(A \\boxright B)", "((A \\wedge B) \\boxright C)"]
# conclusions = ["(A \\boxright C)"]

##### Simplification of Disjunctive Antecedent (no model desired)
premises = ["((A \\vee B) \\boxright C)"]
conclusions = ["(A \\boxright C)"]

##### Strengthening the Antecedent (model desired)
# premises = ["(A \\boxright C)"]
# conclusions = ["((A \\wedge B) \\boxright C)"]

#####################################
##### NOT WORKING COUNTERMODELS #####
#####################################

# NOTE: printing not working
# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # CF_CM4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 242 seconds on the MIT server; now .1928 seconds locally
# N = 4
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
# N = 4
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright neg A)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # # CF_CM8: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']
# # contingent_bool = True
# # disjoint_bool = False

# NOTE: printing not working
# # CF_CM10: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# N = 4
# premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # CF_CM12: SOBEL SEQUENCE (N = 3)
# N = 3
# premises = [
#     '(A \\boxright X)', # 0.03 seconds locally
#     '\\neg ((A \\wedge B) \\boxright X)', # 1.4 seconds locally
#     '(((A \\wedge B) \\wedge C) \\boxright X)', # 4.9 seconds locally
#     # 'neg ((((A wedge B) wedge C) wedge D) boxright X)', # FALSE PREMISE MODELS BEGIN HERE
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # 20.5 seconds locally
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # 64 seconds on the MIT servers
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
# ]
# conclusions = []
# contingent_bool = True
# disjoint_bool = False

# NOTE: not finding a countermodel
# # CF_CM14: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 4
# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: not finding a countermodel
# # CF_CM15: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: OrOperator argument number error
# # CF_CM16: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # CF_CM17: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']
# contingent_bool = True
# disjoint_bool = False

# NOTE: printing not working
# # CF_CM18: COUNTERFACTUAL EXPORTATION
# N = 3
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']
# contingent_bool = True
# disjoint_bool = False

# NOTE: not finding a countermodel
# # CF_CM20
# N = 3
# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']
# contingent_bool = True
# disjoint_bool = False


#############################
### WORKING COUNTERMODELS ###
#############################

# # CF_CM5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# N = 4
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM6: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']
# # contingent_bool = True
# # disjoint_bool = False

# # CF_CM9: TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM11: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = True
# disjoint_bool = False




########################################
### NOT WORKING LOGICAL CONSEQUENCES ###
########################################

# NOTE: erroneously finding a countermodel
# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# contingent_bool = False
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


##################################
#### CONSTITUTIVE NOT WORKING ####
##################################


# # TRUE CONCLUSION MODEL
# premises = ["(A \\essence B)"]
# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(\\neg A \\ground \\neg B)"]

# # TRUE CONCLUSION MODEL
# premises = ["(\\neg A \\essence \\neg B)"]
# premises = ["(\\neg A \\sqsubseteq \\neg B)"]
# premises = ["(A \\leq B)"]
# conclusions = ["(A \\ground B)"]

# # TRUE CONCLUSION MODEL
# premises = ["(A \\leq B)"]
# conclusions = ["(\\neg A \\essence \\neg B)"]

# # TRUE CONCLUSION MODEL
# premises = ["(\\neg A \\leq \\neg B)"]
# premises = ["(A \\sqsubseteq B)"]
# conclusions = ["(A \\essence B)"]

# # FALSE PREMISE MODEL
# premises = ["A", "(B \\essence A)"]
# conclusions = ["\\neg B"]

# # TRUE CONCLUSION MODEL
# premises = ["(A \\sqsubseteq B)"]
# premises = ["(A \\essence B)"]




###############################
### GENERATE Z3 CONSTRAINTS ###
###############################

syntax = syntactic.Syntax(
    premises, # list of strings
    conclusions, # list of strings
    operators, # is an OperatorCollection instance
)

# for sent in syntax.all_sentences.values():
#     print("PRINT TYPE", f"prefix_type {sent.prefix_type} is type {type(sent.prefix_type)}")

semantics = Semantics(N)

model_constraints = ModelConstraints(
    syntax,
    semantics,
    Proposition,
    contingent_bool,
    non_null_bool, # LINTER: argument of type tupple[literal[true]] cannot be assigned to bool in function "__init__"
    disjoint_bool,
    print_impossible, # LINTER: argument of type tupple[literal[true]] cannot be assigned to bool in function "__init__"
)

########################################
### SOLVE, STORE, AND PRINT Z3 MODEL ###
########################################

model_structure = ModelStructure(
    model_constraints,
    max_time=1
)

# print("TEST ALL PROPS", model_structure.all_propositions)
model_structure.print_all()

if not model_structure.z3_model:
    model_constraints_obj = model_structure.model_constraints
    print(model_constraints.sentence_letters)
    # print(model_constraints.model_constraints)
    # print(model_constraints.premise_constraints)
    print(model_structure.unsat_core)


def bv2s(bitvec):
    # return bitvec_to_substates(bitvec, 3)
    def bv2s_helper(N):
        return bitvec_to_substates(bitvec, N)
    return bv2s_helper(3)

# # NOTE: I'm getting an error: 'NoneType' object has no attribute 'evaluate'
# # there is a similar linter error in ModelStructure.
# eval = model_structure.z3_model.evaluate
#
# main_world = model_structure.main_world
# all_worlds = {bit for bit in model_structure.all_bits if eval(semantics.is_world(bit))}
# print(f"all worlds: {set(bv2s(w) for w in all_worlds)}")
# A_V = model_structure.all_sentences['A'].proposition.verifiers
# print(f"A's verifiers: {set(bv2s(v) for v in A_V)}")
# for ver in A_V:
#     for world in all_worlds:
#         print(f"is {bv2s(world)} an {bv2s(ver)}-alternative to the main world {bv2s(main_world)}?")
#         result = eval(semantics.is_alternative(world, ver, main_world))
#         print(result)
#         # print(bool(result))
#         print(type(result))
#         print()

# semantics.is_alternative(6,1,)
# print() 

# print(model_constraints)

# print("print all props:", model_structure.all_propositions)

# complexity = complexity_of(model_setup.prefix(example))
# print(f"{example} has complexity {complexity}")

# a = Defined(model_structure.all_propositions['(A \\vee B)'].prefix_object,model_structure)
# print(str(a))
# b = Defined(model_structure.all_propositions['A'].prefix_object,model_structure)
# print(a == b)
# {a}

# TODO: missing just rec_print
# test_prop = model_structure.all_propositions['(A \\vee B)']
# test_prop.print_proposition(model_structure.main_world)
