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



#####################
### EXAMPLE STOCK ###
#####################

# premises = ["\\neg (\\bot \\vee B)", "(C \\wedge D)"]
# premises = ["A", "((\\neg \\top \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow B)"]
premises = ["A", "(A \\boxright B)"]
conclusions = ["B"]
# premises = ["A", "(A \\wedge B)"]
# premises = ["(D \\leftrightarrow A)"]
# premises = ["(\\neg D \\leftrightarrow \\bot)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow \\top)"]
# premises = ["A", "(A \\boxright B)"]
# premises = ["A", "(A \\equiv B)"]
# premises = ["A", "(A \\leq B)"]

# conclusions = ["(\\neg B \\wedge \\neg D)"]
# premises = ["(A \\boxright B)", "(B \\boxright C)"]
# conclusions = ["(A \\boxright C)"]



#####################
### WORKING PAIRS ###
#####################

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


#####################
#### NOT WORKING ####
#####################

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

semantics = Semantics(3)

model_constraints = ModelConstraints(
    syntax,
    semantics,
    Proposition,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=True,
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

# print(model_constraints)

# print("print all props:", model_structure.all_propositions)

# complexity = complexity_of(model_setup.prefix(example))
# print(f"{example} has complexity {complexity}")

# a = Defined(model_structure.all_propositions['(A \\vee B)'].prefix_sentence,model_structure)
# print(str(a))
# b = Defined(model_structure.all_propositions['A'].prefix_sentence,model_structure)
# print(a == b)
# {a}

# TODO: missing just rec_print
# test_prop = model_structure.all_propositions['(A \\vee B)']
# test_prop.print_proposition(model_structure.main_world)
