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
premises = ["A", "(A \\boxright B)"]
# premises = ["A", "(A \\equiv B)"]
# premises = ["A", "(A \\leq B)"]
# premises = ["(A \\boxright B)", "(B \\boxright C)"]
# premises = ["(A \\boxright B)", "((A \\wedge B) \\boxright C)"]
# premises = ["(A \\boxright B)", "(B \\boxright C)", "A"]
# premises = ["(A \\wedge B)", "((A \\wedge B) \\boxright C)"]
# premises = ["A", "\\neg A"]
# conclusions = ["B"]

# conclusions = ["\\neg C"]
conclusions = ["B"]
# conclusions = ["\\neg B"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]
# conclusions = ["(A \\boxright C)"]
# conclusions = ["C"]



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

# for sent in syntax.all_sentences.values():
#     print("PRINT TYPE", f"prefix_type {sent.prefix_type} is type {type(sent.prefix_type)}")

semantics = Semantics(3)

model_constraints = ModelConstraints(
    syntax,
    semantics,
    Proposition,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=False,
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
