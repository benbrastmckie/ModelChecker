# B: when we develop the API, these will reference the users script
from exposed_things import (
    BotOperator,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    Proposition,
    TopOperator,
    ConditionalOperator,
    BiconditionalOperator,
    CounterfactualOperator,

)

# NOTE: go in API
from hidden_things import(
    ModelConstraints,
    ModelStructure,
)

import syntactic
# B: this seems fine but curious to DISCUSS this

### SETUP LANGUAGE ###

operators = syntactic.OperatorCollection(
    AndOperator,
    NegOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    ConditionalOperator,
    BiconditionalOperator,
    CounterfactualOperator,
)

### PREMISES AND CONCLUSION ###

# premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]
# premises = ["A", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
premises = ["A", "(A \\rightarrow B)"]
# premises = ["A", "(A \\boxright B)"]
# premises = ["A", "(A \\wedge B)"]
# premises = ["(D \\leftrightarrow \\bot)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["(D \\leftrightarrow A)"]
conclusions = ["\\neg B"]

### GENERATE Z3 CONSTRAINTS ###

sytax = syntactic.Syntax(premises, conclusions, operators)
semantics = Semantics(3)
model_constraints = ModelConstraints(
    sytax,
    semantics,
    Proposition,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=False,
)

### SOLVE, STORE, AND PRINT Z3 MODEL ###

model_structure = ModelStructure(model_constraints, max_time=1)
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
