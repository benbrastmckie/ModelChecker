# B: when we develop the API, these will reference the users script
from exposed_things import (
    BotOperator,
    Proposition,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    Proposition,
    TopOperator,
    ConditionalOperator,
    BiconditionalOperator,

)

# NOTE: go in API
from hidden_things import(
    ModelSetup,
    ModelStructure,
    OperatorCollection,
)
from hidden_helpers import complexity_of

semantics = Semantics(3)
print("made semantics")

operators = OperatorCollection(
    AndOperator,
    NegOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    ConditionalOperator,
    BiconditionalOperator,
)
print("made operator collection (trivial)")

# premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]

# premises = ["A", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow B)"]
premises = ["(D \\leftrightarrow A)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["(D \\leftrightarrow A)"]
conclusions = ["\\neg B"]

model_setup = ModelSetup(
    semantics,
    operators,
    premises,
    conclusions,
    Proposition,
    max_time=1,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=False,
)
print("made model_setup")

# sl_dict = model_setup.find_sentence_letters(premises + conclusions)
# print("TEST PRINT SENT_LET_DIC:", sl_dict)

model_structure = ModelStructure(model_setup)
print("made model_structure")

# TEST PRINT
model_structure.print_all()  

# print("print all props:", model_structure.all_propositions)

# COMPLEXITY
# example = "((A \\rightarrow (B \\wedge C)) \\wedge (A \\rightarrow (B \\wedge C)))"
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
