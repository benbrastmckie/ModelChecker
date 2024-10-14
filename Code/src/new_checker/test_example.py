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

)

# NOTE: go in API
from hidden_things import(
    ModelConstraints,
    ModelStructure,
    OperatorCollection,
    Syntax,
)

semantics = Semantics(3)
# print("made semantics")

operators = OperatorCollection(
    AndOperator,
    NegOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    ConditionalOperator,
    BiconditionalOperator,
)
# print("made operator collection (trivial)")

# premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
# conclusions = ["(\\neg B \\wedge \\neg D)"]

# premises = ["A", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["A", "(A \\rightarrow B)"]
premises = ["A", "(A \\leftrightarrow B)"]
# premises = ["(D \\leftrightarrow A)", "((A \\rightarrow (B \\wedge C)) \\wedge D)"]
# premises = ["(D \\leftrightarrow A)"]
conclusions = ["\\neg B"]

sytax = Syntax(
    premises,
    conclusions,
    operators,
    semantics,
)
# print("made model_setup")

model_constraints = ModelConstraints(
    sytax,
    Proposition,
    contingent=False,
    non_null=True,
    disjoint=False,
    print_impossible=False,
)
# print("made model_setup")

# sl_dict = model_setup.find_sentence_letters(premises + conclusions)
# print("TEST PRINT SENT_LET_DIC:", sl_dict)

model_structure = ModelStructure(model_constraints, max_time=1)
# print("made model_structure")

# TEST PRINT
model_structure.print_all()  

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
