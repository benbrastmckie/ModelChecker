# B: when we develop the API, these will reference the users script
from exposed_things import (
    BotOperator,
    Defined,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    Defined,
    TopOperator,
)

# B: when we develop the API these should go into __init__.py
# M: yes—also Operator and Proposition
from hidden_things import(
    ModelSetup,
    ModelStructure,
    OperatorCollection,
)

semantics = Semantics(4)
print("made semantics")

operators = OperatorCollection(
    AndOperator,
    NegOperator,
    OrOperator,
    TopOperator,
    BotOperator,
)
print("made operator collection (trivial)")

premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
conclusions = ["(\\neg B \\wedge \\neg D)"]

model_setup = ModelSetup(
    semantics,
    operators,
    premises,
    conclusions,
    Defined,
    max_time=1,
    contingent=False,
    non_null=True,
    disjoint=False,
)
print("made model_setup")

model_structure = ModelStructure(model_setup)
print("made model_structure")

# TEST PRINT
print("print all props:", model_structure.all_propositions)
model_structure.print_all()  

a = Defined(model_structure.all_propositions['A'].prefix_sentence,model_structure)
b = Defined(model_structure.all_propositions['A'].prefix_sentence,model_structure)
print(a == b)
{a}
# TODO: add printing propositions recursively
