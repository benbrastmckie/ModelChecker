from exposed_things import (
    BotOperator,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    Defined,
    TopOperator,
)
from hidden_things import ModelSetup, ModelStructure, OperatorCollection

premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
conclusions = ["(\\neg B \\wedge \\neg D)"]
operators = OperatorCollection(AndOperator, NegOperator, OrOperator, TopOperator, BotOperator)
print("made operator collection (trivial)")
semantics = Semantics(4)
print("made semantics")

# NOTE: should semantics, operators, propositions be grouped into an object?
# NOTE: could group settings into an object to pass in here if need be?
model_setup = ModelSetup(premises, conclusions, semantics, operators, Defined)
print("made model_setup")
model_structure = ModelStructure(model_setup)
print("made model_structure")
print("back at editable file")
model_structure.print_all()  
print(model_structure.all_propositions)
# TODO: add printing propositions recursively
