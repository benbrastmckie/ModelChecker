from exposed_things import (
    BotOperator,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    NewProposition,
    TopOperator,
)
from hidden_things import ModelSetup, ModelStructure, OperatorCollection

# infix_ex = model_setup.prefix("(\\neg \\neg \\neg B \\wedge \\neg \\neg \\bot)")
# print(f"Here is a prefix sentence: {infix_ex}")

premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
conclusions = ["(\\neg B \\wedge \\neg D)"]
operators = OperatorCollection(AndOperator, NegOperator, OrOperator, TopOperator, BotOperator)
print("made operator collection (trivial)")
semantics = Semantics(4)
print("made semantics")

# NOTE: should semantics, operators, propositions be grouped into an object?
# NOTE: could group settings into an object to pass in here if need be?
model_setup = ModelSetup(premises, conclusions, semantics, operators, NewProposition)
print("made model_setup")
model_structure = ModelStructure(model_setup)
# model_structure = ModelStructure(*solve_output)
print("made model_structure")
print("back at editable file")
model_structure.print_all()  

# TODO: add printing propositions recursively
