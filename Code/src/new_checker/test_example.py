from exposed_things import (Semantics,
                            AndOperator,
                            NegOperator,
                            OrOperator)
from hidden_things import ModelSetup, ModelStructure


premises = ['\\neg (A \\vee B)', '(C \\wedge D)']
conclusions = ['(\\neg B \\wedge \\neg D)']
operators = [AndOperator, NegOperator, OrOperator]
semantics = Semantics(4, operators)
model_setup = ModelSetup(premises, conclusions, semantics, 60, False, False, False, operators)
model_structure = ModelStructure(*model_setup.solve())
print(model_structure.z3_model)