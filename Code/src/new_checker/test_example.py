from exposed_things import (Semantics,
                            AndOperator,
                            NegOperator,
                            OrOperator,
                            Proposition,
                            )
from hidden_things import ModelSetup, ModelStructure, OperatorCollection


premises = ['\\neg (A \\vee B)', '(C \\wedge D)']
conclusions = ['(\\neg B \\wedge \\neg D)']
operators = OperatorCollection(AndOperator, NegOperator, OrOperator)
print('made operator collection (trivial)')
semantics = Semantics(4)
print('made semantics')
model_setup = ModelSetup(premises, conclusions, semantics, operators, Proposition)
print('made model_setup')
solve_output = model_setup.solve()
print('solved the constraints')
model_structure = ModelStructure(*solve_output)
print('made model_structure')
print('back at editable file')
model_structure.print_all() # missing printing propositions recursively


# for proposition in model_structure.all_propositions:
#     print(proposition)
#     print(proposition.truth_or_falsity_at_world(model_structure.main_world))
#     # print(proposition.verifiers, proposition.falsifiers)
#     print('\n')