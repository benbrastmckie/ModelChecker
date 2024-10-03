from exposed_things import (
    BotOperator,
    Semantics,
    AndOperator,
    NegOperator,
    OrOperator,
    Proposition,
    TopOperator,
)
from hidden_things import ModelSetup, ModelStructure, OperatorCollection


# B: this all looks great!
premises = ["\\neg (A \\vee B)", "(C \\wedge D)"]
conclusions = ["(\\neg B \\wedge \\neg D)"]
operators = OperatorCollection(AndOperator, NegOperator, OrOperator, TopOperator, BotOperator)
print("made operator collection (trivial)")
semantics = Semantics(4)
print("made semantics")

# B: right now no settings are passed in but that would add four more arguments.
# I know that is not too many, but it is enough where it becomes hard to keep track.
# to keep things easy for users, I think it would help to store all inputs in a class to pass in.
# the class could have a bunch of defaults which are changed if a user specifies settings.
# I think the Inputs class should include premises, conclusions, and all settings.
# right now we don't have too many settings, but it is likely these will continue to grow.
# M: yeah, I can see that making sense now that at a bare minimum five inputs are necessary
# for a ModelSetup instance. I'm wondering though if an Input class would just be kicking
# problem to the Input class? (Now, the Input instance would have x>5 input necessary)
# (Unless you had implementing the settings in there sequentially in mind)
# What if we kept like premises and conclusions in the ModelSetup and everything 
# else in the Input class? Because a specific Input object with just semantics, operators, and
# Propositions is very reusable—in fact, it would make testing more than one theorem
# very readable (so in this conception premises, conclusions, and an Input instance are passed
# to the ModelSetup constructor). This slightly reduces the nuber of arguments passed into
# the input class at least?
model_setup = ModelSetup(premises, conclusions, semantics, operators, Proposition)
print("made model_setup")

infix_ex = model_setup.prefix("(\\neg \\neg \\neg B \\wedge \\neg \\neg \\bot)")
print(f"Here is a prefix sentence: {infix_ex}")

# B: could we pass model_setup into ModelStructure, making solve() one of it's methods?
# seems like this would skip a step here and would carve at the conceptual joints
# but maybe there is something I'm still missing
solve_output = model_setup.solve()
if solve_output[2]:
    print("solved the constraints")
else:
    print("did not solve the constraints")

model_structure = ModelStructure(*solve_output)
print("made model_structure")
print("back at editable file")
model_structure.print_all()  # missing printing propositions recursively

# B: got it to print! this is coming together very nicely :)

# for proposition in model_structure.all_propositions:
#     print(proposition)
#     print(proposition.truth_or_falsity_at_world(model_structure.main_world))
#     # print(proposition.verifiers, proposition.falsifiers)
#     print('\n')
