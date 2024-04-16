from model_structure import *

################################
########### WORKING ############
################################


### INVALID ###

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']
# # # NOTE: does not work with exhaustivity
# # # NOTE: only the following conclusion works with prop constraints applied to sentence letters
# # conclusions = ['(A \\boxright B)','(A \\boxright C)']

# # NOTE: only works with prop constraints applied to sentence letters
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']



### VALID ###

# # NOTE: only works with prop constraints applied to sentence letters
premises = ['A','(A \\rightarrow B)']
conclusions = ['B']

# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']

# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

premises = ['(A \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']

mod = ModelStructure(premises, conclusions)
mod.solve()

# this is what used to be print_model, can easily make this an attribute if wanted
if mod.model_status:
    # print(f"\nModel time: {time}")
    print(f"\nThere is an {N}-model of:\n")
    for sent in mod.input_sentences:
        print(sent)
    mod.print_states()
    mod.print_evaluation()
    mod.print_props()
else:
    print(f"\nThere are no {N}-models of:\n")
    for sent in mod.input_sentences:
        print(sent)
    print(mod.model)
    print()