"""From the project directory, run: python -m src.model_checker.template.examples"""
from .semantic import (
    Semantics,
    Proposition,
)

from .operators import (
    operators,
)

from .. import syntactic

from .. import model

########################
### DEFAULT SETTINGS ###
########################

settings = {
    'N' : 3,
    'contingent' : True,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : False,
    'print_impossible' : True,
    'max_time' : 1,
}



#####################
### COUNTERMODELS ###
#####################

# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM1_premises = ['(A \\boxright C)']
CF_CM1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM1_example = [
    CF_CM1_premises,
    CF_CM1_conclusions,
]

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM2_premises = ['(A \\circleright C)']
CF_CM2_conclusions = ['((A \\wedge B) \\circleright C)']
CF_CM2_example = [
    CF_CM2_premises,
    CF_CM2_conclusions,
]

# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION
CF_CM7_premises = ['(A \\boxright B)']
CF_CM7_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM7_example = [
    CF_CM7_premises,
    CF_CM7_conclusions,
]

# # CF_CM10: TRANSITIVITY
CF_CM10_premises = ['(A \\boxright B)','(B \\boxright C)']
CF_CM10_conclusions = ['(A \\boxright C)']
CF_CM10_example = [
    CF_CM10_premises,
    CF_CM10_conclusions,
]

# # CF_CM13: SOBEL SEQUENCE
CF_CM13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
]
CF_CM13_conclusions = []
CF_CM13_example = [
    CF_CM13_premises,
    CF_CM13_conclusions,
]

# # CF_CM19: COUNTERFACTUAL EXPORTATION
CF_CM19_premises = ['((A \\wedge B) \\boxright C)']
CF_CM19_conclusions = ['(A \\boxright (B \\boxright C))']
CF_CM19_example = [
    CF_CM19_premises,
    CF_CM19_conclusions,
]


############################
### LOGICAL CONSEQUENCES ###
############################

# # CF_T2: COUNTERFACTUAL MODUS PONENS
CF_T2_premises = ['A','(A \\boxright B)']
CF_T2_conclusions = ['B']
CF_T2_example = [
    CF_T2_premises,
    CF_T2_conclusions
]

# # CF_T3: WEAKENED TRANSITIVITY
CF_T3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
CF_T3_conclusions = ['(A \\boxright C)']
CF_T3_example = [
    CF_T3_premises,
    CF_T3_conclusions
]


# # CF_T5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
CF_T5_premises = ['((A \\vee B) \\boxright C)']
CF_T5_conclusions = ['(A \\boxright C)']
CF_T5_example = [
    CF_T5_premises,
    CF_T5_conclusions
]

# # CF_T_T11: DEFINITION OF NEC
CF_T11_premises = ['(\\neg A \\boxright \\bot)']
CF_T11_conclusions = ['(\\top \\boxright A)']
CF_T11_example = [
    CF_T11_premises,
    CF_T11_conclusions,
]

#########################################
### GENERATE Z3 CONSTRAINTS AND PRINT ###
#########################################

premises, conclusions = CF_CM1_example

syntax = syntactic.Syntax(premises, conclusions, operators)

semantics = Semantics(settings['N'])

model_constraints = model.ModelConstraints(
    settings,
    syntax,
    semantics,
    Proposition,
)

model_structure = model.ModelStructure(model_constraints)

model_structure.print_all()
