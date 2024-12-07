"""run 'pytest' from the '.../Code/src/new_checker/' directory"""

# from new_checker.defined_operators import (
#     NegationOperator,
#     AndOperator,
#     OrOperator,
#     TopOperator,
#     BotOperator,
#     IdentityOperator,
#     EssenceOperator,
#     GroundOperator,
#     CounterfactualOperator,
#     ImpositionOperator,
#     PossibilityOperator,
#     NecessityOperator,
#     MightCounterfactualOperator,
#     MightImpositionOperator,
#     DefEssenceOperator,
#     DefGroundOperator,
#     ConditionalOperator,
#     BiconditionalOperator,
#     DefNecessityOperator,
#     DefPossibilityOperator,
# )

from new_checker.model_builder import (
    ModelConstraints,
    ModelStructure,
)

from new_checker.syntactic import (
    Syntax,
)

###############
### TIMEOUT ###
###############

default_max_time = 2

######################
### LANGUAGE SETUP ###
######################

# operators = OperatorCollection(
#     NegationOperator, # extensional
#     AndOperator,
#     OrOperator,
#     ConditionalOperator, # extensional defined 
#     BiconditionalOperator,
#     TopOperator, # extremal
#     BotOperator,
#     IdentityOperator, # constitutive
#     GroundOperator,
#     EssenceOperator,
#     DefGroundOperator, # constitutive defined
#     DefEssenceOperator,
#     CounterfactualOperator, # counterfactual
#     MightImpositionOperator,
#     ImpositionOperator,
#     MightCounterfactualOperator, # counterfactual defined
#     NecessityOperator, # modal
#     PossibilityOperator,
#     DefNecessityOperator,
#     DefPossibilityOperator,  # modal defined
#     ExclusionOperator, # unilateral primitive
#     UniOrOperator,
#     UniAndOperator,
# )


################
##### MAIN #####
################

def find_model_structure(
    premises,
    conclusions,
    semantics_class,
    proposition,
    operators,
    settings,
):
    syntax = Syntax(premises, conclusions, operators)
    semantics = semantics_class(settings['N'])
    model_constraints = ModelConstraints(
        syntax,
        semantics,
        proposition,
        settings,
    )
    # TODO: add print_impossible to ModelStructure
    return ModelStructure(model_constraints, settings['max_time'])


def failure_message(premises, conclusions, run_time, max_time, desired_found):
    status = "found" if desired_found else "did not find"
    return (
        f"Erroneously {status} a model:\n\n"
        f"Premises:\n{premises}\n\n"
        f"Conclusions:\n{conclusions}\n\n"
        f"Run time: {run_time} seconds\n"
        f"Max time: {max_time} seconds"
    )


def check_model_status(
    premises,
    conclusions,
    semantics,
    proposition,
    operators,
    settings,
):
    model_structure = find_model_structure(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )
    model_status = model_structure.z3_model_status
    run_time = model_structure.z3_model_runtime

    assert (
        not model_structure.timeout
    ), f"Model timed out. Increase max_time beyond {settings['max_time']} seconds."
    assert model_status == settings['desired_status'], failure_message(
        premises,
        conclusions,
        run_time,
        settings['max_time'],
        settings['desired_status'],
    )
