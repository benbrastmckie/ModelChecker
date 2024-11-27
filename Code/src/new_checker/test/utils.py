"""run 'pytest' from the '.../new_checker' directory"""

from new_checker.semantic import (
    Semantics,
    Proposition,
)

from new_checker.operators import (
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    EssenceOperator,
    GroundOperator,
    CounterfactualOperator,
    MightCounterfactualOperator,
    DefEssenceOperator,
    DefGroundOperator,
    ConditionalOperator,
    BiconditionalOperator,
    NecessityOperator,
    DefNecessityOperator,
    DefPossibilityOperator,
    DefPossibilityOperator2,
)

from new_checker.model_builder import (
    ModelConstraints,
    ModelStructure,
)

from new_checker.syntactic import (
    OperatorCollection,
    Syntax,
)


###############
### TIMEOUT ###
###############

default_max_time = 2

######################
### LANGUAGE SETUP ###
######################

operators = OperatorCollection(
    NegationOperator, # extensional
    AndOperator,
    OrOperator,
    ConditionalOperator, # extensional defined 
    BiconditionalOperator,
    TopOperator, # extremal
    BotOperator,
    IdentityOperator, # constitutive
    GroundOperator,
    EssenceOperator,
    DefGroundOperator, # constitutive defined
    DefEssenceOperator,
    CounterfactualOperator, # counterfactual
    MightCounterfactualOperator, # counterfactual defined
    NecessityOperator, # modal
    DefNecessityOperator,
    DefPossibilityOperator,  # modal defined
    DefPossibilityOperator2,
)


################
##### MAIN #####
################

def find_model_structure(
    premises,
    conclusions,
    N,
    contingent,
    non_null,
    disjoint,
    max_time,
):
    syntax = Syntax(premises, conclusions, operators)
    semantics = Semantics(N)
    model_constraints = ModelConstraints(
        syntax, semantics, Proposition, contingent, non_null, disjoint
    )
    # TODO: move print_impossible to ModelStructure
    return ModelStructure(model_constraints, max_time)


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
    N,
    contingent,
    non_null,
    disjoint,
    max_time,
    desired_status,
):
    model_structure = find_model_structure(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time
    )
    model_status = model_structure.z3_model_status
    run_time = model_structure.z3_model_runtime

    assert (
        not model_structure.timeout
    ), f"Model timed out. Increase max_time beyond {max_time} seconds."
    assert model_status == desired_status, failure_message(
        premises,
        conclusions,
        run_time,
        max_time,
        desired_status,
    )
