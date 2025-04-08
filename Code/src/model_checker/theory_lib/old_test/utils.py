"""run 'pytest' from the '.../Code/src/model_checker/' directory"""

from src.model_checker.model import (
    ModelConstraints,
)

from src.model_checker.theory_lib.default.semantic import (
    ModelStructure,
)

from src.model_checker.syntactic import (
    Syntax,
)

default_max_time = 2

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
        settings,
        syntax,
        semantics,
        proposition,
    )
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
