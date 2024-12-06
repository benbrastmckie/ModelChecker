import sys
import os

from __init__ import __version__

from model_builder import (
    ModelConstraints,
    ModelStructure,
)

def ask_time(runtime, max_time):
    """prompt the user to increase the max_time"""
    output = input(f"Enter a value for max_time > {max_time} or leave blank to exit.\n\nmax_time = ")
    if output.strip() == "":
        return None
    try:
        new_max_time = float(output)
    except ValueError:
        print("Invalid input. Please enter a valid number.")
        return ask_time(runtime, max_time)
    if not new_max_time > max_time:
        print("Invalid input. Please enter a valid number.")
        return ask_time(runtime, max_time)
    return new_max_time

def handle_timeout(module, model_setup):
    """Handles timeout scenarios by asking the user for a new time limit."""
    previous_N = model_setup.N - 1
    print(f"There are no {previous_N}-models.")
    print(f"No {model_setup.N}-models were found within {model_setup.model_runtime} seconds.")
    new_max_time = ask_time(model_setup.model_runtime, model_setup.max_time)
    if new_max_time is None:
        print("Process terminated.")
        print(f"Consider increasing max_time to be > {model_setup.max_time} seconds.\n")
        model_setup.N = previous_N
        model_setup.no_model_print(module.print_constraints)
        os._exit(1)
    module.update_max_time(new_max_time)

def adjust(module, offset):
    """Redefines module and model_setup after adjusting N by the offset."""
    module.N += offset
    model_setup = make_model_for(
        module.N,
        module.premises,
        module.conclusions,
        module.max_time,
        module.contingent,
        module.disjoint,
    )
    return module, model_setup

def optimize_N(module, model_setup, past_module, past_model_setup, sat=False):
    """Finds the min value of N for which there is a model up to a timeout limit."""
    if model_setup.model_status: # finds a model
        new_sat = True
        new_module, new_model_setup = adjust(module, -1)
        min_module, min_model_setup = optimize_N(
            new_module,
            new_model_setup,
            module,
            model_setup,
            new_sat
        )
        return min_module, min_model_setup
    if sat: # does not find a model but has before (hence sat = True)
        return past_module, past_model_setup
    if model_setup.model_runtime < model_setup.max_time: # hasn't found a model yet
        new_module, new_model_setup = adjust(module, 1)
        max_module, max_model_setup = optimize_N(
            new_module,
            new_model_setup,
            module,
            model_setup,
            sat
        )
        return max_module, max_model_setup
    handle_timeout(module, model_setup)
    return optimize_model_setup(module)

def create_model_structure(
    N,
    syntax,
    semantics_class,
    proposition_class,
    contingent,
    non_null,
    disjoint,
    print_impossible,
    max_time,
):
    """Creates a model setup based on module attributes."""
    semantics = semantics_class(N)
    model_constraints = ModelConstraints(
        syntax,
        semantics,
        proposition_class,
        contingent,
        non_null,
        disjoint,
        print_impossible,
    )
    return ModelStructure(model_constraints, max_time)

def optimize_model_setup(module):
    """Runs make_model_for on the values provided by the module and user, optimizing if required."""
    max_time = module.max_time
    model_setup = create_model_structure(module, syntax)
    run_time = model_setup.model_runtime
    if run_time > max_time:
        handle_timeout(module, model_setup)
        module, model_setup = optimize_model_setup(module)
    if module.optimize:
        module, model_setup = optimize_N(module, model_setup, module, model_setup)
    return module, model_setup

def make_model_for(
    N,
    syntax,
    semantics_class,
    proposition_class,
    contingent,
    non_null,
    disjoint,
    print_impossible,
    optimize,
    max_time,
):
    if N == 0:
        print("No models for N > 0 were found.")
    model_structure = create_model_structure(
        N,
        syntax,
        semantics_class,
        proposition_class,
        contingent,
        non_null,
        disjoint,
        print_impossible,
        max_time,
    )
    run_time = model_structure.z3_model_runtime
    # if run_time is None:
    #     N -= 1
    #     return build_model(
    #         N,
    #         syntax,
    #         semantics_class,
    #         proposition_class,
    #         contingent=False,
    #         non_null=True,
    #         disjoint=False,
    #         print_impossible=True,
    #         optimize=False,
    #         max_time=1,
    #     )
    if optimize and run_time is not None and run_time < max_time:
        N += 1
        return build_model(
            N,
            syntax,
            semantics_class,
            proposition_class,
            contingent=False,
            non_null=True,
            disjoint=False,
            print_impossible=True,
            optimize=False,
            max_time=1,
        )
    return model_structure

