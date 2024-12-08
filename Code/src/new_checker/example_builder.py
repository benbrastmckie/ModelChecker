import concurrent.futures

from model_builder import (
    ModelConstraints,
    ModelStructure,
)
from syntactic import Syntax

def make_model_for(
    premises,
    conclusions,
    semantics_class,
    proposition_class,
    operators,
    settings,
):
    syntax = Syntax(premises, conclusions, operators)
    semantics = semantics_class(settings['N'])
    model_constraints = ModelConstraints(
        syntax,
        semantics,
        proposition_class,
        settings,
    )
    return ModelStructure(
        model_constraints,
        settings['max_time']
    )

def find_max_N(
    premises,
    conclusions,
    semantics_class,
    proposition_class,
    operators,
    settings,
):
    while True:
        model_structure = make_model_for(
            premises,
            conclusions,
            semantics_class,
            proposition_class,
            operators,
            settings,
        )
        run_time = model_structure.z3_model_runtime
        if run_time < settings['max_time']:
            print(
                f"({model_structure.semantics.name}): " +
                f"RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {settings['N']}."
            )
            settings['N'] += 1
        else:
            return settings['N'] - 1

def compare_semantics(theory_list):
    with concurrent.futures.ProcessPoolExecutor() as executor:
        future_to_theory = {
            executor.submit(find_max_N, *theory): theory
            for theory in theory_list
        }
        for future in concurrent.futures.as_completed(future_to_theory):
            theory = future_to_theory[future]
            try:
                future.result()
            except Exception as e:
                print(f"An error occurred for theory {theory}: {e}")

def translate(premises, conclusions, dictionary):
    """Use dictionary to replace logical operators."""
    def replace_operators(logical_list, dictionary):
        for old, new in dictionary.items():
            logical_list = [sentence.replace(old, new) for sentence in logical_list]
        return logical_list

    imp_prems = replace_operators(premises, dictionary)
    imp_cons = replace_operators(conclusions, dictionary)

    return imp_prems, imp_cons
