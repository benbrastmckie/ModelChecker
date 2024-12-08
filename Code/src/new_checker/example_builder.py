import concurrent.futures

from model_builder import (
    ModelConstraints,
    ModelStructure,
)
from syntactic import Syntax

def make_model_for(
    settings,
    premises,
    conclusions,
    semantics_class,
    proposition_class,
    operators,
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
    settings,
    premises,
    conclusions,
    semantics_class,
    proposition_class,
    operators,
):
    while True:
        model_structure = make_model_for(
            settings,
            premises,
            conclusions,
            semantics_class,
            proposition_class,
            operators,
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

def compare_semantics(theory_list, settings):
    with concurrent.futures.ProcessPoolExecutor() as executor:
        future_to_theory = {
            executor.submit(find_max_N, settings, *theory): theory
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

    return [imp_prems, imp_cons]


def run_comparison(theory_A, theory_B, settings, examples):

    for name, example in examples.items():
        print(f"\nExample: {name} of {example}")
        premises, conclusions = example
        print(f"  Premises:")
        for prem in premises:
            print(f"    {prem}")
        print(f"  Conclusions:")
        for con in conclusions:
            print(f"    {con}")
        dictionary = {
            '\\boxright' : '\\imposition',
            '\\circleright' : '\\could',
        }
        ex_theory_A = example + theory_A
        alt_example = translate(premises, conclusions, dictionary)
        ex_theory_B = alt_example + theory_B
        theory_list = [ex_theory_A, ex_theory_B]
        compare_semantics(theory_list, settings)
