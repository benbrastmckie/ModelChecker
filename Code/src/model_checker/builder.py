import sys
import os
import concurrent.futures

from .model import (
    ModelConstraints,
    ModelStructure,
)
from .syntactic import Syntax

def make_model_for(
    premises,
    conclusions,
    settings,
    semantics_class,
    proposition_class,
    operators,
):
    syntax = Syntax(premises, conclusions, operators)
    semantics = semantics_class(settings['N'])
    model_constraints = ModelConstraints(
        settings,
        syntax,
        semantics,
        proposition_class,
    )
    return ModelStructure(
        model_constraints,
        settings['max_time']
    )

# case:
    # ex_name
    # th_name

    # premises,
    # conclusions,
    # settings,

    # semantics_class,
    # proposition_class,
    # operators,

def find_max_N(theory_name, example_case, semantic_theory):
    premises, conclusions, settings = example_case
    semantics_class = semantic_theory["semantics"]
    proposition_class = semantic_theory["proposition"]
    operators = semantic_theory["operators"]
    while True:
        model_structure = make_model_for(
            premises,
            conclusions,
            settings,
            semantics_class,
            proposition_class,
            operators,
        )
        run_time = model_structure.z3_model_runtime
        if run_time < settings['max_time']:
            print(
                f"{model_structure.semantics.name} ({theory_name}):\n"
                f"  RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {settings['N']}."
            )
            settings['N'] += 1
        else:
            return settings['N'] - 1

def compare_semantics(example_theory_tuples):
    results = []
    with concurrent.futures.ProcessPoolExecutor() as executor:
        future_to_theory = {
            executor.submit(find_max_N, *case): case
            for case in example_theory_tuples
        }
        for future in concurrent.futures.as_completed(future_to_theory):
            case = future_to_theory[future]
            try:
                result = future.result()
                results.append((case[0], result))
            except Exception as e:
                print(f"\nERROR in {case[2]['semantics'].__name__} ({case[0]}):")
                print(f"  {str(e)}" + " Continuing with remaining comparisons...\n")
                results.append((case[0], None))
    return results

def translate(example_case, dictionary):
    """Use dictionary to replace logical operators."""
    premises, conclusions, settings = example_case
    def replace_operators(logical_list, dictionary):
        for old, new in dictionary.items():
            logical_list = [sentence.replace(old, new) for sentence in logical_list]
        return logical_list
    new_premises = replace_operators(premises, dictionary)
    new_conclusion = replace_operators(conclusions, dictionary)
    return [new_premises, new_conclusion, settings]

def translate_example(example_case, semantic_theories):
    example_theory_tuples = []
    for theory_name, semantic_theory in semantic_theories.items():
        translated_case = example_case
        dictionary = semantic_theory.get("dictionary", None)
        if dictionary:
            translated_case = translate(example_case.copy(), dictionary)
        example_tuple = (theory_name, translated_case, semantic_theory)
        example_theory_tuples.append(example_tuple)
    return example_theory_tuples

# TODO: integrate into print object
def run_comparison(example_range, semantic_theories):
    print()
    for example_name, example_case in example_range.items():
        premises, conclusions, settings = example_case
        print(f"{'='*40}\n")
        print(f"EXAMPLE = {example_name}")
        print(f"  Premises:")
        for prem in premises:
            print(f"    {prem}")
        print(f"  Conclusions:")
        for con in conclusions:
            print(f"    {con}")
        print()
        example_theory_tuples = translate_example(example_case, semantic_theories)
        compare_semantics(example_theory_tuples)
        print(f"{'='*40}")

def save_comparisons(default_theory, imposition_theory, settings, examples):
    # Get the absolute path of the current script
    script_path = os.path.realpath(__file__)
    script_dir = os.path.dirname(script_path)
    # Define subdirectory path relative to the script's directory
    new_dir = os.path.join(script_dir, "comparisons")
    # Create the "Examples" directory if it doesn't exist
    os.makedirs(new_dir, exist_ok=True)
    # Prompt the user for a filename
    filename = input("Please enter the output filename (without path): ")
    filepath = os.path.join(new_dir, filename)

    # Open the file for writing and redirect stdout
    with open(filepath, 'w') as f:
        old_stdout = sys.stdout
        sys.stdout = f
        try:
            run_comparison(default_theory, imposition_theory, settings, examples)
        finally:
            # Restore original stdout
            sys.stdout = old_stdout

    print(f"All output has been written to {filename}.")

