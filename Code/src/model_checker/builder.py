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

def try_single_N(theory_name, semantic_theory, example_case):
    """Try a single N value and return (success, runtime)"""
    premises, conclusions, settings = example_case
    semantics_class = semantic_theory["semantics"]
    proposition_class = semantic_theory["proposition"]
    operators = semantic_theory["operators"]
    model_structure = make_model_for(
        premises,
        conclusions,
        settings,
        semantics_class,
        proposition_class,
        operators,
    )
    run_time = model_structure.z3_model_runtime
    success = run_time < settings['max_time']
    if success:
        print(
            f"{model_structure.semantics.name} ({theory_name}):\n"
            f"  RUN TIME = {run_time}, " +
            f"MAX TIME = {settings['max_time']}, " +
            f"N = {settings['N']}."
        )
    else:
        print(
            f"{model_structure.semantics.name} ({theory_name}): "
            f"TIMED OUT\n" +
            f"  RUN TIME = {run_time}, " +
            f"MAX TIME = {settings['max_time']}, " +
            f"N = {example_case[2]['N']}."
        )
    return success, run_time

def compare_semantics(example_theory_tuples):
    results = []
    active_cases = {}  # Track active cases and their current N values
    
    with concurrent.futures.ProcessPoolExecutor() as executor:
        # Initialize first run for each case
        futures = {}
        all_times = []
        for case in example_theory_tuples:
            theory_name, semantic_theory, (premises, conclusions, settings) = case
            example_case = [premises, conclusions, settings.copy()]
            active_cases[theory_name] = settings['N']  # Store initial N
            all_times.append(settings['max_time'])
            new_case = (theory_name, semantic_theory, example_case)
            futures[executor.submit(try_single_N, *new_case)] = new_case
        max_time = max(all_times)
            
        while futures:
            done, _ = concurrent.futures.wait(
                futures,
                # timeout=max_time,
                return_when=concurrent.futures.FIRST_COMPLETED
            )
            for future in done:
                case = futures.pop(future)
                theory_name, semantic_theory, example_case = case
                max_time = example_case[2]['max_time']
                
                try:
                    success, runtime = future.result()
                    if success and runtime < max_time:
                        # Increment N and submit new case
                        example_case[2]['N'] = active_cases[theory_name] + 1
                        active_cases[theory_name] = example_case[2]['N']
                        futures[executor.submit(try_single_N, *case)] = case
                    else:
                        # Found max N for this case
                        results.append((theory_name, active_cases[theory_name] - 1))
                except Exception as e:
                    print(
                        f"\nERROR: {case[1]['semantics'].__name__} " +
                        f"({case[0]}) for N = {example_case[2]['N']}."
                        f"  {str(e)}"
                    )
                    
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
        example_tuple = (theory_name, semantic_theory, translated_case)
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
        print(f"\n{'='*40}")

# TODO: combine with run_comparison once moved into print class
# def save_comparisons(default_theory, imposition_theory, settings, examples):
#     # Get the absolute path of the current script
#     script_path = os.path.realpath(__file__)
#     script_dir = os.path.dirname(script_path)
#     # Define subdirectory path relative to the script's directory
#     new_dir = os.path.join(script_dir, "comparisons")
#     # Create the "Examples" directory if it doesn't exist
#     os.makedirs(new_dir, exist_ok=True)
#     # Prompt the user for a filename
#     filename = input("Please enter the output filename (without path): ")
#     filepath = os.path.join(new_dir, filename)
#
#     # Open the file for writing and redirect stdout
#     with open(filepath, 'w') as f:
#         old_stdout = sys.stdout
#         sys.stdout = f
#         try:
#             run_comparison(default_theory, imposition_theory, settings, examples)
#         finally:
#             # Restore original stdout
#             sys.stdout = old_stdout
#
#     print(f"All output has been written to {filename}.")

