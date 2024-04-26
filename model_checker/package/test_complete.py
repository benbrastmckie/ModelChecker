'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
'''

import argparse
import importlib.util
# import importlib
import sys
from string import Template
from model_structure import make_model_for

script_template = Template("""
'''
Model Checker: ${name}
'''

################################
########## SETTINGS ############
################################

# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True


################################
########### ARGUMENT ###########
################################

### INVALID ###

premises = ['neg A','(A boxright (B vee C))']
conclusions = ['(A boxright B)','(A boxright C)']

### VALID ###

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

""")

# def main():
#     """finds and prints model from user inputs given above"""
#     mod = make_model_for(N)(premises, conclusions)
#     mod.print_all(print_cons_bool, print_unsat_core_bool)


def main_inputs(length, prems, cons, print_cons, print_unsat):
    """finds and prints model from user inputs given above"""
    mod = make_model_for(length)(prems, cons)
    mod.print_all(print_cons, print_unsat)


def optional_generate_test():
    """generate a test file when script is run without input"""
    # Check if a script name was provided
    if len(sys.argv) < 2:
        result = input("Would you like to generate a new test file? (y/n): ")
        if result in ['Yes', 'yes', 'y']:
            test_name = input("Enter the name of your test using snake_case: ")
            template_data = {
                'name': test_name
            }
            script_content = script_template.substitute(template_data)
            output_file_path = f'{test_name}.py'
            with open(output_file_path, 'w', encoding="utf-8") as f:
                f.write(script_content)
            return
        print("You can run a test.py file that already exists with the command:\n")
        print("python3 model-checker test.py")
        return
    # Create an argument parser to get the file path
    parser = argparse.ArgumentParser(description="Import variables from another file")
    parser.add_argument(
        "file_path",
        type=str,
        help="Path to the Python file to read."
    )

    # Parse the command-line argument to get the module path
    args = parser.parse_args()
    file_path = args.file_path
    module_name = "dynamic_module"
    spec = importlib.util.spec_from_file_location(module_name, file_path)
    if spec is None:
        print(f"Error: Unable to find '{file_path}'.")
        exit(1)
    module = importlib.util.module_from_spec(spec)

    # Load the module
    try:
        spec.loader.exec_module(module)
    except Exception as e:
        print(f"Error: Failed to load the module from '{file_path}'. Reason: {e}")
        exit(1)

    # check for models given the values in the imported module
    if not hasattr(module, "N"):
        print("The value of 'N' is absent")
        return
    if not hasattr(module, "premises"):
        print("The premises are absent")
        return
    if not hasattr(module, "conclusions"):
        print("The conclusions are absent")
        return
    if not hasattr(module, "print_cons_bool"):
        print_cons_bool = False
        return
    if not hasattr(module, "print_unsat_core_bool"):
        print_unsat_core_bool = True
        return
    N = getattr(module, "N")
    premises = getattr(module, "premises")
    conclusions = getattr(module, "conclusions")
    print_cons_bool = getattr(module, "print_cons_bool")
    print_unsat_core_bool = getattr(module, "print_unsat_core_bool")
    main_inputs(N, premises, conclusions, print_cons_bool, print_unsat_core_bool)

if __name__ == "__main__":
    # main()
    optional_generate_test()
