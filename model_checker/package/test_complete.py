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


################################
########## SETTINGS ############
################################

# length of bitvectors
# N = 3

# print all Z3 constraints if a model is found
# print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
# print_unsat_core_bool = True


################################
########### WORKING ############
################################


### INVALID ###

# premises = []
# conclusions = []

# premises = ['A']
# conclusions = []

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']

# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# premises = ['A \\boxright C', '\\neg (A \\boxright \\neg B)']
# conclusions = ['\\neg ((A \\wedge B) \\boxright C)']


### VALID ###

# premises = ['A','(A \\rightarrow B)']
# conclusions = ['B']

# NOTE: very slow with non_triv_verify turned on in semantics
# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# # NOTE: very slow with non_triv_verify turned on in semantics
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: slow with non_triv_verify turned on in semantics
# premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# # NOTE: slow with non_triv_verify turned on in semantics
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']

# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']


################################
######### NOT WORKING ##########
################################


### HIGH PRIORITY: NEGATION PROBLEM ###

# # NOTE: ssh finds unsat_core but should have countermodels
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # NOTE: ssh finds unsat_core but should have countermodels
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']


### MEDIUM PRIORITY ###

# # NOTE: it is finding a model by making A and B incompatible
# # premises = ['\\neg ((A \\wedge B) \\boxright D)','((A \\wedge B) \\boxright C)']
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this does not find models for N = 3
# # very slow for N = 5 (ran for minutes on the remote server)
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: doesn't work b/c should countermodel
# # recursive printing would be helpful.
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# this is what used to be print_model, can easily make this an attribute if wanted


################################
########### TEMPLATE ###########
################################

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



################################
############ SOLVER ############
################################

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

    # Create an argument parser to get the script name
    parser = argparse.ArgumentParser(description="Import and use a variable from another script")
    # parser.add_argument("script_name", type=str, help="The name of the script to import (without .py)")
    parser.add_argument(
        "file_path",
        type=str,
        help="Path to the Python file to read."
    )

    # Parse the command-line argument to get the script name
    args = parser.parse_args()
    # script_name = args.script_name
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


    # # Import the specified script/module dynamically
    # try:
    #     imported_script = importlib.import_module(script_name)
    # except ModuleNotFoundError:
    #     print(f"Error: Module '{script_name}' not found.")
    #     sys.exit(1)

    # check for models given the values in the imported script
    # Assuming we want to access a variable named 'my_var'
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


################################
########### EXECUTE ############
################################

if __name__ == "__main__":
    # main()
    optional_generate_test()
