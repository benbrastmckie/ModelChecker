'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
'''

import sys
import os
import subprocess
from string import Template
import argparse
import importlib.util
# import warnings
# import cProfile
# import pstats

# didn't work
# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# # Get the directory path of the current file
# current_dir = os.path.dirname(__file__)
# # Construct the full path to your project root
# project_root = os.path.abspath(os.path.join(current_dir, ".."))
# # project_root = project_root[:-4] # bandaid fix to remove "/src" from the root
# # Add the project root to the Python path
# sys.path.append(project_root)

### FOR TESTING ###
from __init__ import __version__
from model_structure import (
    StateSpace,
    make_model_for,
    )

# ### FOR PACKAGING ###
# from model_checker.__init__ import __version__
# from model_checker.model_structure import (
#     StateSpace,
#     make_model_for,
#     )

script_template = Template("""
'''
Model Checker: ${name}
'''
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

################################
########## SETTINGS ############
################################

# number of atomic states
N = 3

# time cutoff for increasing N
optimize = False

# time cutoff for increasing N
max_time = 1

# print all Z3 constraints if a model is found
print_cons_bool = False

# print all states including impossible states
print_impossible_states_bool = False

# present option to append output to file
save_bool = False


################################
############ SYNTAX ############
################################

### SENTENCES ###

# 'A', 'B', 'C',... can be used for sentence letters

# Alternatively, 'RedBall', 'MarySings',... or 'red_ball', 'mary_sings',... can be used for sentence letters.

# 'top' is a designated sentence for the trivial truth verified by everything and falsified by nothing.


### UNARY OPERATORS ###

# Negation: 'neg', e.g., 'neg A'.
# Necessity: 'Box', e.g., 'Box A'.
# Possibility: 'Diamond', e.g., 'Diamond RedBall'. 

# NOTE: parentheses must not be included for unary operators.


### BINARY OPERATORS ###

# Conjunction: 'wedge', e.g., '(A wedge B)'
# Disjunction: 'vee', e.g., '(A vee B)'
# Conditional: 'rightarrow', e.g., '(A rightarrow B)'
# Biconditional: 'leftrightarrow', e.g., '(A leftrightarrow B)'
# Counterfactual: 'boxright', e.g., '(A boxright B)'

# NOTE: parentheses must always be included for binary operators.


################################
########## ARGUMENTS ###########
################################

### INVALID ###

premises = ['neg A','(A boxright (B vee C))']
conclusions = ['(A boxright B)','(A boxright C)']

### VALID ###

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

""")

class LoadModule:
    """load module and store values as a class"""
    def __init__(self, module_name, module_path):
        self.module_name = module_name
        self.module_path = module_path
        self.default_values = {
            "N": 3,
            "premises": [],
            "conclusions": [],
            "max_time": 5,
            "optimize": False,
            "print_cons_bool": False,
        }
        self.module = self.load_module()
        self.initialize_attributes()
        self.validate_attributes()

    def load_module(self):
        """prepares a test file, raising a error if unsuccessful."""
        try:
            spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
            if spec is None or spec.loader is None:
                raise ImportError("Module spec could not be loaded.")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
        except Exception as e:
            raise ImportError(f"Failed to load the module '{self.module_name}': {e}") from e

    def initialize_attributes(self):
        """stores all user settings included in a test file."""
        self.parent_file = getattr(self.module, "file_name", True)
        self.parent_directory = getattr(self.module, "parent_directory", True)
        self.N = getattr(self.module, "N", self.default_values["N"])
        self.premises = getattr(self.module, "premises", self.default_values["premises"])
        self.conclusions = getattr(self.module, "conclusions", self.default_values["conclusions"])
        self.max_time = getattr(self.module, "max_time", self.default_values["max_time"])
        self.optimize = getattr(self.module, "optimize", self.default_values["optimize"])
        self.print_cons_bool = getattr(
            self.module,
            "print_cons_bool",
            self.default_values["print_cons_bool"]
        )
        self.print_impossible_states_bool = getattr(
            self.module,
            "print_impossible_states_bool",
            False
        )
        self.save_bool = getattr(self.module, "save_bool", True)
        # self.all_constraints = getattr(self.module, "all_constraints", [])

    def validate_attributes(self):
        for attr, default_value in self.default_values.items():
            if not hasattr(self.module, attr):
                print(f"The value of '{attr}' is absent and has been set to {default_value}.")
                # raise ImportError(f"The value of '{attr}' is absent")

def parse_file_and_flags():
    """returns the name and path for the current script"""
    # create an ArgumentParser object
    parser = argparse.ArgumentParser(
        prog='model-checker',
        usage='%(prog)s [options] input',
        description="""
        Running '%(prog)s' without options or an input will prompt the user
        to generate a new test file. To run a test on an existing file, include
        the path to that file as the input.""",
        epilog="""
        More information can be found at:
        https://github.com/benbrastmckie/ModelChecker/""",
    )
    parser.add_argument(
        "file_path",
        nargs='?',
        default=None,
        type=str,
        help="Specifies the path to a Python.",
    )
    parser.add_argument(
        '--constraints',
        '-c',
        action='store_true',
        help='Overrides to include all Z3 constraints.'
    )
    parser.add_argument(
        '--save',
        '-s',
        action='store_true',
        help='Overrides to prompt user to save output.'
    )
    parser.add_argument(
        '--impossible',
        '-i',
        action='store_true',
        help='Overrides to print impossible states.'
    )
    parser.add_argument(
        '--version',
        '-v',
        action='version',
        version=f"%(prog)s:  {__version__}",
        help='Prints the version number.'
    )
    parser.add_argument(
        '--optimize',
        '-o',
        action='store_true',
        help='finds the minimum value for N that is satisfiable before reaching max_time.'
    )
    parser.add_argument(
        '--upgrade',
        '-u',
        action='store_true',
        help='Upgrade the package.'
    )
    # parse the command-line argument to get the module path
    args = parser.parse_args()
    package_name = parser.prog  # Get the package name from the parser
    return args, package_name

# NOTE: the below was in attempt to check for the most recent version before upgrade
# having trouble getting the most recent version from PyPI
# everything else seems to work

# def get_installed_version(package_name):
#     """returns the current version of the package"""
#     try:
#         installed_version = __version__
#         # installed_version = subprocess.check_output(['pip', 'show', package_name]).decode().split('\n')[1].split(': ')[1]
#         return installed_version
#     except ValueError as e:
#         print(f"Error getting installed version: {e}")
#         return False

# def get_latest_version(package_name):
#     """returns the latest version of the package"""
#     try:
#         output = subprocess.check_output(['pip', 'show', package_name, '--no-cache-dir']).decode()
#         version_line = [
#             line for line in output.split('\n')
#             if line.lower().startswith('version:')
#         ][0]
#         latest_version = version_line.split(': ')[1].strip()
#         return latest_version
#     except ValueError as e:
#         print(f"Error getting latest version: {e}")
#         return None

# def check_update(package_name):
#     """finds and compares the latest version to the installed version."""
#     # Get the installed version of the package
#     installed_version = get_installed_version(package_name)
#     # Get the latest version of the package from PyPI
#     latest_version = get_latest_version(package_name)
#     # Compare the installed version with the latest version
#     if installed_version == latest_version:
#         print(f"{package_name} is already up to date (version {installed_version})")
#         return True
#     print(f"{package_name} is not up to date (installed version: {installed_version}, latest version: {latest_version})")
#     return False

def generate_test(name):
    """check if a script name was provided"""
    template_data = {
        'name': name
    }
    script_content = script_template.substitute(template_data)
    output_file_path = f'{name}.py'
    with open(output_file_path, 'w', encoding="utf-8") as f:
        f.write(script_content)
    print(f"\nThe {name}.py file has been created.")
    print("You can run this file with the command:\n")
    print(f"model-checker {name}.py\n")

def ask_generate_test():
    """prompt user to create a test file"""
    result = input("Would you like to generate a new test file? (y/n): ")
    if result in {'Yes', 'yes', 'y', 'Y'}:
        test_name = input("Enter the name of your test using snake_case: ")
        generate_test(test_name)
        return
    print("You can run a test.py file that already exists with the command:\n")
    print("model-checker test.py\n")

def ask_save():
    """print the model and prompt user to store the output"""
    result = input("Would you like to save the output? (y/n):\n")
    if not result in ['Yes', 'yes', 'y']:
        return None, None
    cons_input = input("\nWould you like to include the Z3 constraints? (y/n):\n")
    print_cons = bool(cons_input in ['Yes', 'yes', 'y'])
    file_name = input(
        "\nEnter the file name in snake_case without an extension.\n"
        "Leave the file name blank to append the output to the project file.\n"
        "\nFile name:\n"
    )
    return file_name, print_cons

def no_model_save_or_append(module, model_structure, file_name):
    """option to save or append if no model is found"""
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            model_structure.no_model_print(f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py generated from {module.parent_file}\n"""', file=n)
        model_structure.no_model_save(n)
    print()


def save_or_append(module, structure, file_name, print_cons, print_imposs):
    """option to save or append if a model is found"""
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            structure.print_to(print_cons, print_imposs, f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py generated from {module.parent_file}\n"""', file=n)
        structure.save_to(print_cons, print_imposs, n)
    print()

def optimize_N(module, past_module=None, past_model_setup=None, sat=False):
    """finds the min value of N for there to be a model up to a timeout limit"""
    model_setup = make_model_for(module.N, module.premises, module.conclusions, module.max_time)
    if model_setup.model_status:
        sat = True
        past_module = module
        module.N -= 1
        min_module, model_setup = optimize_N(module, past_module, model_setup, sat)
        return min_module, model_setup
    if sat:
        return past_module, past_model_setup
    if model_setup.model_runtime < model_setup.max_time:
        past_module = module
        module.N += 1
        max_module, model_setup = optimize_N(module, past_module, model_setup, sat)
        return max_module, model_setup
    if model_setup.timeout:
        return past_module, past_model_setup
    raise ValueError(
        f"Something has gone wrong in optimize_N."
    )

def main():
    """load a test or generate a test when run without input"""
    # TODO: can module_name and module_path be extracted from the sys.argv?
    # this would reduce the number of arguments returned by parse_file_and_flags()
    args, package_name = parse_file_and_flags()
    if args.upgrade:
        try:
            subprocess.run(['pip', 'install', '--upgrade', package_name], check=True)
        except subprocess.CalledProcessError as e:
            print(f"Failed to upgrade {package_name}: {e}")
        return
    if len(sys.argv) < 2:
        ask_generate_test()
        return
    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    module = LoadModule(module_name, module_path)
    print_imposs = module.print_impossible_states_bool or args.impossible
    print_cons = module.print_cons_bool or args.constraints
    save_model = module.save_bool or args.save
    optimize_model = module.optimize or args.optimize
    if optimize_model:
        module, model_setup = optimize_N(module)
    else:
        model_setup = make_model_for(module.N, module.premises, module.conclusions, module.max_time)
    if model_setup.timeout:
        print(f"Model timed out at {model_setup.model_runtime}.")
        print(f"Consider increasing max_time > {model_setup.max_time}.")
        return
    if model_setup.model_status:
        states_print = StateSpace(model_setup)
        states_print.print_to(print_cons, print_imposs)
        if save_model:
            file_name, print_cons = ask_save()
            save_or_append(module, states_print, file_name, print_cons, print_imposs)
        return
    model_setup.no_model_print()
    if save_model:
        file_name, print_cons = ask_save()
        no_model_save_or_append(module, model_setup, file_name)

if __name__ == "__main__":
    main()
    # cProfile.run('main()')
    # cProfile.run('main()', 'profile_results')


# # Load the profiling data
# with open('profile_results', 'r') as f:
#     # profiler = pstats.Stats(f)
#     filename = 'profile_results'
#     profiler = pstats.Stats(filename)
#
# # Sort and print the profiling data by time
# profiler.sort_stats('time').print_stats()
