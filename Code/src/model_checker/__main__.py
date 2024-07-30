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
# from concurrent.futures import ThreadPoolExecutor
from threading import (
    Thread,
    Event,
)
import time
from tqdm import tqdm
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

# ### FOR TESTING ###
# from __init__ import __version__
# from model_structure import (
#     StateSpace,
#     make_model_for,
#     )

### FOR PACKAGING ###
from model_checker.__init__ import __version__
from model_checker.model_structure import (
    StateSpace,
    make_model_for,
    )

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

# time cutoff for increasing N
max_time = 1

# find a countermodel with the smallest value of N within max_time
optimize_bool = False

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
# Possibility: 'Diamond', e.g., 'Diamond A'. 

# NOTE: parentheses must not be included for unary operators.


### BINARY OPERATORS ###

# Conjunction: 'wedge', e.g., '(A wedge B)'
# Disjunction: 'vee', e.g., '(A vee B)'
# Conditional: 'rightarrow', e.g., '(A rightarrow B)'
# Biconditional: 'leftrightarrow', e.g., '(A leftrightarrow B)'
# Must Counterfactual: 'boxright', e.g., '(A boxright B)'
# Might Counterfactual: 'circright', e.g., '(A circright B)'
# Ground: 'leq', e.g., '(A leq B)'
# Essece: 'sqsubseteq', e.g., '(A sqsubseteq B)'
# Propositional Identity: 'equiv', e.g., '(A equiv B)'
# Relevance: 'preceq', e.g., '(A preceq B)'

# NOTE: parentheses must always be included for binary operators.


################################
########## ARGUMENTS ###########
################################

# NOTE: Additional examples can be found at: https://github.com/benbrastmckie/ModelChecker/tree/master/Examples

### INVALID ###

premises = ['neg A','(A boxright (B vee C))']
conclusions = ['(A boxright B)','(A boxright C)']
N = 3 # number of atomic states
contingent_bool = False # make all propositions contingent
disjoint_bool = False # make all propositions have disjoint subject-matters

### VALID ###

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']
# N = 3 # number of atomic states
# contingent_bool = False # make all propositions contingent
# disjoint_bool = False # make all propositions have disjoint subject-matters

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
            "max_time": 1,
            "contingent_bool": False,
            "disjoint_bool": False,
            "optimize_bool": False,
            "print_cons_bool": False,
            "print_impossible_states_bool": False,
            "save_bool": False,
        }
        self.parent_file = None
        self.parent_directory = None
        self.N = self.default_values["N"]
        self.premises = self.default_values["premises"]
        self.conclusions = self.default_values["conclusions"]
        self.max_time = self.default_values["max_time"]
        self.contingent_bool = self.default_values["contingent_bool"]
        self.disjoint_bool = self.default_values["disjoint_bool"]
        self.optimize_bool = self.default_values["optimize_bool"]
        self.print_cons_bool = self.default_values["print_cons_bool"]
        self.print_impossible_states_bool = self.default_values["print_impossible_states_bool"]
        self.save_bool = self.default_values["save_bool"]
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
        self.max_time = float(getattr(self.module, "max_time", self.default_values["max_time"]))
        self.contingent_bool = getattr(
            self.module,
            "contingent_bool",
            self.default_values["contingent_bool"]
        )
        self.disjoint_bool = getattr(
            self.module,
            "disjoint_bool",
            self.default_values["disjoint_bool"]
        )
        self.optimize_bool = getattr(
            self.module,
            "optimize_bool",
            self.default_values["optimize_bool"]
        )
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

    def update_max_time(self, new_max_time):
        self.max_time = new_max_time

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
        '--contingent',
        '-c',
        action='store_true',
        help='Overrides to make all propositions contingent.'
    )
    parser.add_argument(
        '--disjoint',
        '-d',
        action='store_true',
        help='Overrides to make all propositions have disjoint subject-matters.'
    )
    parser.add_argument(
        '--print',
        '-p',
        action='store_true',
        help='Overrides to print the Z3 constraints or else the unsat_core constraints if there is no model.'
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
        model_structure.no_model_save(module.print_cons_bool, n)
    print()

def save_or_append(module, model_setup, file_name, print_cons, print_imposs):
    """option to save or append if a model is found"""
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            model_setup.print_to(print_cons, print_imposs, f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py generated from {module.parent_file}\n"""', file=n)
        model_setup.save_to(print_cons, print_imposs, n)
    print()

def adjust(module, offset):
    """Redefines module and model_setup after adjusting N by the offset."""
    module.N += offset
    model_setup = make_model_for(
        module.N,
        module.premises,
        module.conclusions,
        module.max_time,
        module.contingent_bool,
        module.disjoint_bool,
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
    # timed out looking for models
    previous_N = model_setup.N - 1
    print(f"There are no {previous_N}-models.")
    print(f"No {model_setup.N}-models were found within {model_setup.max_time} seconds.")
    new_max_time = ask_time(model_setup.model_runtime, model_setup.max_time)
    if new_max_time is None:
        print("Process terminated.")
        print(f"Consider increasing max_time to be > {model_setup.max_time} seconds.\n")
        model_setup.N = previous_N
        model_setup.no_model_print(module.print_cons_bool)
        os._exit(1)
    module.update_max_time(new_max_time)
    return optimize_model_setup(module, True)

def progress_bar(max_time, stop_event):
    """Show progress bar for how much of max_time has elapsed."""
    step_time = max_time / 100
    with tqdm(
        desc="Running model-checker: ",
        total=100,
        unit="step",
        bar_format="{l_bar}{bar}| {n_fmt}/{total_fmt}",
    ) as pbar:
        while not stop_event.is_set():
            time.sleep(step_time) # NOTE: gives bad result if multiplied by 4
            pbar.update(1)
            if pbar.n >= 100:
                stop_event.set()  # Signal the progress bar to stop

def create_model_setup(module):
    """Creates a model setup based on module attributes."""
    return make_model_for(
        module.N,
        module.premises,
        module.conclusions,
        module.max_time,
        module.contingent_bool,
        module.disjoint_bool,
    )

def handle_timeout(module, model_setup):
    """Handles timeout scenarios by asking the user for a new time limit."""
    print(f"The model timed out at {model_setup.model_runtime} seconds.")
    new_max_time = ask_time(model_setup.model_runtime, model_setup.max_time)
    if new_max_time is None:
        print("Terminating the process.")
        os._exit(1)
    module.update_max_time(new_max_time)

def optimize_model_setup(module, optimize_model):
    """Runs make_model_for on the values provided by the module and user, optimizing if required."""
    max_time = module.max_time
    stop_event = Event()
    progress_thread = Thread(target=progress_bar, args=(max_time, stop_event))
    progress_thread.start()

    model_setup = None
    try:
        model_setup = create_model_setup(module)
        run_time = model_setup.model_runtime
        if run_time > max_time:
            handle_timeout(module, model_setup)
            # stop_event.set()  # Signal the progress bar to stop
            # progress_thread.join(timeout=max_time)  # Wait for the thread to finish
            module, model_setup = optimize_model_setup(module, model_setup)
        if optimize_model:
            module, model_setup = optimize_N(module, model_setup, module, model_setup)

    finally:
        stop_event.set()  # Signal the progress bar to stop
        progress_thread.join(timeout=max_time)  # Wait for the thread to finish

    return module, model_setup

# def optimize_model_setup(module, optimize_model):
#     """Main function: Creates, optimizes (if needed), and manages model setup process."""
#
#     stop_event = Event()
#
#     with ThreadPoolExecutor() as executor:
#         # Run model creation and progress bar in parallel
#         model_future = executor.submit(create_model_setup, module)
#         progress_future = executor.submit(show_progress, module.max_time, stop_event)
#
#         model_setup = model_future.result()
#         module, model_setup = optimize_if_needed(module, model_setup, optimize_model)
#         stop_event.set()  # Stop the progress bar
#         progress_future.result()  # Ensure progress bar thread completes
#
#     while module.timeout:
#         handle_timeout(module, model_setup)
#         model_setup = create_model_setup(module)
#         module, model_setup = optimize_if_needed(module, model_setup, optimize_model)
#
#     return module, model_setup


def main():
    """load a test or generate a test when run without input"""
    if len(sys.argv) < 2:
        ask_generate_test()
        return

    args, package_name = parse_file_and_flags()

    if args.upgrade:
        try:
            subprocess.run(['pip', 'install', '--upgrade', package_name], check=True)
        except subprocess.CalledProcessError as e:
            print(f"Failed to upgrade {package_name}: {e}")
        return

    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    module = LoadModule(module_name, module_path)

    print_imposs = module.print_impossible_states_bool or args.impossible
    print_cons = module.print_cons_bool or args.print
    save_model = module.save_bool or args.save
    optimize_model = module.optimize_bool or args.optimize
    module.contingent_bool = module.contingent_bool or args.contingent

    # shows progress for finding z3 models
    # module, model_setup = optimize_with_progress_bar(module, optimize_model)
    module, model_setup = optimize_model_setup(module, optimize_model)

    if model_setup.model_status:
        states_print = StateSpace(model_setup)
        states_print.print_to(print_cons, print_imposs)
        if save_model:
            file_name, print_cons = ask_save()
            save_or_append(module, states_print, file_name, print_cons, print_imposs)
        return

    # if model_setup.timeout == "unknown":
    #     print(f"No model found. Try increasing max_time > {model_setup.max_time}.\n")
    #     return

    # print(model_setup.z3_model)
    model_setup.no_model_print(print_cons)
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
