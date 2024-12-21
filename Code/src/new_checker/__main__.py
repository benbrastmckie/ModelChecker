'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
'''

import sys
import os
import subprocess
# from concurrent.futures import ThreadPoolExecutor
from string import Template
import argparse
import importlib.util
# from threading import (
#     Thread,
#     Event,
# )
# import time
# from tqdm import tqdm
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
from utils import (
    optimize_model_setup,
)

# ### FOR PACKAGING ###
# from model_checker.__init__ import __version__

script_template = Template("""
'''
Model Checker: ${name}
'''
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

#################################
### IMPORT FROM MODEL-CHECKER ###
#################################

import syntactic

from semantic import (
    Semantics,
    Proposition,
)

from model import(
    ModelConstraints,
    ModelStructure,
)

########################
### IMPORT OPERATORS ###
########################

operators = syntactic.OperatorCollection(
    AndOperator, NegationOperator, OrOperator, # primitive extensional
    ConditionalOperator, BiconditionalOperator, # defined extensional
    TopOperator, BotOperator, # primitive extremal
    GroundOperator, EssenceOperator, IdentityOperator, # primitive constitutive
    NecessityOperator, # primitive modal
    PossiblityOperator, # defined modal
    CounterfactualOperator, # primitive counterfactual
    MightCounterfactualOperator, # defined counterfactual
)

from primitive import (
    AndOperator, NegationOperator, OrOperator, # primitive extensional
    TopOperator, BotOperator, # primitive extremal
    GroundOperator, EssenceOperator, IdentityOperator, # primitive constitutive
    NecessityOperator, # primitive modal
    CounterfactualOperator, # primitive counterfactual
)

from defined import (
    ConditionalOperator, BiconditionalOperator, # defined extensional
    PossiblityOperator, # defined modal
    MightCounterfactualOperator, # defined counterfactual
)

################################
########## SETTINGS ############
################################

# time cutoff for increasing N
max_time = 1

# find a countermodel with the smallest value of N within max_time
optimize = False

# print all Z3 constraints if a model is found
print_constraints = False

# print all states including impossible states
print_impossible = False

# present option to append output to file
save_output = False


################################
############ SYNTAX ############
################################

### SENTENCE LETTERS ###

# 'A', 'B', 'C',... can be used for sentence letters.

# Alternatively, 'RedBall', 'MarySings',... or 'red_ball', 'mary_sings',...
# can be used for sentence letters.

# NOTE: Sentence letters cannot include '\\' which is reserved for operators.


### PRIMATIVE EXTREMAL OPERATORS ###

# '\\top' and '\\bot' are zero-place extremal operators.


### UNARY OPERATORS ###

# Negation (primitive): '\\neg', e.g., '\\neg A'.
# Necessity (primitive): '\\Box', e.g., '\\Box A'.
# Possibility (defined): '\\Diamond', e.g., '\\Diamond A'.

# NOTE: parentheses must not be included for unary operators.


### BINARY OPERATORS ###

# Conjunction (primitive): '\\wedge', e.g., '(A \\wedge B)'
# Disjunction (primitive): '\\vee', e.g., '(A \\vee B)'
# Material Conditional (defined): '\\rightarrow', e.g., '(A \\rightarrow B)'
# Biconditional (defined): '\\leftrightarrow', e.g., '(A \\leftrightarrow B)'

# Must Counterfactual (primitive): '\\boxright', e.g., '(A \\boxright B)'
# Might Counterfactual (defined): '\\circleright', e.g., '(A \\circleright B)'

# Ground (primitive): '\\leq', e.g., '(A \\leq B)'
# Essece (primitive): '\\sqsubseteq', e.g., '(A \\sqsubseteq B)'
# Propositional Identity (primitive): '\\equiv', e.g., '(A \\equiv B)'
# Relevance (primitive): '\\preceq', e.g., '(A \\preceq B)'

# NOTE: parentheses must always be included for binary operators.


################################
########## ARGUMENTS ###########
################################

# NOTE: Additional examples can be found at:

https://github.com/benbrastmckie/ModelChecker/tree/master/Examples

### INVALID ###

premises = ['\\neg A','(A \\boxright (B \\vee C))']
conclusions = ['(A \\boxright B)','(A \\boxright C)']
N = 3 # number of atomic states
contingent = False # makes all propositions contingent
non_null = True # prevents the null state from verifying or falsifying
disjoint = False # makes all propositions have disjoint subject-matters
print_impossible = True # shows impossible states

### VALID ###

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']
# N = 3 # number of atomic states
contingent = False # makes all propositions contingent
non_null = True # prevents the null state from verifying or falsifying
disjoint = False # makes all propositions have disjoint subject-matters
print_impossible = True # shows impossible states


###############################
### GENERATE Z3 CONSTRAINTS ###
###############################

# defines the syntax for the language
syntax = syntactic.Syntax(premises, conclusions, operators)

# semantics = Semantics(N)
semantics = ImpositionSemantics(N)

model_constraints = ModelConstraints(
    syntax,
    semantics,
    Proposition,
    contingent=contingent,
    non_null=True,
    disjoint=disjoint,
    print_impossible=True,
)

########################################
### SOLVE, STORE, AND PRINT Z3 MODEL ###
########################################

# finds z3 model, builds a model structure, and prints the model
model_structure = ModelStructure(model_constraints, max_time=1)
model_structure.print_all()

""")

class BuildModule:
    """load module and store values as a class"""
    def __init__(self, module_name, module_path):
        self.module_name = module_name
        self.module_path = module_path
        self.default_values = {
            "N": 3,
            "premises": [],
            "conclusions": [],
            "max_time": 1,
            "contingent": False,
            "disjoint": False,
            "optimize": False,
            "print_constraints": False,
            "print_impossible": False,
            "save_output": False,
        }
        self.parent_file = None
        self.parent_directory = None
        self.N = self.default_values["N"]
        self.premises = self.default_values["premises"]
        self.conclusions = self.default_values["conclusions"]
        self.max_time = self.default_values["max_time"]
        self.contingent = self.default_values["contingent"]
        self.disjoint = self.default_values["disjoint"]
        self.optimize = self.default_values["optimize"]
        self.print_constraints = self.default_values["print_constraints"]
        self.print_impossible = self.default_values["print_impossible"]
        self.save_output = self.default_values["save_output"]
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
        self.contingent = getattr(
            self.module,
            "contingent",
            self.default_values["contingent"]
        )
        self.disjoint = getattr(
            self.module,
            "disjoint",
            self.default_values["disjoint"]
        )
        self.optimize = getattr(
            self.module,
            "optimize",
            self.default_values["optimize"]
        )
        self.print_constraints = getattr(
            self.module,
            "print_constraints",
            self.default_values["print_constraints"]
        )
        self.print_impossible = getattr(
            self.module,
            "print_impossible",
            False
        )
        self.save_output = getattr(self.module, "save_output", True)

    def update_max_time(self, new_max_time):
        self.max_time = new_max_time

    def validate_attributes(self):
        for attr, default_value in self.default_values.items():
            if not hasattr(self.module, attr):
                print(f"The value of '{attr}' is absent and has been set to {default_value}.")

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
            model_structure.no_model_print(module.print_cons, f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py generated from {module.parent_file}\n"""', file=n)
        model_structure.no_model_save(module.print_constraints, n)
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





def load_module(args):
    """Returns a module from the arguments provided from the specified file.
    Updates the model to reflect the user specified flags."""
    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    module = BuildModule(module_name, module_path)
    module.contingent = module.contingent or args.contingent
    module.disjoint = module.disjoint or args.disjoint
    module.optimize = module.optimize or args.optimize
    module.print_constraints = module.print_constraints or args.print
    module.print_impossible = module.print_impossible or args.impossible
    module.save_output = module.save_output or args.save_output
    return module

def print_result(module, model_setup):
    """Prints resulting model or no model if none is found."""
    if model_setup.model_status:
        states_print = StateSpace(model_setup)
        states_print.print_to(module.print_constraints, module.print_impossible)
        if module.save_output:
            file_name, print_cons = ask_save()
            save_or_append(module, states_print, file_name, print_cons, module.print_imposs)
        return
    model_setup.no_model_print(module.print_constraints)
    if module.save_output:
        file_name, print_cons = ask_save()
        no_model_save_or_append(module, model_setup, file_name)


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

    module = load_module(args)

    module, model_setup = optimize_model_setup(module)

    print_result(module, model_setup)

if __name__ == "__main__":
    main()
