'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
'''

from string import Template
import argparse
import importlib.util
import sys
import os
from model_structure import StateSpace, make_model_for
# from model_checker.model_structure import ( # for packaging
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

# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to append output to file
save_bool = False

# print all states including impossible states
print_impossible_states_bool = False


################################
############ SYNTAX ############
################################

### SENTENCES ###

# 'A', 'B', 'C',... can be used for sentence letters

# Alternatively, 'RedBall', 'MarySings',... can be used for sentence letters.

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
        self.module = self.load_module()
        self.validate_attributes()
        self.initialize_attributes()

    def load_module(self):
        try:
            spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
            if spec is None or spec.loader is None:
                raise ImportError("Module spec could not be loaded.")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
        except Exception as e:
            raise ImportError(f"Failed to load the module '{self.module_name}': {e}") from e

    def validate_attributes(self):
        required_attrs = ["N", "premises", "conclusions"]
        for attr in required_attrs:
            if not hasattr(self.module, attr):
                raise ImportError(f"The value of '{attr}' is absent")

    def initialize_attributes(self):
        self.parent_file = getattr(self.module, "file_name", True)
        self.parent_directory = getattr(self.module, "parent_directory", True)
        self.N = getattr(self.module, "N")
        self.premises = getattr(self.module, "premises")
        self.conclusions = getattr(self.module, "conclusions")
        self.print_cons_bool = getattr(self.module, "print_cons_bool", False)
        self.print_unsat_core_bool = getattr(self.module, "print_unsat_core_bool", True)
        self.print_impossible_states_bool = getattr(
            self.module,
            "print_impossible_states_bool",
            False
        )
        self.save_bool = getattr(self.module, "save_bool", True)
        # self.use_constraints_bool = getattr(self.module, "use_constraints", False)
        self.all_constraints = getattr(self.module, "all_constraints", [])

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
    # parse the command-line argument to get the module path
    args = parser.parse_args()
    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    cons_bool = args.constraints
    save_bool = args.save
    imposs_bool = args.impossible
    return module_name, module_path, cons_bool, save_bool, imposs_bool

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

def no_model_save_or_append(module, model_structure, file_name, print_cons, print_imposs):
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            model_structure.no_model_print(print_cons, f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py generated from {module.parent_file}\n"""', file=n)
        model_structure.no_model_save(print_cons, n)
    print()


def save_or_append(module, structure, file_name, print_cons, print_imposs):
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

def main():
    """load a test or generate a test when run without input"""
    if len(sys.argv) < 2:
        ask_generate_test()
        return
    # TODO: can module_name and module_path be extracted from the sys.argv?
    # this would reduce the number of arguments returned by parse_file_and_flags()
    module_name, module_path, cons_flag, save_flag, imposs_flag = parse_file_and_flags()
    module = LoadModule(module_name, module_path)
    print_imposs = module.print_impossible_states_bool or imposs_flag
    print_cons = module.print_cons_bool or cons_flag
    save_model = module.save_bool or save_flag
    model_setup, model_structure = make_model_for(module.N, module.premises, module.conclusions)
    if model_structure.model_status:
        states_print = StateSpace(model_setup, model_structure)
        states_print.print_to(print_cons, print_imposs)
        if save_model:
            file_name, print_cons = ask_save()
            save_or_append(module, states_print, file_name, print_cons, print_imposs)
        return
    print_unsat = module.print_unsat_core_bool or cons_flag
    model_structure.no_model_print(print_unsat)
    if save_model:
        file_name, print_cons = ask_save()
        no_model_save_or_append(module, model_structure, file_name, print_unsat, print_imposs)


if __name__ == "__main__":
    main()
