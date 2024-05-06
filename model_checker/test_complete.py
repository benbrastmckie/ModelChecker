'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
'''

import argparse
import os
import importlib.util
import sys
from string import Template
from package.model_structure import make_model_for

script_template = Template("""
'''
Model Checker: ${name}
'''
import os
parent_directory = os.path.dirname(__file__)

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

# use constraints to find models in stead of premises and conclusions
use_constraints_bool = False

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

def print_or_save(module):
    """print the model and prompt user to store the output"""
    mod = make_model_for(module.N)(module.premises, module.conclusions)
    if module.use_constraints_bool:
        mod.constraints = module.all_constraints
    mod.print_to(module.print_cons_bool, module.print_unsat_core_bool)
    if not module.save_bool:
        return
    result = input("Would you like to save the output? (y/n):\n")
    if not result in ['Yes', 'yes', 'y']:
        return
    cons_input = input("\nWould you like to include the Z3 constraints? (y/n):\n")
    cons_include = bool(cons_input in ['Yes', 'yes', 'y'])
    output_file_name = input("\nEnter the file name or leave blank to append the output to the project file:\n")
    if len(output_file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            mod.print_to(cons_include, cons_include, f)
            print('"""', file=f)
        return
    with open(f"{module.parent_directory}/{output_file_name}.py", 'w', encoding="utf-8") as n:
        mod.save_to(output_file_name, cons_include, n)
    print()

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
            raise ImportError(f"Failed to load the module '{self.module_name}': {e}")

    def validate_attributes(self):
        required_attrs = ["N", "premises", "conclusions"]
        for attr in required_attrs:
            if not hasattr(self.module, attr):
                raise ImportError(f"The value of '{attr}' is absent")

    def initialize_attributes(self):
        self.parent_directory = getattr(self.module, "parent_directory", True)
        self.N = getattr(self.module, "N")
        self.premises = getattr(self.module, "premises")
        self.conclusions = getattr(self.module, "conclusions")
        self.print_cons_bool = getattr(self.module, "print_cons_bool", False)
        self.print_unsat_core_bool = getattr(self.module, "print_unsat_core_bool", True)
        self.save_bool = getattr(self.module, "save_bool", True)
        self.use_constraints_bool = getattr(self.module, "use_constraints", False)
        self.all_constraints = getattr(self.module, "all_constraints", [])

def parse_script_name_and_path():
    """returns the name and path for the current script"""
    # create an ArgumentParser object
    parser = argparse.ArgumentParser(description="Import variables from another file")
    parser.add_argument(
        "file_path",
        type=str,
        help="Path to the Python file to read."
    )
    # parse the command-line argument to get the module path
    args = parser.parse_args()
    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    # module_name = "dynamic_module"
    return module_name, module_path

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
    print("You can run this file with the command:")
    print(f"python3 test_complete.py {name}.py")

def ask_generate_test():
    """prompt user to create a test file"""
    result = input("Would you like to generate a new test file? (y/n): ")
    if result in {'Yes', 'yes', 'y', 'Y'}:
        test_name = input("Enter the name of your test using snake_case: ")
        generate_test(test_name)
        return
    print("You can run a test.py file that already exists with the command:\n")
    print("python3 test_complete.py test.py\n")

def main():
    """load a test or generate a test when run without input"""
    if len(sys.argv) < 2:
        ask_generate_test()
        return
    module_name, module_path = parse_script_name_and_path()
    module = LoadModule(module_name, module_path)
    print_or_save(module)

if __name__ == "__main__":
    main()
