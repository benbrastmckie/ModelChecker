'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
to test from the Code/ directory, run: python -m src.model_checker 
'''

import sys
import os
import shutil
import subprocess
import argparse
import importlib.util
from model_checker.__init__ import __version__

class BuildModule:
    """load module and store values as a class"""
    def __init__(self, module_name, module_path):
        self.module_name = module_name
        self.module_path = module_path
        self.module = self.load_module()
        self.default_values = {
            "N": 3,
            "premises": [],
            "conclusions": [],
            "max_time": 1,
            "contingent": False,
            "non_empty": False,
            "non_null": False,
            "disjoint": False,
            # "optimize": False,
            "print_constraints": False,
            "print_impossible": False,
            "save_output": False,
        }
        self.settings = getattr(
            self.module,
            "settings",
            None
        )
        self.model_structure = getattr(
            self.module,
            "model_structure",
            None
        )
        self.print_command = getattr(
            self.module,
            "print_command",
            None
        )
        self.N = getattr(
            self.settings,
            "N",
            None
        )
        self.premises = getattr(
            self.module,
            "premises",
            self.default_values["premises"]
        )
        self.conclusions = getattr(
            self.module,
            "conclusions",
            self.default_values["conclusions"]
        )
        self.max_time = getattr(
            self.settings,
            "max_time",
            self.default_values["max_time"]
        )
        self.contingent = getattr(
            self.settings,
            "contingent",
            self.default_values["contingent"]
        )
        self.non_empty = getattr(
            self.settings,
            "non_empty",
            self.default_values["non_empty"]
        )
        self.non_null = getattr(
            self.settings,
            "non_null",
            self.default_values["non_null"]
        )
        self.disjoint = getattr(
            self.settings,
            "disjoint",
            self.default_values["disjoint"]
        )
        # self.optimize = getattr(
        #     self.settings,
        #     "optimize",
        #     self.default_values["optimize"]
        # )
        self.print_constraints = getattr(
            self.settings,
            "print_constraints",
            self.default_values["print_constraints"]
        )
        self.print_impossible = getattr(
            self.settings,
            "print_impossible",
            self.default_values["print_impossible"]
        )
        self.save_output = getattr(
            self.module,
            "save_output",
            self.default_values["save_output"]
        )
        # TODO: fix
        # self.validate_attributes()

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

    # TODO: fix to check just the settings
    # def validate_attributes(self):
    #     # print(f"TEST: {self.settings}")
    #     for attr, default_value in self.default_values.items():
    #         # print(f"ATTR {attr} {type(attr)} DEFAULT {default_value} {type(default_value)}")
    #         if attr not in self.settings:
    #             print(f"The value of '{attr}' is absent and has been set to {default_value}.")

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
        '--non_empty',
        '-e',
        action='store_true',
        help='Overrides to make all propositions non_empty.'
    )
    parser.add_argument(
        '--non_null',
        '-n',
        action='store_true',
        help='Overrides to make all propositions non_null.'
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
        '--save_output',
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
    # parser.add_argument(
    #     '--optimize',
    #     '-o',
    #     action='store_true',
    #     help='finds the minimum value for N that is satisfiable before reaching max_time.'
    # )
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

# def generate_test(name):
#     """check if a script name was provided"""
#     template_data = {
#         'name': name
#     }
#     script_content = script_template.substitute(template_data)
#     output_file_path = f'{name}.py'
#     with open(output_file_path, 'w', encoding="utf-8") as f:
#         f.write(script_content)
#     print(f"\nThe {name}.py file has been created.")
#     print("You can run this file with the command:\n")
#     print(f"model-checker {name}.py\n")

def generate_project(name):
    """
    Copy the 'template/' directory to the current working directory, 
    rename it to the specified 'name', and rename its modules by prefixing 'name'.
    """
    project_name = 'project_' + name
    # Dynamically resolve the source directory relative to this script
    source_dir = os.path.join(os.path.dirname(__file__), 'template')  
    destination_dir = os.path.join(os.getcwd(), project_name)  

    try:
        # Check if the source directory exists
        if not os.path.exists(source_dir):
            raise FileNotFoundError(f"The source directory '{source_dir}' was not found.")

        # Check if the destination directory already exists
        if os.path.exists(destination_dir):
            print(f"Error: Directory '{destination_dir}' already exists.")
            return

        # Copy the template directory
        shutil.copytree(source_dir, destination_dir)

        # Rename the files in the copied directory
        files_to_rename = {
            "examples.py": "examples.py",
            "operators.py": "operators.py",
            "semantics.py": "semantics.py",
        }
        
        for old_name, new_name in files_to_rename.items():
            old_path = os.path.join(destination_dir, old_name)
            new_path = os.path.join(destination_dir, new_name)
            if os.path.exists(old_path):
                os.rename(old_path, new_path)

        print(f"\nProject generated at: {destination_dir}\n")
        print("The following modules were created:")
        for old_name, new_name in files_to_rename.items():
            print(f"  {new_name}")

        # Run the example script
        example_script = os.path.join(destination_dir, "examples.py")
        print(example_script)
        if os.path.exists(example_script):
            print("\nRunning the example script...")
            subprocess.run(["model-checker", example_script])
        else:
            print(f"\nFail to run: model-checker {example_script}")

        # Output the test command
        print(f"\nRun the following command to test your project:\n\nmodel-checker {destination_dir}/examples.py\n")
    
    except FileNotFoundError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

def ask_generate_project():
    """prompt user to create a test file"""
    result = input("Would you like to generate a new project? (y/n): ")
    if result in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
        test_name = input("Enter the name of your project using snake_case: ")
        generate_project(test_name)
        return
    print("You can run an example.py file that already exists with the command:\n")
    print("model-checker example.py\n")

def ask_save():
    """print the model and prompt user to store the output"""
    result = input("Would you like to save the output? (y/n):\n")
    if not result in ['Yes', 'yes', 'Ye', 'ye', 'Y', 'y']:
        VOID = ""
        return VOID, False
    cons_input = input("\nWould you like to include the Z3 constraints? (y/n):\n")
    print_cons = bool(cons_input in ['Yes', 'yes', 'Ye', 'ye', 'Y', 'y'])
    file_name = input(
        "\nEnter the file name in snake_case without an extension.\n"
        "Leave the file name blank to append the output to the project file.\n"
        "\nFile name: "
    )
    return file_name, print_cons

def no_model_save_or_append(module, model_structure, file_name, print_cons):
    """option to save or append if no model is found"""
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            # TODO: add method
            model_structure.no_model_print(print_cons, f)
            print('"""', file=f)
        return
    destination_dir = os.path.join(os.getcwd(), module.module_name)  
    with open(f"{destination_dir}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py created in {destination_dir}\n"""', file=n)
        # TODO: add method
        model_structure.no_model_save(print_cons, n)
    print()

def save_or_append(module, model_structure, file_name, print_cons):
    """Option to save or append if a model is found."""
    if len(file_name) == 0:
        with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
            print('\n"""', file=f)
            model_structure.print_to(print_cons, f)  # TODO: add function
            print('"""', file=f)
        print(f"\nAppended output to {module.module_path}")
        return

    # Default or fallback path
    project_name = getattr(module, 'module_name', 'project')
    destination_dir = os.path.join(os.getcwd(), project_name)
    
    # Ensure the directory exists
    os.makedirs(destination_dir, exist_ok=True)

    with open(f"{destination_dir}/{file_name}.py", 'w', encoding="utf-8") as n:
        print(f'# TITLE: {file_name}.py created in {destination_dir}\n"""', file=n)
        model_structure.save_to(print_cons, n)  # TODO: add function
    print(f'\n{file_name}.py created in {destination_dir}\n')

def create_module(args):
    """Returns a module from the arguments provided from the specified file.
    Updates the model to reflect the user specified flags."""
    module_path = args.file_path
    module_name = os.path.splitext(os.path.basename(module_path))[0]
    module = BuildModule(module_name, module_path)
    module.contingent = module.contingent or args.contingent
    module.non_empty = module.non_empty or args.non_empty
    module.non_null = module.non_null or args.non_null
    module.disjoint = module.disjoint or args.disjoint
    # module.optimize = module.optimize or args.optimize
    module.print_constraints = module.print_constraints or args.print
    module.print_impossible = module.print_impossible or args.impossible
    module.save_output = module.save_output or args.save_output
    return module

def print_result(module):
    """Prints resulting model or no model if none is found."""
    model_structure = module.model_structure
    if model_structure.z3_model_status:
        module.print_command
        # TODO: turn on once print_to and save_to have been added
        if module.save_output:
            file_name, print_cons = ask_save()
            save_or_append(module, model_structure, file_name, print_cons)
        return
    # # TODO: turn on once print_to and save_to have been added
    # model_structure.no_model_print(module.print_constraints)
    # if module.save_output:
    #     file_name, print_cons = ask_save()
    #     no_model_save_or_append(module, model_structure, file_name, print_cons)


def main():
    if len(sys.argv) < 2:
        ask_generate_project()
        return
    args, package_name = parse_file_and_flags()
    if args.upgrade:
        print("Upgrading package")
        try:
            subprocess.run(['pip', 'install', '--upgrade', package_name], check=True)
        except subprocess.CalledProcessError as e:
            print(f"Failed to upgrade {package_name}: {e}")
        return

    module = create_module(args)

    print_result(module)

if __name__ == "__main__":
    main()
