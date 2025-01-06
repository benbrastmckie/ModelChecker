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
from src.model_checker.__init__ import __version__
from src.model_checker.builder import make_model_for

class BuildModule:
    """Load and store module values with settings and validation.
    
    This class handles loading a Python module and extracting its model checking
    configuration including premises, conclusions, and various settings.
    """
    
    DEFAULT_EXAMPLE = {
        "premises": [],
        "conclusions": [],
    }
    
    DEFAULT_SETTINGS = {
        "N": 3,
        "contingent": False,
        "non_empty": False,
        "non_null": False,
        "disjoint": False,
        "print_impossible": False,
        "print_constraints": False,
        "save_output": False,
        "max_time": 1,
        # "optimize": False,
    }

    def __init__(self, module_name: str, module_path: str):
        """Initialize BuildModule with module name and path.
        
        Args:
            module_name: Name of the module to load
            module_path: File path to the module
        
        Raises:
            ImportError: If module cannot be loaded
        """
        self.module_name = module_name
        self.module_path = module_path
        self.module = self.load_module()
        
        # Load core attributes
        self.semantics = getattr(self.module, "semantics", None)
        self.proposition = getattr(self.module, "proposition", None)
        self.operators = getattr(self.module, "operators", None)
        
        # Load example configuration
        self.premises = getattr(self.module, "premises", self.DEFAULT_EXAMPLE["premises"])
        self.conclusions = getattr(self.module, "conclusions", self.DEFAULT_EXAMPLE["conclusions"])
        
        # Initialize settings
        self._init_settings()
        self.validate_required_attributes()

    def _init_settings(self):
        """Initialize all settings from module with defaults."""
        module_settings = getattr(self.module, "settings", {})
        
        # Initialize each setting from module_settings with fallback to defaults
        for key, default_value in self.DEFAULT_SETTINGS.items():
            setattr(self, key, module_settings.get(key, default_value))
        
        # Store complete settings dict
        self.settings = {
            key: getattr(self, key)
            for key in self.DEFAULT_SETTINGS
        }

    def load_module(self):
        """Load the Python module from file.
        
        Returns:
            The loaded module object
            
        Raises:
            ImportError: If module cannot be loaded
        """
        try:
            spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
            if spec is None or spec.loader is None:
                raise ImportError("Module spec could not be loaded.")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
        except Exception as e:
            raise ImportError(f"Failed to load the module '{self.module_name}': {e}") from e

    def validate_required_attributes(self):
        """Validate that required module attributes are present and check for missing defaults."""
        # Check required attributes
        required = ["semantics", "proposition", "operators"] 
        missing = [attr for attr in required if getattr(self, attr) is None]
        if missing:
            raise ValueError(
                f"Module {self.module_name} is missing required attributes: {', '.join(missing)}"
            )

        # Check for missing example defaults
        for key, default_val in self.DEFAULT_EXAMPLE.items():
            module_val = getattr(self.module, key, None)
            if module_val is None:
                print(f"Warning: Module {self.module_name} is missing '{key}', using default value: {default_val}")

        # Check for missing settings defaults  
        module_settings = getattr(self.module, "settings", {})
        for key, default_val in self.DEFAULT_SETTINGS.items():
            if key not in module_settings:
                print(f"Warning: Module {self.module_name} settings missing '{key}', using default value: {default_val}")

# TODO: continue moving functions above into the class below
class BuildExample:
    """Class to create and store model structure with settings as attributes."""
    def __init__(self, module_flags):
        """Initialize model structure from module flags."""
        module_path = module_flags.file_path
        module_name = os.path.splitext(os.path.basename(module_path))[0]
        self.module = BuildModule(module_name, module_path)

        # Set settings as instance attributes
        self.N = self.module.settings["N"]
        self.contingent = self.module.settings["contingent"] or module_flags.contingent
        self.non_empty = self.module.settings["non_empty"] or module_flags.non_empty
        self.non_null = self.module.settings["non_null"] or module_flags.non_null
        self.disjoint = self.module.settings["disjoint"] or module_flags.disjoint
        self.print_constraints = self.module.settings["print_constraints"] or module_flags.print_constraints
        self.print_impossible = self.module.settings["print_impossible"] or module_flags.print_impossible
        self.save_output = self.module.settings["save_output"] or module_flags.save_output
        self.max_time = self.module.settings["max_time"]

        # Create model structure
        self.model_structure = make_model_for(
            self.__dict__,
            self.module.premises,
            self.module.conclusions, 
            self.module.semantics,
            self.module.proposition,
            self.module.operators,
        )

    def print_result(self):
        """Prints resulting model or no model if none is found."""
        model_structure = self.model_structure
        print_constraints = model_structure.settings["print_constraints"]
        if model_structure.z3_model_status:
            model_structure.print_to(print_constraints)
            if model_structure.settings["save_output"]:
                file_name, save_constraints = self.ask_save()
                self.save_or_append(model_structure, model_structure, file_name, save_constraints)
            return
        model_structure.no_model_print_to(print_constraints)
        if model_structure.settings["save_output"]:
            file_name, save_constraints = self.ask_save()
            self.no_model_save_or_append(self.module, model_structure, file_name, save_constraints)

    def no_model_save_or_append(self, module, model_structure, file_name, print_cons):
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

    def ask_save(self):
        """print the model and prompt user to store the output"""
        result = input("Would you like to save the output? (y/n):\n")
        if not result in ['Yes', 'yes', 'Ye', 'ye', 'Y', 'y']:
            return None, None
        cons_input = input("\nWould you like to include the Z3 constraints? (y/n):\n")
        print_cons = bool(cons_input in ['Yes', 'yes', 'Ye', 'ye', 'Y', 'y'])
        file_name = input(
            "\nEnter the file name in snake_case without an extension.\n"
            "Leave the file name blank to append the output to the project file.\n"
            "\nFile name: "
        )
        return file_name, print_cons

    def save_or_append(self, module, model_structure, file_name, print_constraints):
        """Option to save or append if a model is found."""
        if file_name is None:
            return
        if len(file_name) == 0:
            with open(f"{module.module_path}", 'a', encoding="utf-8") as f:
                print('\n"""', file=f)
                model_structure.print_to(print_constraints, f)
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
            model_structure.save_to(print_constraints, n)  # TODO: add function
        print(f'\n{file_name}.py created in {destination_dir}\n')

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
        '--print_constraints',
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
        '--print_impossible',
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
    flags = parser.parse_args()
    package_name = parser.prog  # Get the package name from the parser
    return flags, package_name

def main():
    if len(sys.argv) < 2:
        ask_generate_project()
        return
    module_flags, package_name = parse_file_and_flags()
    if module_flags.upgrade:
        print("Upgrading package")
        try:
            subprocess.run(['pip', 'install', '--upgrade', package_name], check=True)
        except subprocess.CalledProcessError as e:
            print(f"Failed to upgrade {package_name}: {e}")
        return

    example = BuildExample(module_flags)

    example.print_result()

if __name__ == "__main__":
    main()
