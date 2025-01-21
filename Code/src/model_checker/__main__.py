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
# Try local imports first (for development)
try:
    from src.model_checker import __version__
    from src.model_checker.builder import (
        make_model_for,
        translate,
    )
    from src.model_checker.model import (
        SemanticDefaults,
        PropositionDefaults
    )
    from src.model_checker.syntactic import OperatorCollection
except ImportError:
    # Fall back to installed package imports
    from model_checker import __version__
    from model_checker.builder import (
        make_model_for,
        translate,
    )
    from model_checker.model import (
        SemanticDefaults,
        PropositionDefaults
    )
    from model_checker.syntactic import OperatorCollection


class BuildModule:
    """Load and store module values with settings and validation.
    
    This class handles loading a Python module and extracting its model checking
    configuration including premises, conclusions, and various settings.
    """
    
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        # "optimize": False,
    }

    def __init__(self, module_flags):
        """Initialize BuildModule with module name and path.
        
        Args:
            module_name: Name of the module to load
            module_path: File path to the module
        
        Raises:
            ImportError: If module cannot be loaded
        """

        self.module_flags = module_flags
        self.module_path = module_flags.file_path
        self.module_name = os.path.splitext(os.path.basename(self.module_path))[0]
        self.module = self._load_module()
        
        # Load core attributes
        self.semantic_theories = self._load_attribute("semantic_theories")
        self.example_range = self._load_attribute("example_range")

        # Load general settings
        self.general_settings = self._load_general_settings()

    def _load_module(self):
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

    def _load_attribute(self, attr_name):
        """Checks if an attribute exists in the module and store it.
        
        Args:
            attr_name: Name of the attribute to check and store
            
        Raises:
            AttributeError: If the attribute is missing from the module
        """
        if not hasattr(self.module, attr_name):
            raise AttributeError(
                f"Module '{self.module_name}' is missing the attribute '{attr_name}'. "
            )
        return getattr(self.module, attr_name, {})

    def _load_general_settings(self):
        """Initialize all settings from module with defaults."""
        general_settings = getattr(self.module, "general_settings", {})
        
        # Initialize each setting from module_settings with fallback to defaults
        for key, default_value in self.DEFAULT_GENERAL_SETTINGS.items():
            if key not in general_settings:
                print(f"Warning: Module {self.module_name} settings missing '{key}', using default value: {default_value}")
            setattr(self, key, general_settings.get(key, default_value))
        
        # Store complete settings dict
        general_settings = {
            key: getattr(self, key)
            for key in self.DEFAULT_GENERAL_SETTINGS
        }

        return general_settings


class BuildExample:
    """Class to create and store model structure with settings as attributes."""

    DEFAULT_EXAMPLE = {
        "premises": [],
        "conclusions": [],
    }
    
    def __init__(self, module, semantic_theory, example_case):

        """Initialize model structure from module flags."""
        self.module = module
        self.semantics, self.proposition, self.operators, self.dictionary = self._validate_semantic_theory(semantic_theory)
        self.DEFAULT_EXAMPLE_SETTINGS = self.semantics.DEFAULT_EXAMPLE_SETTINGS
        self.premises, self.conclusions, example_settings = self._validate_example(example_case)
        self.settings = self._validate_settings(example_settings)

        # # TODO: warn if no premises or no conclusions
        # # Check for missing example defaults
        # for key, default_val in self.DEFAULT_EXAMPLE.items():
        #     module_val = getattr(self.module, key, None)
        #     if module_val is None:
        #         print(f"Warning: Module {self.module_name} is missing '{key}', using default value: {default_val}")

        # # TODO: warn if missing setting
        # # Check for missing settings defaults  
        # module_settings = getattr(self.module, "settings", {})
        # for key, default_val in self.DEFAULT_GENERAL_SETTINGS.items():
        #     if key not in module_settings:
        #         print(f"Warning: Module {self.module_name} settings missing '{key}', using default value: {default_val}")

        # # Set settings as instance attributes
        # for key, value in self.settings.items():
        #     setattr(self, key, value)

        # Create model structure
        self.model_structure = make_model_for(
            self.settings,
            self.premises,
            self.conclusions, 
            self.semantics,
            self.proposition,
            self.operators,
        )

    def _validate_semantic_theory(self, semantic_theory):
        """Validates that semantic_theory contains the required components in the correct order.
        
        Args:
            semantic_theory: A tuple/list containing (Semantics, Proposition, OperatorCollection)
            
        Returns:
            The validated semantic_theory
            
        Raises:
            TypeError: If any component has an invalid type
        """

        if not isinstance(semantic_theory, dict) or len(semantic_theory) < 3:
            raise TypeError(
                "semantic_theory must be a tuple/list containing exactly 3 elements: "
                "(Semantics, Proposition, OperatorCollection)"
            )

        semantics = semantic_theory["semantics"]
        proposition = semantic_theory["proposition"] 
        operators = semantic_theory["operators"]
        dictionary = semantic_theory.get("operators", None)

        # Validate semantics is subclass of SemanticDefaults
        if not issubclass(semantic_theory["semantics"], SemanticDefaults):
            raise TypeError(
                f"First element must be a subclass of SemanticDefaults, got {type(semantics)}"
            )

        # Validate proposition is subclass of PropositionDefaults
        if not issubclass(proposition, PropositionDefaults):
            raise TypeError(
                f"Second element must be a subclass of PropositionDefaults, got {type(proposition)}"
            )

        # Validate operators is instance of OperatorCollection
        if not isinstance(operators, OperatorCollection):
            raise TypeError(
                f"Third element must be an instance of OperatorCollection, got {type(operators)}"
            )

        return semantics, proposition, operators, dictionary

    def _validate_example(self, example_case):
        """Validates that example_case contains lists of strings and a dictionary.
        
        Args:
            example_case: A tuple/list containing (premises, conclusions, settings)
            
        Returns:
            The validated example_case
            
        Raises:
            TypeError: If any component has an invalid type
        """
        if not isinstance(example_case, (tuple, list)) or len(example_case) != 3:
            raise TypeError(
                "example_case must be a tuple/list containing exactly 3 elements: "
                "(premises, conclusions, settings)"
            )

        premises, conclusions, example_settings = example_case

        # Validate premises is a list of strings
        if not isinstance(premises, list) or not all(isinstance(p, str) for p in premises):
            raise TypeError(
                f"First element must be a list of strings, got {type(premises)} "
                f"containing types {[type(p) for p in premises]}"
            )

        # Validate conclusions is a list of strings
        if not isinstance(conclusions, list) or not all(isinstance(c, str) for c in conclusions):
            raise TypeError(
                f"Second element must be a list of strings, got {type(conclusions)} "
                f"containing types {[type(c) for c in conclusions]}"
            )

        # Validate settings is a dictionary
        if not isinstance(example_settings, dict):
            raise TypeError(
                f"Third element must be a dictionary, got {type(example_settings)}"
            )

        return example_case

    def _validate_settings(self, example_settings):
        """Validates and merges example settings with general settings and module flags.
        
        Args:
            example_settings: Dictionary containing settings specific to this example
            
        Returns:
            Dictionary containing the merged and validated settings with module flag overrides
            
        The function performs three steps:
        1. Merges example settings with general settings, warning about overlaps
        2. Updates boolean settings based on module flags
        3. Returns the final merged and validated settings dictionary
        """
        def merge_settings(example_settings, general_settings):
            """Adds example_settings to general_settings, mentioning overlaps."""
            # Track and merge settings

            copy_general = general_settings
            for key, example_value in example_settings.items():
                # Get value from module settings or use default
                general_value = copy_general.get(key, example_value)
                
                # Check if we're replacing an existing general setting
                if key in self.DEFAULT_EXAMPLE.keys() and example_value != general_value:
                    print(f"Warning: Example setting '{key} = {example_value}' is replacing the general setting "
                          f"'{key} = {general_value}'")
                
                # Update the settings
                copy_general[key] = example_value
    
            return copy_general
    
        def disjoin_flags(all_settings):
            """Update boolean settings if module flag is True."""
            module_flags = self.module.module_flags
            updated_settings = all_settings.copy()
            
            for key, value in vars(module_flags).items():
                if isinstance(value, bool) and value and key in updated_settings:
                    updated_settings[key] = value
                    
            return updated_settings
    
        # Merge and update settings
        all_settings = merge_settings(example_settings, self.module.general_settings)
        updated_settings = disjoin_flags(all_settings)
    
        return updated_settings

    def print_result(self, example_name, theory_name):
        """Prints resulting model or no model if none is found."""
        model_structure = self.model_structure
        default_settings = self.DEFAULT_EXAMPLE_SETTINGS
        model_structure.print_to(default_settings, example_name, theory_name)
        if model_structure.settings["save_output"]:
            file_name, save_constraints = self.ask_save()
            self.save_or_append(model_structure, file_name, save_constraints, example_name, theory_name)

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

    def save_or_append(self, model_structure, file_name, save_constraints, example_name, theory_name):
        """Option to save or append if a model is found."""
        if file_name is None:
            return
        if len(file_name) == 0:
            with open(f"{self.module.module_path}", 'a', encoding="utf-8") as f:
                print('\n"""', file=f)
                model_structure.print_to(example_name, theory_name, save_constraints, f)
                print('"""', file=f)
            print(f"\nAppended output to {self.module.module_path}")
            return

        # Default or fallback path
        project_name = getattr(self.module, 'module_name', 'project')
        destination_dir = os.path.join(os.getcwd(), project_name)
        
        # Ensure the directory exists
        os.makedirs(destination_dir, exist_ok=True)

        with open(f"{destination_dir}/{file_name}.py", 'w', encoding="utf-8") as n:
            print(f'# TITLE: {file_name}.py created in {destination_dir}\n"""', file=n)
            model_structure.save_to(example_name, theory_name, save_constraints, n)
        print(f'\n{file_name}.py created in {destination_dir}\n')

def generate_project(name, theory='template'):
    """
    Copy the 'template/' directory to the current working directory, 
    rename it to the specified 'name', and rename its modules by prefixing 'name'.
    """
    project_name = 'project_' + name
    # Dynamically resolve the source directory relative to this script
    source_dir = os.path.join(os.path.dirname(__file__), 'theory_lib', theory)  
    destination_dir = os.path.join(os.getcwd(), project_name)  

    try:
        # Check if the source directory exists
        if not os.path.exists(source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{theory}' was not found in '{source_dir}'."
            )

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
        result = input("Would you like to test the example script? (y/n): ")
        if result not in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
            # Output the test command
            print(f"\nRun the following command to test your project:\n\nmodel-checker {destination_dir}/examples.py\n")
            return
        example_script = os.path.join(destination_dir, "examples.py")
        print(example_script)
        if os.path.exists(example_script):
            print("\nRunning the example script...")
            subprocess.run(["model-checker", example_script])
        else:
            print(f"\nFailed to run: model-checker {example_script}")
    
    except FileNotFoundError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

def ask_generate_project():
    """prompt user to create a test file"""
    result = input("Would you like to generate a new project? (y/n): ")
    if result not in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
        print("You can run an example.py file that already exists with the command:\n")
        print("model-checker example.py\n")
    test_name = input("Enter the name of your project using snake_case: ")
    generate_project(test_name)

def parse_file_and_flags():
    """returns the name and path for the current script"""
    # create an ArgumentParser object
    parser = argparse.ArgumentParser(
        prog='model-checker',
        usage='%(prog)s [options] input',
        description="""
        Running '%(prog)s' without options or an input will prompt the user
        to generate a project. To run a test on an existing file, include
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
        '--non_empty',
        '-e',
        action='store_true',
        help='Overrides to make all propositions non_empty.'
    )
    parser.add_argument(
        '--load_theory',
        '-l',
        type=str,
        metavar='NAME',
        help='Load a specific theory by name.'
    )
    parser.add_argument(
        '--non_null',
        '-n',
        action='store_true',
        help='Overrides to make all propositions non_null.'
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
    parser.add_argument(
        '--print_z3',
        '-z',
        action='store_true',
        help='Overrides to print Z3 model or unsat_core.'
    )
    # parse the command-line argument to get the module path
    flags = parser.parse_args()
    package_name = parser.prog  # Get the package name from the parser
    return flags, package_name

# TODO: make method for runtime and progress bar
# TODO: make method for turning on cProfile
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
    if module_flags.load_theory:
        semantic_theory_name = module_flags.load_theory
        generate_project(semantic_theory_name, semantic_theory_name)

    module = BuildModule(module_flags)

    # TODO: check if compare = True and then:
        # check if multiple semantic_theories and then:
            # run comparison function

    for example_name, example_case in module.example_range.items():
        for theory_name, semantic_theory in module.semantic_theories.items():
            dictionary = semantic_theory.get("dictionary", None)
            if dictionary:
                example_case = translate(example_case, dictionary)
            example = BuildExample(module, semantic_theory, example_case)
            example.print_result(example_name, theory_name)

if __name__ == "__main__":
    main()
