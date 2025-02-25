import os
import importlib.util
import concurrent.futures
import time
import shutil
import subprocess

# Try local imports first (for development)
try:
    from src.model_checker import __version__
    from src.model_checker.model import (
        SemanticDefaults,
        PropositionDefaults,
        ModelConstraints,
    )
    from src.model_checker.syntactic import (
        OperatorCollection, 
        Syntax,
    )
except ImportError:
    # Fall back to installed package imports
    from model_checker import __version__
    from model_checker.model import (
        SemanticDefaults,
        PropositionDefaults,
        ModelConstraints,
    )
    from model_checker.syntactic import (
        OperatorCollection,
        Syntax,
    )


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
        "maximize": False,
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
        self.module_path = self.module_flags.file_path
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
        """Initialize all settings from module with defaults and flag overrides."""

        general_settings = getattr( # Permits user to replace general_settings
            self.module,
            "general_settings",
            self.DEFAULT_GENERAL_SETTINGS
        )

        # Initialize each setting from module_settings with fallback to defaults
        for key, default_value in self.DEFAULT_GENERAL_SETTINGS.items():
            # Check if there's a flag override
            flag_value = getattr(self.module_flags, key, None)
            if flag_value is True:  # Only override if flag is explicitly True
                value = flag_value
            else:  # Use module setting or fall back to default
                value = general_settings.get(key, default_value)
            setattr(self, key, value)
        
        # Store complete settings dict with flag overrides
        general_settings = {
            key: getattr(self, key)
            for key in self.DEFAULT_GENERAL_SETTINGS
        }

        return general_settings

    def try_single_N(self, theory_name, semantic_theory, example_case):
        """Try a single N value and return (success, runtime)"""
        premises, conclusions, settings = example_case
        semantics_class = semantic_theory["semantics"]
        model_structure_class = semantic_theory["model"]
        operators = semantic_theory["operators"]
        syntax = Syntax(premises, conclusions, operators)
        semantics = semantics_class(settings['N'])
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            semantic_theory["proposition"],
        )
        model_structure = model_structure_class(model_constraints, settings['max_time'])
        run_time = model_structure.z3_model_runtime
        success = run_time < settings['max_time']
        if success:
            print(
                f"{model_structure.semantics.name} ({theory_name}):\n"
                f"  RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {settings['N']}."
            )
        else:
            print(
                f"{model_structure.semantics.name} ({theory_name}): "
                f"TIMED OUT\n  RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {example_case[2]['N']}."
            )
        return success, run_time

    def compare_semantics(self, example_theory_tuples):
        results = []
        active_cases = {}  # Track active cases and their current N values
        
        with concurrent.futures.ProcessPoolExecutor() as executor:
            # Initialize first run for each case
            futures = {}
            all_times = []
            for case in example_theory_tuples:
                theory_name, semantic_theory, (premises, conclusions, settings) = case
                example_case = [premises, conclusions, settings.copy()]
                active_cases[theory_name] = settings['N']  # Store initial N
                all_times.append(settings['max_time'])
                new_case = (theory_name, semantic_theory, example_case)
                futures[executor.submit(self.try_single_N, *new_case)] = new_case
            max_time = max(all_times)
                
            while futures:
                done, _ = concurrent.futures.wait(
                    futures,
                    # timeout=max_time,
                    return_when=concurrent.futures.FIRST_COMPLETED
                )
                for future in done:
                    case = futures.pop(future)
                    theory_name, semantic_theory, example_case = case
                    max_time = example_case[2]['max_time']
                    
                    try:
                        success, runtime = future.result()
                        if success and runtime < max_time:
                            # Increment N and submit new case
                            example_case[2]['N'] = active_cases[theory_name] + 1
                            active_cases[theory_name] = example_case[2]['N']
                            futures[executor.submit(self.try_single_N, *case)] = case
                        else:
                            # Found max N for this case
                            results.append((theory_name, active_cases[theory_name] - 1))
                    except Exception as e:
                        print(
                            f"\nERROR: {case[1]['semantics'].__name__} " +
                            f"({case[0]}) for N = {example_case[2]['N']}."
                            f"  {str(e)}"
                        )
                        
        return results

    def translate(self, example_case, dictionary):
        """Use dictionary to replace logical operators."""
        premises, conclusions, settings = example_case
        def replace_operators(logical_list, dictionary):
            for old, new in dictionary.items():
                logical_list = [sentence.replace(old, new) for sentence in logical_list]
            return logical_list
        new_premises = replace_operators(premises, dictionary)
        new_conclusion = replace_operators(conclusions, dictionary)
        return [new_premises, new_conclusion, settings]

    def translate_example(self, example_case, semantic_theories):
        example_theory_tuples = []
        for theory_name, semantic_theory in semantic_theories.items():
            translated_case = example_case
            dictionary = semantic_theory.get("dictionary", None)
            if dictionary:
                translated_case = self.translate(example_case.copy(), dictionary)
            example_tuple = (theory_name, semantic_theory, translated_case)
            example_theory_tuples.append(example_tuple)
        return example_theory_tuples

    def run_comparison(self):
        print()
        for example_name, example_case in self.example_range.items():
            premises, conclusions, settings = example_case
            print(f"{'='*40}\n")
            print(f"EXAMPLE = {example_name}")
            print(f"  Premises:")
            for prem in premises:
                print(f"    {prem}")
            print(f"  Conclusions:")
            for con in conclusions:
                print(f"    {con}")
            print()
            example_theory_tuples = self.translate_example(example_case, self.semantic_theories)
            self.compare_semantics(example_theory_tuples)
            print(f"\n{'='*40}")

    def run_examples(self):
        for example_name, example_case in self.example_range.items():
            for theory_name, semantic_theory in self.semantic_theories.items():
                dictionary = semantic_theory.get("dictionary", None)
                if dictionary:
                    example_case = self.translate(example_case, dictionary)
                example_max_time = example_case[2]["max_time"]

                from concurrent.futures import ThreadPoolExecutor, TimeoutError

                with ThreadPoolExecutor() as executor:
                    # Submit the build task
                    future = executor.submit(
                        BuildExample,
                        self,
                        semantic_theory,
                        example_case,
                        semantic_theory["model"]
                    )
                    
                    # Create and update progress indicator
                    print("Running model-checker: ", end="", flush=True)
                    start_time = time.time()
                    progress_chars = ["-", "\\", "|", "/"]
                    i = 0
                    while not future.done() and (time.time() - start_time) < example_max_time:
                        print(f"\rRunning model-checker: {progress_chars[i]}", end="", flush=True)
                        i = (i + 1) % len(progress_chars)
                        time.sleep(0.1)
                    print("\rRunning model-checker: Done" + " " * 10 + "\n")
                    
                    try:
                        example = future.result(timeout=0)  # Get result if ready
                        if example is not None:
                            example.print_result(example_name, theory_name)
                    except TimeoutError:
                        print(f"\nExample '{example_name}' timed out after {example_max_time} seconds")


class BuildProject:
    """Handles project generation and setup."""

    DEFAULT_FILES = {
        "examples.py": "examples.py",
        "operators.py": "operators.py",
        "semantics.py": "semantics.py",
    }

    def __init__(self, theory: str = 'default'):
        """Initialize project builder with specified theory."""
        self.theory = theory
        self.source_dir = os.path.join(os.path.dirname(__file__), 'theory_lib', theory)
        self.project_name: str = ""
        self.destination_dir: str = ""

    def ask_generate(self):
        """Prompt user to create a test file."""
        result = input(f"Would you like to generate a new {self.theory}-project? (y/n): ")
        if result not in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
            print("\nYou can run an example.py file that already exists with the command:\n")
            print("  $ model-checker example.py\n")
            return
        
        test_name = input("Enter the name of your project using snake_case: ")
        self.generate(test_name)

    def generate(self, name):
        """
        Generate a new project by copying template files and setting up structure.
        
        Args:
            name: Base name for the project (will be prefixed with 'project_')
        """
        self.project_name = 'project_' + name
        if not self.project_name:
            raise ValueError("Project name must be set before generating destination directory")
        self.destination_dir = os.path.join(os.getcwd(), self.project_name)

        try:
            self._validate_paths()
            self._copy_project_files()
            self._rename_files()
            self._print_success_message()
            self._handle_example_script()

        except FileNotFoundError as e:
            print(f"Error: {e}")
        except Exception as e:
            print(f"An unexpected error occurred: {e}")

    def _validate_paths(self):
        """Validate source and destination paths."""
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{self.theory}' was not found in '{self.source_dir}'."
            )

        if os.path.exists(self.destination_dir):
            raise FileExistsError(f"Directory '{self.destination_dir}' already exists.")

    def _copy_project_files(self):
        """Copy template files to new project directory."""
        shutil.copytree(self.source_dir, self.destination_dir)

    def _rename_files(self):
        """Rename project files according to template."""
        for old_name, new_name in self.DEFAULT_FILES.items():
            old_path = os.path.join(self.destination_dir, old_name)
            new_path = os.path.join(self.destination_dir, new_name)
            if os.path.exists(old_path):
                os.rename(old_path, new_path)

    def _print_success_message(self):
        """Print success message with created files."""
        print(f"\nProject generated at: {self.destination_dir}\n")
        print("The following modules were created:")
        for _, new_name in self.DEFAULT_FILES.items():
            print(f"  {new_name}")

    def _handle_example_script(self):
        """Handle running the example script if requested."""
        result = input("Would you like to test the example script? (y/n): ")
        if result not in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
            print(f"\nRun the following command to test your project:\n\nmodel-checker {self.destination_dir}/examples.py\n")
            return

        example_script = os.path.join(self.destination_dir, "examples.py")
        print(example_script)
        if os.path.exists(example_script):
            print("\nRunning the example script...")
            subprocess.run(["model-checker", example_script])
        else:
            print(f"\nFailed to run: model-checker {example_script}")


class BuildExample:
    """Class to create and store model structure with settings as attributes."""

    def __init__(self, build_module, semantic_theory, example_case, model_structure_class):
        """Initialize model structure from module flags."""
        self.module = build_module.module
        self.module_flags = build_module.module_flags
        self.semantics, self.proposition, self.operators, self.dictionary = self._validate_semantic_theory(semantic_theory)
        self.premises, self.conclusions, self.example_settings = self._validate_example(example_case)
        self.settings = self._validate_settings(self.example_settings)
        self.example_syntax = Syntax(self.premises, self.conclusions, self.operators)

        # Create model constraints
        self.model_constraints = ModelConstraints(
            self.settings,
            self.example_syntax,
            # TODO: replace with parameters dictionary
            self.semantics(self.settings),
            self.proposition,
        )

        # Create model structure with max_time from settings
        self.model_structure = model_structure_class(
            self.model_constraints,
            self.settings
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

        def update_example_settings(example_settings):
            default_example_settings = self.semantics.DEFAULT_EXAMPLE_SETTINGS
            for key, value in example_settings.items():
                default_example_settings[key] = value
            return default_example_settings

        # TODO: right now the merged settings gets carried over from one example
        # to the next which is not how it should be
        def merge_settings(example_settings, general_settings):
            """Adds example_settings to general_settings, mentioning overlaps."""
            # Track and merge settings

            combined_settings = general_settings
            for key, example_value in example_settings.items():
                # Get value from module settings or use default
                general_value = combined_settings.get(key, example_value)
                
                # Check if we're replacing an existing general setting
                if key in general_settings.keys() and example_value != general_value:
                    print(
                        f"Warning: Example setting '{key} = {example_value}' is " +
                        f"replacing the general setting '{key} = {general_value}'."
                    )
                
                # Update the settings
                combined_settings[key] = example_value
    
            return combined_settings
    
        def disjoin_flags(all_settings):
            """Override settings with command line flag values.
            
            Takes the merged settings dictionary and updates any boolean settings
            that have corresponding command line flags set to True. Only updates
            settings that already exist in the settings dictionary.

            Args:
                all_settings: Dictionary containing the merged general and example settings

            Returns:
                Dictionary with settings updated based on command line flag values
            """
            module_flags = self.module_flags
            updated_settings = all_settings.copy()
            # Check each command line flag
            for key, value in vars(module_flags).items():
                # Only override if flag is boolean, True, and setting exists
                if isinstance(value, bool) and value and key in updated_settings:
                    updated_settings[key] = value
            return updated_settings
    
        # Merge and update settings
        updated_example_settings = update_example_settings(example_settings)
        all_settings = merge_settings(updated_example_settings, self.module.general_settings)
        flag_updated_settings = disjoin_flags(all_settings)
    
        return flag_updated_settings

    def check_result(self):
        model_expectation = self.settings["model"]
        model_findings = self.model_structure.z3_model_status
        return model_findings == model_expectation

    def print_result(self, example_name, theory_name):
        """Prints resulting model or no model if none is found."""
        model_structure = self.model_structure
        default_settings = self.example_settings
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




# TODO: combine with run_comparison once moved into print class
# def save_comparisons(default_theory, imposition_theory, settings, examples):
#     # Get the absolute path of the current script
#     script_path = os.path.realpath(__file__)
#     script_dir = os.path.dirname(script_path)
#     # Define subdirectory path relative to the script's directory
#     new_dir = os.path.join(script_dir, "comparisons")
#     # Create the "Examples" directory if it doesn't exist
#     os.makedirs(new_dir, exist_ok=True)
#     # Prompt the user for a filename
#     filename = input("Please enter the output filename (without path): ")
#     filepath = os.path.join(new_dir, filename)
#
#     # Open the file for writing and redirect stdout
#     with open(filepath, 'w') as f:
#         old_stdout = sys.stdout
#         sys.stdout = f
#         try:
#             run_comparison(default_theory, imposition_theory, settings, examples)
#         finally:
#             # Restore original stdout
#             sys.stdout = old_stdout
#
#     print(f"All output has been written to {filename}.")

