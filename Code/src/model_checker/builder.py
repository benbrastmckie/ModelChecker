"""Model checker builder module for constructing and executing modal logic examples.

This module provides the core functionality for building and executing modal logic model
checking examples. It contains three main classes:

BuildModule:
    Manages loading and executing model checking examples from Python modules. Handles
    dynamic module loading, configuration settings, and coordinating the model checking
    process across different semantic theories.

BuildProject:
    Creates new theory implementation projects from templates. Handles directory
    structure creation, file copying, and initial setup of new modal logic theory
    implementations.

BuildExample:
    Handles individual model checking examples, including model construction,
    constraint generation, and result evaluation. Manages the interaction between
    syntactic representations and semantic theories.

The module supports:
- Dynamic loading of Python modules containing modal logic examples
- Comparison of different semantic theories on the same logical problems
- Creation of new theory implementation projects from templates
- Model finding with configurable settings and constraints
- Result visualization and saving
- Operator translation between different notational systems

Example usage:
    # Load and run examples from a module
    module = BuildModule(module_flags)
    module.run_examples()

    # Create a new theory project
    project = BuildProject("theory_name")
    project.generate("project_name")

    # Build and evaluate a specific example
    example = BuildExample(build_module, semantic_theory, example_case)
    example.print_result("example_name", "theory_name")
"""

import z3
import os
import importlib.util
import concurrent.futures
import time
import shutil
import subprocess
from concurrent.futures.thread import ThreadPoolExecutor

# Standard imports
from model_checker import __version__
from model_checker.model import (
    SemanticDefaults,
    PropositionDefaults,
    ModelConstraints,
    ModelDefaults,
)
from model_checker.syntactic import (
    OperatorCollection,
    Syntax,
)


class BuildModule:
    """Manages loading and executing model checking examples from Python modules.
    
    This class is responsible for dynamically loading a Python module containing modal logic
    examples, extracting configuration settings, and coordinating the model checking process.
    It provides functionality for running examples with different logical theories, comparing
    performance across semantic implementations, and translating between different notations.
    
    The class supports both single example processing and comparative analysis of multiple
    semantic theories on the same logical problems.
    
    Attributes:
        module_flags: Command-line flags that override module settings
        module_path (str): File path to the Python module being loaded
        module_name (str): Name of the module (without extension)
        module: The loaded Python module object
        semantic_theories (dict): Mapping of theory names to their implementations
        example_range (dict): Mapping of example names to their definitions
        general_settings (dict): General configuration settings for model checking
        print_impossible (bool): Whether to print models that are impossible
        print_constraints (bool): Whether to print Z3 constraints
        print_z3 (bool): Whether to print raw Z3 output
        save_output (bool): Whether to save results to files
        maximize (bool): Whether to maximize the model size
    """

    def __init__(self, module_flags):
        """Initialize BuildModule with module flags containing configuration.
        
        Args:
            module_flags: Object containing configuration flags including file_path
                          and other optional settings that override module settings
        
        Raises:
            ImportError: If the module cannot be loaded
            AttributeError: If required attributes are missing from the module
        """
        # Import here to avoid circular imports
        from model_checker.settings import SettingsManager, DEFAULT_GENERAL_SETTINGS

        self.module_flags = module_flags
        self.module_path = self.module_flags.file_path
        self.module_name = os.path.splitext(os.path.basename(self.module_path))[0]
        self.module = self._load_module()
        
        # Load core attributes
        self.semantic_theories = self._load_attribute("semantic_theories")
        self.example_range = self._load_attribute("example_range")

        # Initialize settings manager with first semantic theory (can be updated per theory later)
        first_theory = next(iter(self.semantic_theories.values()))
        self.settings_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
        
        # Load general settings
        user_general_settings = getattr(self.module, "general_settings", None)
        self.general_settings = self.settings_manager.validate_general_settings(user_general_settings)
        
        # Apply flag overrides for general settings
        self.general_settings = self.settings_manager.apply_flag_overrides(self.general_settings, self.module_flags)
        
        # Also set attributes for backward compatibility
        for key, value in self.general_settings.items():
            setattr(self, key, value)

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


    def try_single_N(self, theory_name, semantic_theory, example_case):
        """Try a single N value and return (success, runtime).
        
        Attempts to find a model with a specific N value (number of worlds) for a given
        semantic theory and example case. Times out after the maximum allowed time.
        
        Args:
            theory_name (str): Name of the semantic theory being tested
            semantic_theory (dict): Dictionary containing the semantic theory implementation
            example_case (list): List containing [premises, conclusions, settings]
            
        Returns:
            tuple: (success, runtime) where:
                - success (bool): True if model found within max time, False otherwise
                - runtime (float): Time taken to attempt finding the model
                
        The method prints progress information including theory name, runtime, max time
        allowed, and N value used. If the attempt times out, it prints a timeout message.
        """
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
        """Compare different semantic theories by finding maximum model sizes.
        
        This method attempts to find the maximum model size (N) for each semantic theory
        by incrementally testing larger values of N until a timeout occurs. It runs the
        tests concurrently using a ProcessPoolExecutor for better performance.
        
        Args:
            example_theory_tuples: List of tuples containing (theory_name, semantic_theory, example_case)
                where example_case is [premises, conclusions, settings]
                
        Returns:
            list: List of tuples containing (theory_name, max_N) where max_N is the largest
                  number of worlds for which a model was found within the time limit
                  
        The method prints progress information for each attempt, including:
        - Theory name and implementation
        - Runtime and maximum allowed time
        - Current N value being tested
        - Timeout notifications when applicable
        """
        results = []
        active_cases = {}  # Track active cases and their current N values
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
        """Use dictionary to replace logical operators in logical formulas.
        
        Takes a dictionary mapping old operators to new operators and replaces all
        occurrences of old operators with their new versions in the premises and
        conclusions.
        
        Args:
            example_case (list): A list containing [premises, conclusions, settings]
            dictionary (dict): Mapping of old operators to new operators
            
        Returns:
            list: New example case with translated operators in premises and conclusions
            
        Example:
            >>> example_case = [["\\nec p"], ["\\pos p"], {"N": 3}]
            >>> dictionary = {"\\nec": "\\Box", "\\pos": "\\Diamond"} 
            >>> translate(example_case, dictionary)
            [["\\Box p"], ["\\Diamond p"], {"N": 3}]
        """
        premises, conclusions, settings = example_case
        def replace_operators(logical_list, dictionary):
            for old, new in dictionary.items():
                logical_list = [sentence.replace(old, new) for sentence in logical_list]
            return logical_list
        new_premises = replace_operators(premises, dictionary)
        new_conclusion = replace_operators(conclusions, dictionary)
        return [new_premises, new_conclusion, settings]

    def translate_example(self, example_case, semantic_theories):
        """Translates example case for each semantic theory using their dictionaries.

        Takes an example case and applies any operator translations defined in each semantic
        theory's dictionary to create theory-specific versions of the example.

        Args:
            example_case (list): List containing [premises, conclusions, settings]
            semantic_theories (dict): Dictionary mapping theory names to their implementations

        Returns:
            list: List of tuples (theory_name, semantic_theory, translated_case) where:
                - theory_name (str): Name of the semantic theory
                - semantic_theory (dict): The semantic theory implementation
                - translated_case (list): Example case with operators translated for that theory

        Example:
            >>> example_case = [["\\nec p"], ["\\pos p"], {"N": 3}]
            >>> semantic_theories = {
            ...     "S4": {"dictionary": {"\\nec": "\\Box", "\\pos": "\\Diamond"}, ...},
            ...     "S5": {"dictionary": {"\\nec": "□", "\\pos": "◇"}, ...}
            ... }
            >>> translate_example(example_case, semantic_theories)
            [
                ("S4", s4_theory, [["\\Box p"], ["\\Diamond p"], {"N": 3}]),
                ("S5", s5_theory, [["□ p"], ["◇ p"], {"N": 3}])
            ]
        """
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
        """Compare different semantic theories by running examples and printing results.
        
        Iterates through each example in example_range and runs it against all semantic theories.
        For each example:
        1. Prints example name and details (premises and conclusions)
        2. Translates operators according to each theory's dictionary
        3. Compares semantic theories by finding maximum model sizes
        4. Prints results showing which theories could handle larger models
        
        The comparison helps evaluate the relative efficiency and capabilities of different
        semantic theories when applied to the same examples
        """

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

    class ProgressSpinner:
        """Displays an animated progress spinner while a task runs."""
        
        def __init__(self):
            self.progress_chars = ["-", "\\", "|", "/"]
            self.current = 0
            
        def update(self):
            """Update and display the next spinner character."""
            print(f"\rRunning model-checker: {self.progress_chars[self.current]}", 
                  end="", flush=True)
            self.current = (self.current + 1) % len(self.progress_chars)
            
        def complete(self):
            """Display completion message."""
            print("\r" + " " * 30 + "\r", end="", flush=True)

    def run_single_iteration(self, executor, example_case, example_name, theory_name, semantic_theory):
        """Run a single iteration of the model checker with progress tracking.

        Executes one iteration of the model checker while displaying an animated progress
        spinner. Handles timeouts and result processing.

        Args:
            executor: ThreadPoolExecutor instance for running the model checker
            example_case: List containing [premises, conclusions, settings]
            example_name: Name of the example being processed
            theory_name: Name of the semantic theory being used
            semantic_theory: Dictionary containing the semantic theory implementation

        Returns:
            BuildExample: The processed example object if successful, None if failed or timed out

        The method:
        1. Submits the model checking task to the executor
        2. Displays an animated progress spinner while waiting
        3. Handles timeouts based on example settings
        4. Processes and prints results if successful
        """
        future = executor.submit(
            BuildExample,
            self,
            semantic_theory,
            example_case
        )
        
        spinner = self.ProgressSpinner()
        start_time = time.time()
        example_max_time = example_case[2]["max_time"]
        
        while not future.done() and (time.time() - start_time) < example_max_time:
            spinner.update()
            time.sleep(0.1)
            
        spinner.complete()
        
        # try:
        example = future.result(timeout=example_max_time)  # Use the example's max_time instead of 0
        if example is None:
            return None
            
        example.print_result(example_name, theory_name)
        return example
            
        # except TimeoutError:
        #     print(f"\nExample '{example_name}' timed out after {example_max_time} seconds")
        #     return None
        # except Exception as e:
        #     print(f"\nError running example '{example_name}': {str(e)}")
        #     return None

    def process_example(self, example_name, example_case, theory_name, semantic_theory):
        """Process a single example with the given semantic theory.
        
        Args:
            example_name (str): Name of the example being processed
            example_case (list): List containing [premises, conclusions, settings]
            theory_name (str): Name of the semantic theory being used
            semantic_theory (dict): Dictionary containing semantic theory configuration
            
        Returns:
            BuildExample: The processed example object, or None if processing failed
            
        This method handles:
        1. Operator translation if needed
        2. Creating a theory-specific SettingsManager
        3. Initial model generation
        4. Iterative model finding if requested
        """
        # TODO: add try/except back in
        # try:
        # Import settings manager for this specific theory
        from model_checker.settings import SettingsManager, DEFAULT_GENERAL_SETTINGS
        
        # Create a theory-specific settings manager
        theory_settings_manager = SettingsManager(
            {"semantics": semantic_theory["semantics"]},
            DEFAULT_GENERAL_SETTINGS
        )
        
        # Translate operators if dictionary exists
        translated_case = self._translate_if_needed(example_case, semantic_theory)
        premises, conclusions, example_settings = translated_case
        
        # Generate initial model
        with ThreadPoolExecutor() as executor:
            example = self.run_single_iteration(
                executor, translated_case, example_name, theory_name, semantic_theory
            )
            
            if not example:
                return None
                
            # # TODO: if keep, remove process_iterations from example for-loop
            # # Handle iteration if requested
            # if example.settings.get("iterate", 0) > 1:
            #     # example_copy = list(example_case)
            #     # example_copy[2] = example_case[2].copy()
            #     example = self.process_iterations(example_name, example_case, theory_name, semantic_theory)
            #     # example = self.process_iterations(
            #     #     example, translated_case, example_name, theory_name
            #     # )
                
            return example
                
        # except Exception as e:
        #     print(f"\nError processing example '{example_name}': {str(e)}")
        #     return None
            
    def _translate_if_needed(self, example_case, semantic_theory):
        """Translate operators if a dictionary is provided in the semantic theory.
        
        Args:
            example_case (list): Original example case
            semantic_theory (dict): Semantic theory configuration
            
        Returns:
            list: Translated example case, or original if no translation needed
        """
        if semantic_theory.get("dictionary"):
            return self.translate(example_case.copy(), semantic_theory["dictionary"])
        return example_case
        
    def process_iterations(self, example_name, example_case, theory_name, semantic_theory):
        """Process multiple iterations of model checking for a given example.
        
        This method attempts to find multiple models for the given example by
        iteratively solving and then adding constraints to find distinct models.
        
        Args:
            example_name (str): Name of the example being processed
            example_case (list): The example case containing [premises, conclusions, settings]
            theory_name (str): Name of the semantic theory being used
            semantic_theory (dict): Dictionary containing the semantic theory implementation
        
        Returns:
            None: Results are printed to standard output
        """
        """Process additional model iterations if requested.
        
        Args:
            example (BuildExample): Current example being processed
            example_case (list): Current example case
            example_name (str): Name of the example
            theory_name (str): Name of the semantic theory
            
        Returns:
            BuildExample: The final example after all iterations
        """
        try:
            example = BuildExample(self, semantic_theory, example_case)
            example_max_time = example_case[2]["max_time"]
            
            # Print initial model
            if example.model_structure.z3_model is not None:
                example.print_result(example_name, theory_name)
            
            while example.settings["iterate"] > 1:
                # Update settings for next iteration
                example.settings["iterate"] -= 1
                
                # Find next model
                old_z3_model = example.model_structure.z3_model
                if old_z3_model is None:
                    print("\nNo valid model to iterate from.")
                    break
                    
                found_model = example.find_next_model(old_z3_model)
                
                # Check if we found another model
                if not found_model or example.model_structure.z3_model_status is False:
                    print("\nNo more models found.")
                    break
                    
                if example.model_structure.z3_model is None:
                    print("\nFailed to find next model.")
                    break
                    
                example.print_result(example_name, theory_name)
                
            return example
            
        except Exception as e:
            print(f"\nError processing iterations for example '{example_name}': {str(e)}")
            return None

    def run_examples(self):
        """Process and execute each example case with all semantic theories.
        
        Iterates through example cases and theories, translating operators if needed.
        Runs model checking with progress indicator and timeout handling.
        Prints results or timeout message for each example/theory combination.
        """
        for example_name, example_case in self.example_range.items():
            for theory_name, semantic_theory in self.semantic_theories.items():
                # Make setting reset for each semantic_theory
                example_copy = list(example_case)
                example_copy[2] = example_case[2].copy()
                iterate = example_copy[2].get("iterate", 0)
                if iterate is not None and iterate > 1:
                    self.process_iterations(example_name, example_copy, theory_name, semantic_theory)
                else:
                    self.process_example(example_name, example_copy, theory_name, semantic_theory)

class BuildProject:
    """Creates a new theory implementation project from a template.
    
    This class handles the creation of a new modal logic theory implementation
    by copying and configuring template files. It sets up the directory structure
    and initializes the basic implementation files.
    
    The generated project includes necessary files from the source theory,
    such as operators.py, semantic.py, examples.py, and README.md, providing
    the foundation for implementing a new modal logic theory.
    
    Attributes:
        theory (str): Name of the source theory to use as template
        source_dir (str): Directory path to the source theory
        project_name (str): Name of the new project (will be prefixed with 'project_')
        destination_dir (str): Directory path for the new project
        log_messages (list): Log of actions and messages during project generation
    """

    # Essential files that should be present in a valid theory
    ESSENTIAL_FILES = [
        "README.md",
        "__init__.py"
    ]
    
    # Core files that will be highlighted in the success message
    CORE_FILES = [
        "examples.py",
        "operators.py",
        "semantic.py",
        "README.md"
    ]

    def __init__(self, theory: str = 'default'):
        """Initialize project builder with specified theory."""
        self.theory = theory
        self.source_dir = os.path.join(os.path.dirname(__file__), 'theory_lib', theory)
        self.project_name: str = ""
        self.destination_dir: str = ""
        self.log_messages = []

    def log(self, message, level="INFO"):
        """Log a message with a specified level.
        
        Args:
            message (str): The message to log
            level (str): The log level (INFO, WARNING, ERROR)
        """
        self.log_messages.append(f"[{level}] {message}")
        if level == "ERROR":
            print(f"Error: {message}")
        elif level == "WARNING":
            print(f"Warning: {message}")
        else:
            print(message)

    def ask_generate(self):
        """Prompt user to create a new theory implementation project.
        
        Asks the user if they want to generate a new project for the current theory.
        If yes, prompts for a project name and calls generate(). If no, displays
        information about running existing example files.
        
        The method handles:
        - User confirmation for project creation
        - Project name input validation 
        - Fallback instructions for using existing examples
        """
        result = input(f"Would you like to generate a new {self.theory}-project? (y/n): ")
        if result not in {'Yes', 'yes', 'Ye', 'ye', 'Y', 'y'}:
            print("\nYou can run an example.py file that already exists with the command:\n")
            print("  $ model-checker example.py\n")
            return
        
        test_name = input("Enter the name of your project using snake_case: ")
        self.generate(test_name)

    
    def generate(self, name):
        """Generate a new theory implementation project from templates.
        
        Creates a new project directory with the standard theory implementation structure
        by copying all files from the source theory. The project name will be prefixed
        with 'project_' to maintain consistent naming conventions.
        
        Args:
            name (str): Base name for the project, should use snake_case formatting
            
        Raises:
            ValueError: If project name is empty or invalid
            FileExistsError: If project directory already exists
            FileNotFoundError: If source theory cannot be found
        """
        self.project_name = 'project_' + name
        if not self.project_name:
            raise ValueError("Project name must be set before generating destination directory")
        self.destination_dir = os.path.join(os.getcwd(), self.project_name)

        try:
            self._validate_source_directory()
            self._create_destination_directory()
            self._copy_files()
            self._update_init_file()
            self._validate_essential_files()
            self._print_success_message()
            self._handle_example_script()

        except Exception as e:
            print(f"An error occurred: {e}")

    def _validate_source_directory(self):
        """Verify the source directory exists and contains necessary files."""
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{self.theory}' was not found in '{self.source_dir}'."
            )
            
        # Check for essential files
        missing_files = []
        for file in self.ESSENTIAL_FILES:
            file_path = os.path.join(self.source_dir, file)
            if not os.path.exists(file_path):
                missing_files.append(file)
                
        if missing_files:
            self.log(f"Missing essential files in source directory: {', '.join(missing_files)}", "WARNING")

    def _create_destination_directory(self):
        """Create the destination directory if it doesn't exist."""
        if os.path.exists(self.destination_dir):
            raise FileExistsError(f"Directory '{self.destination_dir}' already exists.")
        os.makedirs(self.destination_dir)

    def _copy_files(self):
        """Copy all files from source to destination directory."""
        # Directories to ignore
        ignore_dirs = ['__pycache__', '.ipynb_checkpoints']
        
        # Copy all files from source to destination
        for item in os.listdir(self.source_dir):
            # Skip __pycache__ and other ignored directories
            if item in ignore_dirs:
                continue
                
            source_item = os.path.join(self.source_dir, item)
            dest_item = os.path.join(self.destination_dir, item)
            
            try:
                if os.path.isdir(source_item):
                    # Copy directories recursively, but ignore __pycache__ and .ipynb_checkpoints
                    shutil.copytree(
                        source_item, 
                        dest_item,
                        ignore=shutil.ignore_patterns(*ignore_dirs)
                    )
                    self.log(f"Copied directory: {item}")
                else:
                    # Copy files
                    shutil.copy2(source_item, dest_item)
                    self.log(f"Copied file: {item}")
            except Exception as e:
                self.log(f"Error copying {item}: {str(e)}", "ERROR")

    def _update_init_file(self):
        """Update the __init__.py file with the current version."""
        init_path = os.path.join(self.destination_dir, "__init__.py")
        if os.path.exists(init_path):
            with open(init_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Find version from pyproject.toml or use default
            current_version = self._get_current_version()
            
            # Replace version in __init__.py
            new_content = content.replace("unknown", current_version)
            
            with open(init_path, 'w', encoding='utf-8') as f:
                f.write(new_content)

    def _get_current_version(self):
        """Extract the current version from pyproject.toml."""
        try:
            current_dir = os.path.dirname(__file__)
            while current_dir != '/':
                pyproject_path = os.path.join(current_dir, 'pyproject.toml')
                if os.path.exists(pyproject_path):
                    with open(pyproject_path, 'r', encoding='utf-8') as f:
                        pyproject_content = f.read()
                        # Extract version using basic string operations
                        version_line = [line for line in pyproject_content.split('\n') 
                                     if line.strip().startswith('version = ')][0]
                        return version_line.split('=')[1].strip().strip('"\'')
                current_dir = os.path.dirname(current_dir)
            return "0.8.18"  # Fallback version
        except Exception as e:
            self.log(f"Could not determine current version: {e}", "WARNING")
            return "0.8.18"  # Fallback version

    def _validate_essential_files(self):
        """Verify all essential files were copied to the destination."""
        missing_files = []
        for file in self.ESSENTIAL_FILES:
            file_path = os.path.join(self.destination_dir, file)
            source_path = os.path.join(self.source_dir, file)
            
            # If file exists in source but not in destination, try to copy it again
            if os.path.exists(source_path) and not os.path.exists(file_path):
                try:
                    # Try direct binary copy as a backup method
                    with open(source_path, 'rb') as src, open(file_path, 'wb') as dst:
                        dst.write(src.read())
                except Exception:
                    missing_files.append(file)
            elif not os.path.exists(file_path):
                missing_files.append(file)
                
        if missing_files:
            self.log(f"Missing essential files in generated project: {', '.join(missing_files)}", "ERROR")

    def _print_success_message(self):
        """Print success message with created files."""
        print(f"\nProject generated at: {self.destination_dir}\n")
        print("The following modules were created:")
        
        # List core files that were actually copied
        for file in sorted(os.listdir(self.destination_dir)):
            # Show all .py files and README.md
            if file.endswith(".py") or file == "README.md":
                print(f"  {file}")

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
            try:
                # Use sys.executable to ensure we use the correct Python interpreter
                import sys
                subprocess.run(["model-checker", example_script], 
                             check=True,
                             timeout=30)  # Add 30 second timeout
            except subprocess.TimeoutExpired:
                print("\nScript execution timed out. You can run it manually with:")
                print(f"model-checker {example_script}")
            except subprocess.CalledProcessError as e:
                print(f"\nError running example script: {e}")
                print(f"You can run it manually with: model-checker {example_script}")
            except Exception as e:
                print(f"\nUnexpected error: {e}")
                print(f"You can run it manually with: model-checker {example_script}")
        else:
            print(f"\nFailed to run: model-checker {example_script}")


class BuildExample:
    """Handles the creation and evaluation of a single model checking example.
    
    This class takes a semantic theory and an example case (premises, conclusions, and settings),
    constructs a logical model, and evaluates the validity of the argument. It provides methods
    for finding models, printing results, and saving the model to a file.
    
    The class integrates the syntactic representation of sentences with the semantic theory
    to create constraints that Z3 can solve, producing a model or countermodel for the argument.
    
    Attributes:
        build_module (BuildModule): The parent module managing the model checking process
        semantic_theory (dict): The semantic theory implementation to use
        example_case (list): The example case containing premises, conclusions, and settings
        semantics_class: The class implementing the semantic theory
        model_class: The class implementing the model structure
        proposition_class: The class implementing propositions
        operators (OperatorCollection): The collection of logical operators
        premises (list): The premise sentences
        conclusions (list): The conclusion sentences
        settings (dict): Configuration settings for the model
        model_structure: The resulting model structure after solving
    """

    def __init__(self, build_module, semantic_theory, example_case):
        """Initialize model structure from module flags."""
        from model_checker.settings import SettingsManager
        
        # Store from build_module
        self.module = build_module.module
        self.module_flags = build_module.module_flags

        # Unpack and store semantic_theory
        self.semantics = None
        self.proposition = None
        self.operators = None
        self.dictionary = None
        self.model_structure_class = None
        self._validate_semantic_theory(semantic_theory)
        
        # Create settings manager specifically for this theory
        self.settings_manager = SettingsManager(
            {"semantics": self.semantics},
            build_module.general_settings  # Use module's settings as fallback
        )

        # Unpack and store example_case
        self.premises, self.conclusions, self.example_settings = self._validate_example(example_case)
        self.example_syntax = Syntax(self.premises, self.conclusions, self.operators)
        
        # Get complete settings using the settings manager
        self.settings = self.settings_manager.get_complete_settings(
            build_module.general_settings,
            self.example_settings,
            self.module_flags
        )
        
        # Create model constraints
        if self.semantics is None:
            raise AttributeError(f"Semantics is None in BuildExample.")
        self.model_constraints = ModelConstraints(
            self.settings,
            self.example_syntax,
            # TODO: replace with parameters dictionary
            self.semantics(self.settings),
            self.proposition,
        )

        # Create model structure with max_time from settings
        if self.model_structure_class is None:
            raise AttributeError(f"The model_structure_class is None in BuildExample.")
        self.model_structure = self.model_structure_class(
            self.model_constraints,
            self.settings,
        )
        sentence_objects = self.model_structure.premises + self.model_structure.conclusions
        self.model_structure.interpret(sentence_objects)
        self.solver = self.model_structure.solver

    def find_next_model(self, old_z3_model):
        """Find a new model that differs from the previous one.
        
        Attempts to find a new model that is semantically distinct from the provided previous
        model by adding constraints that require at least one difference in either:
        - Sentence letter valuations
        - Primitive function/relation interpretations
        
        Args:
            old_z3_model: The previous Z3 model to differentiate from
            
        Returns:
            bool: True if a new distinct model was found, False otherwise
            
        Note:
            The method focuses on semantic differences rather than just structural ones,
            meaning the new model must interpret some component differently rather than
            just having different internal representation.
        """
        if old_z3_model is None:
            print("Warning: No previous model provided to find_next_model")
            return False

        try:
            # Update the solver by ruling out the old_z3_model
            self._update_solver(old_z3_model)
            
            # Try to find a new model
            new_result = self.model_structure.re_solve()
            if new_result is None:
                print("Warning: re_solve() returned None")
                return False
                
            # Process the results
            try:
                self.model_structure._process_solver_results(new_result)
            except Exception as e:
                print(f"Error processing solver results: {e}")
                return False
            
            # Check if we found a valid new model
            if not self.model_structure.z3_model_status:
                print("Warning: Model status is False")
                return False
                
            if self.model_structure.z3_model is None:
                print("Warning: Z3 model is None")
                return False
                
            try:
                self.model_structure._update_model_structure(
                    self.model_structure.z3_model
                )
                return True
            except z3.Z3Exception as e:
                print(f"Warning: Failed to update model structure: {e}")
                print("Current model state:")
                print(f"  Model status: {self.model_structure.z3_model_status}")
                print(f"  Model type: {type(self.model_structure.z3_model)}")
                return False
            
        except z3.Z3Exception as e:
            print(f"Warning: Z3 exception in find_next_model: {e}")
            return False
        except Exception as e:
            print(f"Error in find_next_model: {str(e)}")
            print(f"Error type: {type(e)}")
            import traceback
            print(f"Traceback:\n{traceback.format_exc()}")
            return False

    def _update_solver(self, old_z3_model):
        """Add constraints to ensure the next model differs from the previous one.
        
        Adds Z3 constraints that require the new model to differ from the previous model
        in at least one of:
        - The valuation of sentence letters
        - The interpretation of primitive functions/relations
        
        Other aspects of the model structure (e.g., accessibility relations) are not
        constrained and may remain the same or change freely.
        
        Args:
            old_z3_model: The previous Z3 model to differentiate from
            
        Raises:
            z3.Z3Exception: If constraint creation fails
        """
        try:
            solver = self.model_structure.solver
            different_model_constraints = []
            
            # Process sentence letters
            for letter in self.model_constraints.sentence_letters:
                if not isinstance(letter, z3.ExprRef):
                    continue
                try:
                    old_value = old_z3_model.eval(letter, model_completion=True)
                    if old_value is not None:
                        # Create proper Z3 comparison
                        different_model_constraints.append(letter != old_value)
                except z3.Z3Exception as e:
                    print(f"Warning: Failed to evaluate letter {letter}: {e}")
                    continue

            # Process primitive functions
            semantics_dict = getattr(self.model_constraints.semantics, '__dict__', {})
            for name, func in semantics_dict.items():
                # Skip non-Z3 items and internal attributes
                if name.startswith('_') or not isinstance(func, z3.FuncDeclRef):
                    print(f"EXCLUDED: {name} TYPE: {type(func)}")
                    continue
                    
                print(f"KEPT: {name} TYPE: {type(func)}")
                try:
                    if isinstance(func, z3.FuncDeclRef):
                        # For function declarations, we need to create differences in their interpretations
                        arity = func.arity()
                        if arity > 0:
                            # For functions with arguments, create existential constraint
                            # that requires some input to produce a different output
                            args = [z3.Int(f'arg_{i}') for i in range(arity)]
                            func_app = func(*args)
                            # Create constraint requiring some input to give different output
                            different_model_constraints.append(
                                z3.Exists(args, func_app != old_z3_model.eval(func_app, model_completion=True))
                            )
                    # elif isinstance(func, z3.ExprRef):
                    #     # For direct expressions
                    #     old_value = old_z3_model.eval(func, model_completion=True)
                    #     if old_value is not None:
                    #         different_model_constraints.append(func != old_value)
                            
                except z3.Z3Exception as e:
                    print(f"Warning: Failed to process {name}: {e}")
                    continue

            # Add the disjunction of differences as a constraint
            if different_model_constraints:
                try:
                    constraint = z3.Or(*different_model_constraints)
                    solver.assert_and_track(
                        constraint,
                        f"different_from_model_{hash(str(old_z3_model))}"
                    )
                    self.solver = solver
                except z3.Z3Exception as e:
                    print(f"Warning: Failed to create constraint: {e}")
                
        except Exception as e:
            print(f"Error in _update_solver: {str(e)}")
            raise

    # def find_difference_constraint(self, old_z3_model):
    #     different_model_constraints = []
    #     
    #     # Check differences in sentence letter assignments
    #     for letter in self.model_constraints.sentence_letters:
    #         old_value = old_z3_model.eval(letter)
    #         different_model_constraints.append(letter != old_value)
    #     
    #     # Check differences in primitive relations/functions
    #     for primitive_name, primitive in self.model_constraints.semantics.__dict__.items():
    #         if isinstance(primitive, z3.ExprRef):
    #             old_value = old_z3_model.eval(primitive)
    #             different_model_constraints.append(primitive != old_value)
    #             print(f"Primitive to vary between models: {primitive_name}")
    #
    #     return z3.Or(*different_model_constraints)

    # def find_next_model(self, old_z3_model):
    #     if old_z3_model is None:
    #         return
        # self._load_old_model(old_z3_model)
        #
        # # Add difference constraints if we have previous models
        # if self.old_z3_models is not None:
        #     for model_index, prev_model in enumerate(self.old_z3_models):
        #         self._add_difference_constraints(model_index, prev_model)

    # def _load_old_model(self, old_z3_model):
    #     if self.old_z3_models is None:
    #         self.old_z3_models = [old_z3_model]
    #     else:
    #         self.old_z3_models.append(old_z3_model)


    def _validate_semantic_theory(self, semantic_theory):
        """Validates and extracts components from the semantic theory dictionary.
        
        Ensures the semantic theory dictionary contains all required components with valid types
        and stores them as instance attributes. Required components include semantics class,
        proposition class, operator collection, and model structure class.
        
        Args:
            semantic_theory (dict): Dictionary containing:
                - "semantics": Class inheriting from SemanticDefaults
                - "proposition": Class inheriting from PropositionDefaults  
                - "operators": Instance of OperatorCollection
                - "model": Class inheriting from ModelDefaults
                - "dictionary" (optional): Dictionary mapping operators to alternate notation
                
        Raises:
            TypeError: If any component is missing or has an invalid type
            
        Note:
            Components are stored as instance attributes:
            - self.semantics: The semantic theory class
            - self.proposition: The proposition handling class
            - self.operators: The operator collection instance
            - self.dictionary: Optional operator translation dictionary
            - self.model_structure_class: The model structure class
        """
        if not isinstance(semantic_theory, dict) or len(semantic_theory) < 3:
            raise TypeError(
                "semantic_theory must be a tuple/list containing exactly 3 elements: "
                "(Semantics, Proposition, OperatorCollection)"
            )

        self.semantics = semantic_theory["semantics"]
        self.proposition = semantic_theory["proposition"] 
        self.operators = semantic_theory["operators"]
        self.dictionary = semantic_theory.get("dictionary", None)
        self.model_structure_class = semantic_theory["model"]

        # Validate semantics is subclass of SemanticDefaults
        if not issubclass(semantic_theory["semantics"], SemanticDefaults):
            raise TypeError(
                f"First element must be a subclass of SemanticDefaults, got {type(self.semantics)}"
            )

        # Validate proposition is subclass of PropositionDefaults
        if not issubclass(self.proposition, PropositionDefaults):
            raise TypeError(
                f"Second element must be a subclass of PropositionDefaults, got {type(self.proposition)}"
            )

        # Validate operators is instance of OperatorCollection
        if not isinstance(self.operators, OperatorCollection):
            raise TypeError(
                f"Third element must be an instance of OperatorCollection, got {type(self.operators)}"
            )

        # Validate model_structure_class is instance of ModelDefaults
        if not issubclass(self.model_structure_class, ModelDefaults):
            raise TypeError(
                f"Third element must be an instance of OperatorCollection, got {type(self.operators)}"
            )

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

    # _validate_settings method has been removed as it's now redundant
    # The BuildExample constructor already uses SettingsManager.get_complete_settings

    def check_result(self):
        """Compare the model findings against expected model existence.
        
        Returns:
            bool: True if model findings match expectations, False otherwise.
            
        The method compares the actual model status (whether a model was found)
        against the expected model status specified in settings["model"].
        This is used to verify if the model checker produced the expected result
        (e.g., finding a model when one should exist, or not finding one when
        none should exist).
        """
        model_expectation = self.settings["model"]
        model_findings = self.model_structure.z3_model_status
        return model_findings == model_expectation

    def print_result(self, example_name, theory_name):
        """Prints resulting model or no model if none is found.
        
        This method handles the display of model checking results, including:
        - Printing the model structure if a valid model is found
        - Displaying a message if no countermodel exists
        - Checking model satisfiability
        - Handling output saving if requested
        
        Args:
            example_name (str): The name of the example being checked
            theory_name (str): The name of the semantic theory being used
            
        The method also coordinates with the model structure's print_to method for
        detailed model output and handles the save_output setting by prompting the
        user for file saving preferences when appropriate.
        """
        model_structure = self.model_structure
        default_settings = self.example_settings
        
        # TODO: sort out what this was doing in the iterate function
        # if model_structure.z3_model is None:
        #     print(f"\nNo countermodel found for example '{example_name}' with theory '{theory_name}'")
        #     constraints = model_structure.model_constraints.all_constraints
        #     print(f"CONSTRAINTS {constraints} TYPE {type(constraints)}")
        #     return
        #
        # if model_structure.solver.check() != z3.sat:
        #     print("Warning: Model is no longer satisfiable")
        #     return
            
        model_structure.print_to(default_settings, example_name, theory_name)
            
        if model_structure.settings["save_output"]:
            file_name, save_constraints = self.ask_save()
            self.save_or_append(model_structure, file_name, save_constraints, example_name, theory_name)
            
    def ask_save(self):
        """Prompts the user to save the model output and specify output options.
        
        This method handles the user interaction for saving model output by:
        1. Asking if the user wants to save the output
        2. If yes, asking if Z3 constraints should be included
        3. Prompting for a filename (blank for appending to project file)
        
        Returns:
            tuple: (file_name, save_constraints) where:
                - file_name (str or None): Name for output file, None if no save requested,
                                         empty string for appending to project file
                - save_constraints (bool): Whether to include Z3 constraints in output
        """

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
        """Option to save or append model output to a file.
        
        This method handles saving the model output either by appending to an existing file
        or creating a new file. It supports two modes of operation:
        
        1. Append Mode: If file_name is empty, appends the output to the project's module file
        2. New File Mode: If file_name is provided, creates a new .py file in the project directory
        
        Args:
            model_structure: The model structure containing the results to save
            file_name (str): Target filename (empty for append mode)
            save_constraints (bool): Whether to include Z3 constraints in output
            example_name (str): Name of the example being saved
            theory_name (str): Name of the semantic theory used
            
        The method handles directory creation if needed and uses appropriate formatting
        for both append and new file modes. For append mode, it wraps the output in
        triple quotes. For new file mode, it creates a properly formatted Python file
        with a title comment.
        """

        # Handle the case where file_name is None (user declined to save)
        if file_name is None:
            return
        
        # Handle empty string (append to existing file)
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

