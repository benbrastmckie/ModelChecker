"""BuildModule implementation for managing model checking examples.

This module provides the BuildModule class for loading and executing model checking 
examples from Python modules. It handles dynamic module loading, configuration 
settings, and coordinating the model checking process.
"""

import os
import importlib.util
import concurrent.futures
import time
from concurrent.futures.thread import ThreadPoolExecutor
import sys
import threading

# Relative imports
from model_checker.output.progress import UnifiedProgress, Spinner
from model_checker.syntactic import Syntax
from model_checker.builder.serialize import (
    serialize_semantic_theory,
    deserialize_semantic_theory
)


class BuildModule:
    """Manages loading and executing model checking examples from Python modules.
    
    This class is responsible for dynamically loading a Python module containing modal logic
    examples, extracting configuration settings, and coordinating the model checking process.
    
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

    def _discover_theory_module(self, theory_name, semantic_theory):
        """Dynamically discover the theory module name from semantic theory.
        
        This method follows the Theory Agnostic Principle by extracting the module
        name from the semantic theory's components rather than using hardcoded mappings.
        
        Args:
            theory_name: Display name of the theory (e.g., "BernardChampollion")
            semantic_theory: Dictionary containing theory components
            
        Returns:
            str: Module name (e.g., "exclusion") or None if not found
        """
        # Try to extract module name from semantics class
        semantics_class = semantic_theory.get("semantics")
        if semantics_class and hasattr(semantics_class, "__module__"):
            module_path = semantics_class.__module__
            # Extract theory module name from path
            # e.g., "model_checker.theory_lib.exclusion.semantic" -> "exclusion"
            parts = module_path.split('.')
            if len(parts) >= 3 and parts[1] == "theory_lib":
                return parts[2]
        
        # Try model class as fallback
        model_class = semantic_theory.get("model")
        if model_class and hasattr(model_class, "__module__"):
            module_path = model_class.__module__
            parts = module_path.split('.')
            if len(parts) >= 3 and parts[1] == "theory_lib":
                return parts[2]
        
        # Try proposition class as final fallback
        prop_class = semantic_theory.get("proposition")
        if prop_class and hasattr(prop_class, "__module__"):
            module_path = prop_class.__module__
            parts = module_path.split('.')
            if len(parts) >= 3 and parts[1] == "theory_lib":
                return parts[2]
        
        return None
    
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

        # Store raw settings - validation happens per-theory in BuildExample
        self.raw_general_settings = getattr(self.module, "general_settings", None)
        
        # For backward compatibility, create general_settings dict
        # We need this for attributes and existing code that expects it
        if self.raw_general_settings is not None:
            # Use first theory's defaults as baseline (preserving existing behavior)
            first_theory = next(iter(self.semantic_theories.values()))
            # Create a temporary manager just to get the merged defaults
            # Don't print warnings during this setup phase
            import contextlib
            import io
            with contextlib.redirect_stdout(io.StringIO()):
                temp_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
                self.general_settings = temp_manager.validate_general_settings(self.raw_general_settings)
                self.general_settings = temp_manager.apply_flag_overrides(self.general_settings, self.module_flags)
        else:
            self.general_settings = DEFAULT_GENERAL_SETTINGS.copy()
        
        # Set attributes for backward compatibility
        for key, value in self.general_settings.items():
            setattr(self, key, value)
            
        # Initialize output manager if save_output is enabled
        from model_checker.output import OutputManager, InteractiveSaveManager, ConsoleInputProvider
        
        # Create interactive manager if save_output is enabled
        self.interactive_manager = None
        if self.save_output:
            # Create console input provider for production use
            input_provider = ConsoleInputProvider()
            self.interactive_manager = InteractiveSaveManager(input_provider)
            # Check if interactive flag is set
            if hasattr(self.module_flags, 'interactive') and self.module_flags.interactive:
                # Interactive flag specified - set mode directly
                self.interactive_manager.set_mode('interactive')
            else:
                # No interactive flag - prompt for mode
                self.interactive_manager.prompt_save_mode()
        
        self.output_manager = OutputManager(
            save_output=self.save_output,
            mode=getattr(self.module_flags, 'output_mode', 'batch'),
            sequential_files=getattr(self.module_flags, 'sequential_files', 'multiple'),
            interactive_manager=self.interactive_manager
        )
        
        # Create output directory if needed
        if self.output_manager.should_save():
            self.output_manager.create_output_directory()

    def _is_generated_project(self, module_dir):
        """Detect if module is from a generated project.
        
        Generated projects are identified by the project_ prefix pattern.
        This approach is structure-agnostic and works regardless of 
        internal theory organization. Checks both the current directory
        and parent directories for the project_ pattern.
        
        Args:
            module_dir (str): Directory containing the module
            
        Returns:
            bool: True if module is from a generated project
        """
        # Check current directory
        current_name = os.path.basename(module_dir)
        if current_name.startswith('project_'):
            return True
        
        # Check parent directories up to a reasonable depth
        current_path = module_dir
        for _ in range(3):  # Check up to 3 levels up
            parent_path = os.path.dirname(current_path)
            if parent_path == current_path:  # Reached root
                break
            parent_name = os.path.basename(parent_path)
            if parent_name.startswith('project_'):
                return True
            current_path = parent_path
        
        return False

    def _find_project_directory(self, module_dir):
        """Find the root directory of a generated project.
        
        Traverses up the directory tree to find the directory with project_ prefix.
        
        Args:
            module_dir (str): Directory containing the module
            
        Returns:
            str: Path to the project root directory
        """
        # Check current directory first
        current_name = os.path.basename(module_dir)
        if current_name.startswith('project_'):
            return module_dir
        
        # Check parent directories
        current_path = module_dir
        for _ in range(3):  # Check up to 3 levels up
            parent_path = os.path.dirname(current_path)
            if parent_path == current_path:  # Reached root
                break
            parent_name = os.path.basename(parent_path)
            if parent_name.startswith('project_'):
                return parent_path
            current_path = parent_path
        
        # Fallback to module_dir if no project directory found
        return module_dir

    def _load_module(self):
        """Load the Python module from file.
        
        Returns:
            The loaded module object
            
        Raises:
            ImportError: If module cannot be loaded
        """
        try:
            module_dir = os.path.dirname(os.path.abspath(self.module_path))
            
            # Check if this is a generated project
            is_generated_project = self._is_generated_project(module_dir)
            
            if is_generated_project:
                # Find the actual project directory (may be current dir or a parent)
                project_dir = self._find_project_directory(module_dir)
                project_name = os.path.basename(project_dir)
                
                # For generated projects, ensure both project and parent directories are in sys.path
                # This enables both relative imports and sibling module imports
                project_parent = os.path.dirname(project_dir)
                if project_parent not in sys.path:
                    sys.path.insert(0, project_parent)
                if project_dir not in sys.path:
                    sys.path.insert(0, project_dir)
                if module_dir not in sys.path:
                    sys.path.insert(0, module_dir)
                
                # Set package context to enable relative imports
                # If we're in a subdirectory, build the full package path
                if module_dir != project_dir:
                    # Calculate relative path from project to module directory
                    rel_path = os.path.relpath(module_dir, project_dir)
                    subpackage_parts = rel_path.split(os.sep)
                    package_name = project_name + "." + ".".join(subpackage_parts)
                else:
                    package_name = project_name
            else:
                # Existing package detection logic for theory_lib and installed packages
                package_parts = []
                current_dir = module_dir
                
                while os.path.exists(os.path.join(current_dir, "__init__.py")):
                    package_parts.insert(0, os.path.basename(current_dir))
                    parent_dir = os.path.dirname(current_dir)
                    if parent_dir == current_dir:
                        break
                    current_dir = parent_dir
                
                if package_parts:
                    package_name = ".".join(package_parts)
                    parent_of_package = os.path.dirname(current_dir)
                    if parent_of_package not in sys.path:
                        sys.path.insert(0, parent_of_package)
                else:
                    package_name = ""
                    if module_dir not in sys.path:
                        sys.path.insert(0, module_dir)
            
            # Load the module
            spec = importlib.util.spec_from_file_location(
                self.module_name, 
                self.module_path, 
                submodule_search_locations=[module_dir]
            )
            if spec is None or spec.loader is None:
                raise ImportError("Module spec could not be loaded.")
            
            module = importlib.util.module_from_spec(spec)
            
            # Set package attribute for relative imports
            if package_name:
                module.__package__ = package_name
            
            spec.loader.exec_module(module)
            return module
            
        except Exception as e:
            if "attempted relative import" in str(e):
                # Enhanced error message for relative import issues
                if self._is_generated_project(os.path.dirname(os.path.abspath(self.module_path))):
                    raise ImportError(
                        f"Relative import error in generated project '{self.module_name}': {e}\n"
                        f"Generated projects should have their imports properly configured. "
                        f"This may indicate an issue with the project template or generation process."
                    ) from e
                else:
                    raise ImportError(
                        f"Relative import error in '{self.module_name}': {e}\n"
                        f"To use relative imports, make sure your project follows Python package structure with __init__.py files."
                    ) from e
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
        """
        example_theory_tuples = []
        for theory_name, semantic_theory in semantic_theories.items():
            translated_case = example_case.copy()
            dictionary = semantic_theory.get("dictionary", None)
            if dictionary:
                translated_case = self.translate(translated_case, dictionary)
            example_tuple = (theory_name, semantic_theory, translated_case)
            example_theory_tuples.append(example_tuple)
        return example_theory_tuples

    def run_model_check(self, example_case, example_name, theory_name, semantic_theory):
        """Run model checking with the given parameters.
        
        Args:
            example_case: List of [premises, conclusions, settings]
            example_name: Name of the example being processed
            theory_name: Name of the semantic theory
            semantic_theory: Dictionary with semantics implementation
            
        Returns:
            BuildExample: The processed example
            
        Raises:
            TimeoutError: If execution exceeds the maximum time
            ValueError: If parameters are invalid
        """
        from model_checker.builder.example import BuildExample
        
        # Apply translation if needed
        dictionary = semantic_theory.get("dictionary", None)
        if dictionary:
            example_case = self.translate(example_case, dictionary)
        
        # Start progress tracking
        spinner = Spinner()
        spinner.start()
        
        try:
            example = BuildExample(self, semantic_theory, example_case, theory_name)
            return example
        finally:
            spinner.stop()
    
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
        """
        from model_checker.models.constraints import ModelConstraints

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
    
    @staticmethod
    def try_single_N_static(theory_name, theory_config, example_case):
        """
        Static version of try_single_N that can be pickled for multiprocessing.
        
        This method is designed to be called by ProcessPoolExecutor with
        serialized data that can be pickled across process boundaries.
        
        Args:
            theory_name: Name of the theory
            theory_config: Serialized theory configuration
            example_case: Example case with premises, conclusions, settings
            
        Returns:
            tuple: (success, runtime)
        """
        from model_checker.models.constraints import ModelConstraints
        from model_checker.syntactic import Syntax
        from model_checker.builder.serialize import deserialize_semantic_theory
        
        # Reconstruct the semantic theory from serialized data
        semantic_theory = deserialize_semantic_theory(theory_config)
        
        # Recreate the logic from try_single_N
        premises, conclusions, settings = example_case
        semantics_class = semantic_theory["semantics"]
        model_structure_class = semantic_theory["model"]
        operators = semantic_theory["operators"]
        syntax = Syntax(premises, conclusions, operators)
        # Different theories have different initialization patterns
        if 'Logos' in semantics_class.__name__:
            semantics = semantics_class(combined_settings=settings)
        else:
            semantics = semantics_class(settings)
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            semantic_theory["proposition"],
        )
        model_structure = model_structure_class(model_constraints, settings)
        run_time = model_structure.z3_model_runtime
        success = run_time < settings['max_time']
        
        # Define color constants
        GREEN = "\033[32m"
        RED = "\033[31m"
        RESET = "\033[0m"
        
        if success:
            # Green color for successful runs
            output = (
                f"{GREEN}{model_structure.semantics.name} ({theory_name}):\n"
                f"  RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {settings['N']}.{RESET}\n"
            )
            print(output, end='', flush=True)
        else:
            # Red color for timeouts
            output = (
                f"{RED}{model_structure.semantics.name} ({theory_name}): "
                f"TIMED OUT\n  RUN TIME = {run_time}, " +
                f"MAX TIME = {settings['max_time']}, " +
                f"N = {example_case[2]['N']}.{RESET}\n"
            )
            print(output, end='', flush=True)
        return success, run_time
    
    def try_single_N_serialized(self, theory_name, theory_config, example_case):
        """
        Wrapper for try_single_N that deserializes the semantic theory first.
        
        This method is designed to be called by ProcessPoolExecutor with
        serialized data that can be pickled across process boundaries.
        
        Args:
            theory_name: Name of the theory
            theory_config: Serialized theory configuration
            example_case: Example case with premises, conclusions, settings
            
        Returns:
            tuple: (success, runtime)
        """
        # Reconstruct the semantic theory from serialized data
        semantic_theory = deserialize_semantic_theory(theory_config)
        
        # Call the original method with reconstructed objects
        return self.try_single_N(theory_name, semantic_theory, example_case)

    def compare_semantics(self, example_theory_tuples):
        """Compare different semantic theories by finding maximum model sizes.
        
        This method attempts to find the maximum model size (N) for each semantic theory
        by incrementally testing larger values of N until a timeout occurs. It runs the
        tests concurrently using a ProcessPoolExecutor for better performance.
        
        The method now uses serialization to avoid pickle errors with complex objects.
        
        Args:
            example_theory_tuples: List of tuples containing (theory_name, semantic_theory, example_case)
                where example_case is [premises, conclusions, settings]
                
        Returns:
            list: List of tuples containing (theory_name, max_N) where max_N is the largest
                  number of worlds for which a model was found within the time limit
        """
        results = []
        active_cases = {}  # Track active cases and their current N values
        
        with concurrent.futures.ProcessPoolExecutor() as executor:
            # Initialize first run for each case
            futures = {}
            all_times = []
            
            for case in example_theory_tuples:
                theory_name, semantic_theory, (premises, conclusions, settings) = case
                
                # Serialize the semantic theory for pickling
                theory_config = serialize_semantic_theory(theory_name, semantic_theory)
                
                # Create example case with copied settings
                example_case = [premises, conclusions, settings.copy()]
                active_cases[theory_name] = settings['N']  # Store initial N
                all_times.append(settings['max_time'])
                
                # Submit with serialized data
                new_case = (theory_name, theory_config, example_case)
                futures[executor.submit(BuildModule.try_single_N_static, *new_case)] = (
                    theory_name, theory_config, example_case, semantic_theory
                )
            
            max_time = max(all_times) if all_times else 1
                
            while futures:
                done, _ = concurrent.futures.wait(
                    futures,
                    return_when=concurrent.futures.FIRST_COMPLETED
                )
                for future in done:
                    theory_name, theory_config, example_case, semantic_theory = futures.pop(future)
                    max_time = example_case[2]['max_time']
                    
                    try:
                        success, runtime = future.result()
                        
                        if success and runtime < max_time:
                            # Increment N and submit new case
                            example_case[2]['N'] = active_cases[theory_name] + 1
                            active_cases[theory_name] = example_case[2]['N']
                            
                            # Submit with same serialized config but updated N
                            new_case = (theory_name, theory_config, example_case)
                            futures[executor.submit(BuildModule.try_single_N_static, *new_case)] = (
                                theory_name, theory_config, example_case, semantic_theory
                            )
                        else:
                            # Found max N for this case
                            results.append((theory_name, active_cases[theory_name] - 1))
                            
                    except Exception as e:
                        import traceback
                        print(
                            f"\nERROR: {semantic_theory['semantics'].__name__} "
                            f"({theory_name}) for N = {example_case[2]['N']}. {str(e)}"
                        )
                        # Log the error but try to continue with other theories
                        results.append((theory_name, active_cases.get(theory_name, 0) - 1))
                        
        return results
    
    def run_comparison(self):
        """Compare different semantic theories by running examples and printing results.
        
        Iterates through each example in example_range and runs it against all semantic theories.
        For each example:
        1. Prints example name and details (premises and conclusions)
        2. Translates operators according to each theory's dictionary
        3. Compares semantic theories by finding maximum model sizes
        4. Prints results showing which theories could handle larger models
        """
        from model_checker.models.constraints import ModelConstraints
        
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

    def _prompt_for_iterations(self):
        """Prompt user for number of iterations in interactive mode.
        
        Returns:
            int: Number of additional models to find (0 means no more)
        """
        print("\nDo you want to find another model?")
        response = input("Enter a number to iterate or hit return to continue: ").strip()
        
        if not response:
            # User hit return - continue to next example
            return 0
            
        try:
            num_iterations = int(response)
            if num_iterations < 0:
                print("Please enter a positive number.")
                return self._prompt_for_iterations()
            return num_iterations
        except ValueError:
            print("Please enter a valid number or hit return to continue.")
            return self._prompt_for_iterations()

    def process_example(self, example_name, example_case, theory_name, semantic_theory):
        """Process a single model checking example with a fresh Z3 context.
        
        Args:
            example_name (str): Name of the example being processed
            example_case (list): The example case containing [premises, conclusions, settings]
            theory_name (str): Name of the semantic theory being used
            semantic_theory (dict): Dictionary containing the semantic theory implementation
            
        Returns:
            BuildExample: The example after processing
        """
        from model_checker.utils import Z3ContextManager
        
        # Always reset Z3 context at the start of processing a new example
        Z3ContextManager.reset_context()
        
        # Disable debug logs for cleaner output
        import logging
        logging.getLogger().setLevel(logging.ERROR)
        """Process a single model checking example.
        
        Args:
            example_name (str): Name of the example being processed
            example_case (list): The example case containing [premises, conclusions, settings]
            theory_name (str): Name of the semantic theory being used
            semantic_theory (dict): Dictionary containing the semantic theory implementation
            
        Returns:
            BuildExample: The example after processing
        """
        from model_checker.builder.example import BuildExample
        import sys
        import logging
        import importlib
        import z3
        
        # Disable all debug logs for cleaner output
        logging.getLogger().setLevel(logging.ERROR)
        # Specifically disable iteration logs
        for logger_name in ["model_checker", "model_checker.builder", "model_checker.iterate"]:
            logging.getLogger(logger_name).setLevel(logging.ERROR)
        
        # Reset Z3 solver to ensure clean state for each example
        z3.reset_params()
        z3.set_param(verbose=0)
        
        # Apply translation if needed
        dictionary = semantic_theory.get("dictionary", None)
        if dictionary:
            example_case = self.translate(example_case, dictionary)
        
        # Get the iterate count early to set up progress tracking
        iterate_count = example_case[2].get('iterate', 1)
        
        # If iterate=1, no progress tracking needed
        if iterate_count == 1:
            # Create and solve the example without progress tracking
            example = BuildExample(self, semantic_theory, example_case, theory_name)
            self._capture_and_save_output(example, example_name, theory_name)
            return example
        
        # Create unified progress tracker for all models
        max_time = example_case[2].get('max_time', 60.0)
        progress = UnifiedProgress(
            total_models=iterate_count,
            max_time=max_time  # Single timeout for all operations
        )
        
        # Add vertical space before first progress bar
        print()
        
        # Capture Model 1 start time BEFORE any work
        model_1_start = time.time()
        
        # Start progress for first model with timing
        progress.start_model_search(1, start_time=model_1_start)
        
        # Create and solve the example
        example = BuildExample(self, semantic_theory, example_case, theory_name)
        
        # Update progress
        progress.model_checked()
        
        # Store timing reference for iteration report
        # The model already has z3_model_runtime for solver time
        # Add total search time for consistency
        example.model_structure._search_start_time = model_1_start
        example.model_structure._total_search_time = time.time() - model_1_start
        
        # Check if a model was found
        if not example.model_structure.z3_model_status:
            progress.complete_model_search(found=False)
            progress.finish()
            self._capture_and_save_output(example, example_name, theory_name)
            return example
        
        # Complete first model search
        progress.complete_model_search(found=True)
        
        # Add vertical space after first progress bar
        print()
        
        # Pass progress to example for iterator to use
        if iterate_count > 1:
            example._unified_progress = progress
        
        # Handle iteration for interactive mode first to get correct count
        if self.interactive_manager and self.interactive_manager.is_interactive():
            # First, print the model without numbering
            self._capture_and_save_output(example, example_name, theory_name)
            
            # Then prompt for iterations
            user_iterations = self._prompt_for_iterations()
            if user_iterations == 0:
                progress.finish()
                return example
            # Override iterate count with user's choice (plus 1 for the model already shown)
            iterate_count = user_iterations + 1
            
            # Update progress with new total
            progress.total_models = iterate_count
            example._unified_progress = progress
        else:
            # In batch mode, just print the first model without numbering
            # The numbering starts with the second model from iteration
            self._capture_and_save_output(example, example_name, theory_name)
            
            # Return if we don't need to iterate in batch mode
            if iterate_count <= 1:
                progress.finish()
                return example
            
            # Add vertical space after the first model before iteration starts
            print()
        
        try:
            # Get the theory-specific iterate_example function
            try:
                # Dynamically discover the theory module from the semantic theory
                module_name = self._discover_theory_module(theory_name, semantic_theory)
                
                if not module_name:
                    # Fallback: try theory_name as module name directly
                    module_name = theory_name.lower()
                
                # Import the theory module to access its iterate function
                theory_module = importlib.import_module(f"model_checker.theory_lib.{module_name}")
                
                # Check for generator version first
                if hasattr(theory_module, 'iterate_example_generator'):
                    theory_iterate_example = theory_module.iterate_example_generator
                elif hasattr(theory_module, 'iterate_example'):
                    theory_iterate_example = theory_module.iterate_example
                else:
                    raise ImportError(f"Theory module '{module_name}' does not provide an iterate_example function")
            except ImportError as e:
                print(f"Error: {e}", file=sys.stderr)
                return example
            
            # Check if theory supports generator interface
            if hasattr(theory_iterate_example, '__wrapped__') and \
               hasattr(theory_iterate_example.__wrapped__, 'returns_generator'):
                # Use generator interface for incremental display
                self._run_generator_iteration(example, theory_iterate_example, example_name, theory_name, iterate_count)
                return example
            
            # Fallback to list-based iteration
            model_structures = theory_iterate_example(example, max_iterations=iterate_count)
            
            # Skip the first model which is already printed
            # Track distinct models for numbering
            distinct_count = 1
            # Use iterate_count for the expected total models rather than actual found models
            expected_total = iterate_count
            total_distinct = sum(1 for s in model_structures if not hasattr(s, '_is_isomorphic') or not s._is_isomorphic)
            
            for i, structure in enumerate(model_structures[1:], start=2):
                # Only display non-isomorphic models with their differences
                if not hasattr(structure, '_is_isomorphic') or not structure._is_isomorphic:
                    distinct_count += 1
                    
                    # For the first model, just print it
                    if distinct_count == 1:
                        # Print model header
                        print(f"MODEL {distinct_count}/{expected_total}")
                        
                        # Set the current model structure
                        example.model_structure = structure
                        
                        # Print the model
                        self._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
                    else:
                        # For subsequent models, first print the differences then the model
                        # Print detailed differences between this model and the previous one
                        previous_model = model_structures[i-2]  # The -2 is because i starts at 1, plus we want the previous model
                        
                        # Recalculate the detailed differences between this model and the previous one
                        # This ensures we get the full detailed differences rather than just the summary
                        # Get a valid previous model
                        previous_idx = i - 2  # models_structures[0] is the first model, and we're at i=0 for the second model (1-indexed)
                        if previous_idx >= 0 and previous_idx < len(model_structures):
                            previous_model = model_structures[previous_idx]
                                
                            # Use the model structure's detect_model_differences if available
                            # BUT only if model_differences hasn't already been set by the iterator
                            if not hasattr(structure, 'model_differences') or structure.model_differences is None:
                                try:
                                    # First try using theory-specific difference detection
                                    if hasattr(structure, 'detect_model_differences'):
                                        structure.model_differences = structure.detect_model_differences(previous_model)
                                        structure.previous_structure = previous_model
                                    else:
                                        # Check if structure has calculate_model_differences for legacy support
                                        if hasattr(structure, 'calculate_model_differences'):
                                            structure.model_differences = structure.calculate_model_differences(previous_model)
                                            structure.previous_structure = previous_model
                                except Exception as e:
                                    print(f"\nError calculating detailed differences: {str(e)}")
                        
                        # Now print the differences
                        try:
                            # Each theory must provide its own print_model_differences method
                            if hasattr(structure, 'print_model_differences'):
                                structure.print_model_differences()
                            else:
                                print("Error: Theory does not provide print_model_differences method")
                        except Exception as e:
                            print(f"Error printing model differences: {str(e)}")
                                
                        # Print model header
                        print(f"MODEL {distinct_count}/{expected_total}")
                        
                        # Set the current model structure
                        example.model_structure = structure
                        
                        # Mark the last model to prevent partial output issues
                        if distinct_count == total_distinct or distinct_count == expected_total:
                            structure._is_last_model = True
                            
                        # Print the model
                        self._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
                    
                # For isomorphic models that are skipped, we could optionally add a subtle indicator
                # Uncomment to show skipped models
                # elif hasattr(structure, '_is_isomorphic') and structure._is_isomorphic:
                #     print(f"\n(Skipped isomorphic model variant {i})")
            
            # Print summary after all models have been displayed
            distinct_count = sum(1 for s in model_structures if not hasattr(s, '_is_isomorphic') or not s._is_isomorphic)
            
            # Print any iteration debug messages if available
            if hasattr(example, '_iterator') and hasattr(example._iterator, 'get_debug_messages'):
                debug_messages = example._iterator.get_debug_messages()
                if debug_messages:
                    # Print a separator line first
                    print()
                    for msg in debug_messages:
                        print(msg)
            
            # Termination info is now handled by the iterator's detailed report
            
            # Check if there was any partial output
            if hasattr(example.model_structure, 'model_differences') and not hasattr(example.model_structure, '_is_last_model'):
                # Clear out any partial difference output
                print("\n" + "="*40)
        
        except Exception as e:
            print(f"Error during iteration: {str(e)}")
            import traceback
            print(traceback.format_exc())
        finally:
            # Ensure progress is cleaned up
            progress.finish()
        
        return example
    
    def _run_generator_iteration(self, example, theory_iterate_example, example_name, theory_name, iterate_count):
        """Run iteration using generator interface for incremental display.
        
        Args:
            example: The BuildExample instance
            theory_iterate_example: Theory-specific iterate function with generator support
            example_name: Name of the example being run
            theory_name: Name of the theory
            iterate_count: Total number of models to find
        """
        # Get generator from theory
        model_generator = theory_iterate_example(example, max_iterations=iterate_count)
        
        # Track distinct models
        distinct_count = 0  # Will increment when we find the first additional model
        previous_model = example.model_structure
        
        try:
            # Process models as they're yielded
            for i, structure in enumerate(model_generator, start=2):
                # Skip isomorphic models in display
                if hasattr(structure, '_is_isomorphic') and structure._is_isomorphic:
                    continue
                    
                distinct_count += 1
                
                # Always print differences from previous model (except for the first additional model)
                if previous_model:
                    # Print differences using structure's method
                    if hasattr(structure, 'print_model_differences'):
                        structure.print_model_differences()
                    else:
                        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===")
                        if hasattr(structure, 'model_differences') and structure.model_differences:
                            # Basic difference display if no custom method
                            from model_checker.iterate.metrics import ResultFormatter
                            formatter = ResultFormatter()
                            diff_report = formatter.format_difference_report(structure.model_differences)
                            print(diff_report)
                        else:
                            print("(No differences calculated)")
                
                # Print model header - now showing correct numbering (2/4, 3/4, 4/4)
                print(f"MODEL {distinct_count + 1}/{iterate_count}")
                
                # Update example with new model
                example.model_structure = structure
                
                # Display model immediately
                self._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
                
                # Add extra vertical space after non-isomorphic models (except for the last one)
                # Only add space if we're not at the last model we'll actually find
                # Note: We can't know if more models exist until we try to get the next one
                # So we always add space unless we've reached the requested count
                if distinct_count < iterate_count - 1:
                    print()
                
                # Update previous model for next iteration
                previous_model = structure
                
        except StopIteration:
            # Normal termination - no more models found
            pass
        except Exception as e:
            print(f"Error during iteration: {e}", file=sys.stderr)
            import traceback
            traceback.print_exc()
        
        # Termination info is now handled by the iterator's detailed report
        
    def _get_termination_info(self, example, found_count, requested_count):
        """Generate comprehensive termination message.
        
        Args:
            example: BuildExample with iterator information
            found_count: Number of distinct models found
            requested_count: Number of models requested
            
        Returns:
            str: Formatted termination message
        """
        # Get iterator if available
        iterator = getattr(example, '_iterator', None)
        if not iterator:
            return f"Found {found_count}/{requested_count} distinct models."
        
        # Get basic stats
        skipped_count = getattr(iterator, 'isomorphic_model_count', 0)
        elapsed_time = 0.0
        if hasattr(iterator, 'termination_manager'):
            elapsed_time = iterator.termination_manager.get_elapsed_time()
        
        # Base message with stats
        base_msg = f"Found {found_count}/{requested_count} distinct models "
        base_msg += f"(skipped {skipped_count} isomorphic models in {elapsed_time:.1f}s)."
        
        # Add termination reason
        if found_count == requested_count:
            reason = "Successfully found all requested models."
        else:
            reason = self._get_termination_reason(iterator, found_count, requested_count)
        
        return f"{base_msg}\n{reason}"
    
    def _get_termination_reason(self, iterator, found_count, requested_count):
        """Determine why iteration stopped.
        
        Returns formatted reason string.
        """
        # Check debug messages for specific reasons
        debug_messages = iterator.get_debug_messages() if hasattr(iterator, 'get_debug_messages') else []
        
        # Debug: print messages to understand termination
        # import sys
        # print(f"DEBUG: Found {len(debug_messages)} debug messages:", file=sys.stderr)
        # for msg in debug_messages:
        #     print(f"  - {msg}", file=sys.stderr)
        
        # Look for specific termination indicators
        for msg in reversed(debug_messages):  # Check most recent first
            if "No more models found" in msg and "unsat" in msg:
                return "Search complete: No more non-isomorphic models exist."
            elif "timeout" in msg.lower() and "reached" in msg.lower():
                # Extract timeout value from message if present
                import re
                timeout_match = re.search(r'(\d+\.?\d*)s\)', msg)
                if timeout_match:
                    timeout_val = timeout_match.group(1)
                    return f"Search stopped: Time limit reached (max {timeout_val}s)."
                else:
                    timeout_val = iterator.settings.get('iteration_timeout', iterator.settings.get('timeout', 300))
                    return f"Search stopped: Time limit reached (max {timeout_val}s)."
            elif "consecutive invalid" in msg or "consecutive failed" in msg:
                max_attempts = iterator.settings.get('max_invalid_attempts', 20)
                return f"Search stopped: {max_attempts} consecutive attempts found only isomorphic models."
            elif "Insufficient progress" in msg:
                return "Search stopped: Too many checks with insufficient progress."
        
        # Default message if no specific reason found
        return f"Search ended after finding {found_count} of {requested_count} requested models."
        
    def process_iterations(self, example_name, example_case, theory_name, semantic_theory):
        """Process multiple iterations of model checking for a given example.
        
        Uses ModelIterator to find multiple distinct models for the example.
        
        Args:
            example_name (str): Name of the example being processed
            example_case (list): The example case containing [premises, conclusions, settings]
            theory_name (str): Name of the semantic theory being used
            semantic_theory (dict): Dictionary containing the semantic theory implementation
        
        Returns:
            BuildExample: The final example after all iterations
        """
        # Forward to the new process_example method which handles iteration in a better way
        return self.process_example(example_name, example_case, theory_name, semantic_theory)

    def _capture_and_save_output(self, example, example_name, theory_name, model_num=None):
        """Capture and save model output if save_output is enabled.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            theory_name: Name of the theory
            model_num: Optional model number for iterations
        """
        if not self.output_manager.should_save():
            # Just print normally if not saving
            example.print_model(example_name, theory_name)
            return
            
        # Import necessary components
        from model_checker.output import ModelDataCollector, MarkdownFormatter, ANSIToMarkdown
        import io
        import sys
        
        # Capture the output
        captured_output = io.StringIO()
        old_stdout = sys.stdout
        sys.stdout = captured_output
        
        try:
            # Print the model to our capture buffer
            example.print_model(example_name, theory_name, output=captured_output)
            raw_output = captured_output.getvalue()
        finally:
            sys.stdout = old_stdout
            
        # Also print to console so user sees output
        print(raw_output, end='')
        
        # Convert ANSI colors if present
        converter = ANSIToMarkdown()
        converted_output = converter.convert(raw_output)
        
        # Collect model data
        collector = ModelDataCollector()
        model_data = collector.collect_model_data(
            example.model_structure,
            example_name,
            theory_name
        )
        
        # If this is part of an iteration, update the example name
        if model_num is not None:
            display_name = f"{example_name}_model{model_num}"
        else:
            display_name = example_name
            
        # Format the output
        formatter = MarkdownFormatter(use_colors=True)
        formatted_output = formatter.format_example(model_data, converted_output)
        
        # Handle interactive vs batch save
        if self.interactive_manager and self.interactive_manager.is_interactive():
            # Check if model found
            if example.model_structure.z3_model_status:
                # Prompt to save this model
                if self.interactive_manager.prompt_save_model(example_name):
                    # Get model number
                    model_number = model_num or self.interactive_manager.get_next_model_number(example_name)
                    # Save interactively
                    self.output_manager.save_model_interactive(
                        example_name, model_data, formatted_output, model_number
                    )
        else:
            # Batch mode - save normally
            self.output_manager.save_example(display_name, model_data, formatted_output)
    
    def run_examples(self):
        """Process and execute each example case with all semantic theories.
        
        Iterates through example cases and theories, translating operators if needed.
        Runs model checking with progress indicator and timeout handling.
        Prints results or timeout message for each example/theory combination.
        """
        from model_checker.builder.example import BuildExample
        import z3
        import sys
        import gc
        
        # For each example, create a completely isolated Z3 environment
        # This ensures no state leakage between examples, solving the timeout issues
        # that can occur when running multiple examples in sequence
        try:
            for example_name, example_case in self.example_range.items():
                # Force garbage collection to clean up any lingering Z3 objects
                gc.collect()
                
                # Reset Z3 context to create a fresh environment for this example
                # This is the critical fix for ensuring proper Z3 state isolation
                # Each example gets its own fresh Z3 context, preventing any state leakage
                import z3
                if hasattr(z3, '_main_ctx'):
                    z3._main_ctx = None
                
                # Force another garbage collection to ensure clean state
                gc.collect()
                
                # Run the system in a clean state
                for theory_name, semantic_theory in self.semantic_theories.items():
                    # Make setting reset for each semantic_theory
                    example_copy = list(example_case)
                    example_copy[2] = example_case[2].copy()
                    
                    # Process the example with our new unified approach
                    # This handles both single models and iterations consistently
                    try:
                        self.process_example(example_name, example_copy, theory_name, semantic_theory)
                    finally:
                        # Force cleanup after each example to prevent state leaks
                        gc.collect()
                        
        except KeyboardInterrupt:
            print("\n\nExecution interrupted by user.")
            # Still finalize if we saved any output
            if self.output_manager.should_save() and self.output_manager.output_dir is not None:
                self.output_manager.finalize()
                import os
                print(f"\nPartial output saved to: {os.path.abspath(self.output_manager.output_dir)}")
            sys.exit(1)
                    
        # Finalize output saving if enabled
        if self.output_manager.should_save():
            self.output_manager.finalize()
            
            # Only print path if output was actually saved
            if self.output_manager.output_dir is not None:
                # Get full path for display
                import os
                full_path = os.path.abspath(self.output_manager.output_dir)
                
                # Prompt for directory change
                if self.interactive_manager:
                    self.interactive_manager.prompt_change_directory(full_path)
                else:
                    # No interactive manager - show instructions directly
                    print(f"\nOutput saved to: {full_path}")
                    print(f"To change to output directory, run:")
                    print(f"  cd {full_path}")
