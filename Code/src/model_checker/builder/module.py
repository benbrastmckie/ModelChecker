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

# Relative imports
from model_checker.builder.progress import Spinner
from model_checker.syntactic import Syntax

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

        # Initialize settings manager with first semantic theory
        first_theory = next(iter(self.semantic_theories.values()))
        self.settings_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
        
        # Load general settings
        user_general_settings = getattr(self.module, "general_settings", None)
        self.general_settings = self.settings_manager.validate_general_settings(user_general_settings)
        
        # Apply flag overrides for general settings
        self.general_settings = self.settings_manager.apply_flag_overrides(self.general_settings, self.module_flags)
        
        # Set attributes for backward compatibility
        for key, value in self.general_settings.items():
            setattr(self, key, value)

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
            example = BuildExample(self, semantic_theory, example_case)
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
        from model_checker.model import ModelConstraints

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
        """
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
    
    def run_comparison(self):
        """Compare different semantic theories by running examples and printing results.
        
        Iterates through each example in example_range and runs it against all semantic theories.
        For each example:
        1. Prints example name and details (premises and conclusions)
        2. Translates operators according to each theory's dictionary
        3. Compares semantic theories by finding maximum model sizes
        4. Prints results showing which theories could handle larger models
        """
        from model_checker.model import ModelConstraints
        
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
        
        # Create and solve the example
        example = BuildExample(self, semantic_theory, example_case)
        
        # Check if a model was found
        if not example.model_structure.z3_model_status:
            example.print_model(example_name, theory_name)
            return example
        
        # Get the iterate count
        iterate_count = example.settings.get('iterate', 1)
        
        # Print the first model with numbering if we're iterating
        if iterate_count > 1:
            print(f"\nMODEL 1/{iterate_count}")
            
        example.print_model(example_name, theory_name)
        
        # Return if we don't need to iterate
        if iterate_count <= 1:
            return example
        
        try:
            # Get the theory-specific iterate_example function
            try:
                # Map display name to module name
                # This mapping handles cases where theory_name is a display name (like "Brast-McKie")
                # rather than the actual module name used for imports
                theory_display_to_module = {
                    "Brast-McKie": "logos",  # Brast-McKie is the logos theory
                    "Default": "default",
                    "Exclusion": "exclusion",
                    "unilateral_theory": "exclusion",  # Exclusion theory's internal name
                    "Imposition": "imposition",
                    "Bimodal": "bimodal",
                    "Logos": "logos"
                }
                
                # Get the module name from the mapping or use the theory name directly
                module_name = theory_display_to_module.get(theory_name, theory_name.lower())
                
                # Import the theory module to access its iterate_example function
                theory_module = importlib.import_module(f"model_checker.theory_lib.{module_name}")
                if not hasattr(theory_module, 'iterate_example'):
                    raise ImportError(f"Theory module '{module_name}' does not provide an iterate_example function")
                
                theory_iterate_example = theory_module.iterate_example
            except ImportError as e:
                print(f"Error: {e}", file=sys.stderr)
                return example
            
            # Find additional models using the theory-specific iterate_example function
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
                        print(f"\nMODEL {distinct_count}/{expected_total}")
                        
                        # Set the current model structure
                        example.model_structure = structure
                        
                        # Print the model
                        example.print_model(f"{example_name}", theory_name)
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
                            # Force setting to properly colorize output
                            print("\033[1m\033[0m", end="")  # Force ANSI escape sequence processing
                            
                            # Use format_model_differences if available (theory-specific detailed formatting)
                            if hasattr(structure, 'format_model_differences') and structure.model_differences:
                                structure.format_model_differences(structure.model_differences)
                            # Fall back to generic print_model_differences
                            elif hasattr(structure, 'print_model_differences'):
                                # Print the color test first to ensure terminal capabilities are recognized
                                if not structure.print_model_differences():
                                    # If method returns False, no differences were found or displayed
                                    pass  # Let's suppress the "No differences" message per requirements
                            # Last resort: use the ModelStructure's generic methods
                            elif hasattr(structure, 'model_differences') and structure.model_differences:
                                # Just print the differences directly
                                print("\n=== MODEL DIFFERENCES ===\n")
                                print(structure.model_differences)
                            else:
                                # Let's also suppress this message as it's similar to "No model differences"
                                pass
                        except Exception as e:
                            print(f"Error printing model differences: {str(e)}")
                                
                        # Print model header
                        print(f"\nMODEL {distinct_count}/{expected_total}")
                        
                        # Set the current model structure
                        example.model_structure = structure
                        
                        # Mark the last model to prevent partial output issues
                        if distinct_count == total_distinct or distinct_count == expected_total:
                            structure._is_last_model = True
                            
                        # Print the model
                        example.print_model(f"{example_name}", theory_name)
                    
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
            
            print(f"\nFound {distinct_count}/{expected_total} distinct models.")
            
            # Check if there was any partial output
            if hasattr(example.model_structure, 'model_differences') and not hasattr(example.model_structure, '_is_last_model'):
                # Clear out any partial difference output
                print("\n" + "="*40)
        
        except Exception as e:
            print(f"Error during iteration: {str(e)}")
            import traceback
            print(traceback.format_exc())
        
        return example
        
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
