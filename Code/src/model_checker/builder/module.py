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

    def _load_module(self):
        """Load the Python module from file.
        
        Returns:
            The loaded module object
            
        Raises:
            ImportError: If module cannot be loaded
        """
        try:
            # Add the parent directory to sys.path to enable package imports
            module_dir = os.path.dirname(os.path.abspath(self.module_path))
            
            # Set up the appropriate package context for relative imports
            package_parts = []
            current_dir = module_dir
            
            # Build package name by traversing directories upward until we find no __init__.py
            while os.path.exists(os.path.join(current_dir, "__init__.py")):
                package_parts.insert(0, os.path.basename(current_dir))
                parent_dir = os.path.dirname(current_dir)
                
                # Stop if we reach the root directory
                if parent_dir == current_dir:
                    break
                current_dir = parent_dir
            
            # Create the package name and make sure the parent directory is in sys.path
            if package_parts:
                package_name = ".".join(package_parts)
                # Add the parent of the top-level package to sys.path
                parent_of_package = os.path.dirname(current_dir)
                if parent_of_package not in sys.path:
                    sys.path.insert(0, parent_of_package)
            else:
                # If no package structure detected, treat as standalone module
                package_name = ""
                # Add the module directory to path so sibling modules can be imported
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
            
            # Set the package attribute to enable relative imports
            if package_name:
                module.__package__ = package_name
            
            # Execute the module
            spec.loader.exec_module(module)
            return module
            
        except Exception as e:
            if "attempted relative import" in str(e):
                # More helpful error message for relative import issues
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
        from model_checker.builder.iterate import ModelIterator
        import sys
        
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
            # Create iterator and find additional models
            iterator = ModelIterator(example)
            model_structures = iterator.iterate()
            
            # Skip the first model which is already printed
            # Track distinct models for numbering
            distinct_count = 1
            total_distinct = iterator.distinct_models_found
            
            for i, structure in enumerate(model_structures[1:], start=2):
                # Only display non-isomorphic models with their differences
                if not hasattr(structure, '_is_isomorphic') or not structure._is_isomorphic:
                    distinct_count += 1
                    
                    # Skip printing differences directly - they will be printed by print_model
                    # through model_structure.print_to()
                    
                    # Print the new model header with the correct denominator
                    print(f"\nMODEL {distinct_count}/{total_distinct}")
                    
                    # Set the current model structure and print it
                    example.model_structure = structure
                    
                    # Mark the last model to prevent partial output issues
                    if distinct_count == total_distinct:
                        structure._is_last_model = True
                        
                    example.print_model(f"{example_name}", theory_name)
                    
                # For isomorphic models that are skipped, we could optionally add a subtle indicator
                # Uncomment to show skipped models
                # elif hasattr(structure, '_is_isomorphic') and structure._is_isomorphic:
                #     print(f"\n(Skipped isomorphic model variant {i})")
            
            # Print summary after all models have been displayed
            print(f"\nFound {iterator.distinct_models_found} distinct models out of {iterator.checked_model_count} checked.")
            
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
        
        for example_name, example_case in self.example_range.items():
            for theory_name, semantic_theory in self.semantic_theories.items():
                # Make setting reset for each semantic_theory
                example_copy = list(example_case)
                example_copy[2] = example_case[2].copy()
                
                # Process the example with our new unified approach
                # This handles both single models and iterations consistently
                self.process_example(example_name, example_copy, theory_name, semantic_theory)
