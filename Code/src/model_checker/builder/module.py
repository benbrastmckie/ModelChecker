"""BuildModule implementation for managing model checking examples.

This module provides the BuildModule class for loading and executing model checking 
examples from Python modules. It handles dynamic module loading, configuration 
settings, and coordinating the model checking process.
"""

import os
import importlib.util
import time
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
        
        # Create runner instance
        from model_checker.builder.runner import ModelRunner
        self.runner = ModelRunner(self)
        
        # Create comparison instance if in comparison mode
        if hasattr(module_flags, 'comparison') and module_flags.comparison:
            from model_checker.builder.comparison import ModelComparison
            self.comparison = ModelComparison(self)
        
        # Create translation instance
        from model_checker.builder.translation import OperatorTranslation
        self.translation = OperatorTranslation()

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
        # Delegate to translation module
        return self.translation.translate(example_case, dictionary)
    
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
        # Delegate to translation module
        return self.translation.translate_example(example_case, semantic_theories)

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
        # Delegate to runner
        return self.runner.run_model_check(example_case, example_name, theory_name, semantic_theory)
    
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
        # Delegate to runner
        return self.runner.try_single_N(theory_name, semantic_theory, example_case)
    
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
        # Delegate to the runner's static function
        from model_checker.builder.runner import try_single_N_static
        return try_single_N_static(theory_name, theory_config, example_case)
    
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
        # Delegate to comparison module
        if not hasattr(self, 'comparison'):
            from model_checker.builder.comparison import ModelComparison
            self.comparison = ModelComparison(self)
        return self.comparison.compare_semantics(example_theory_tuples)
    
    def run_comparison(self):
        """Compare different semantic theories by running examples and printing results.
        
        Iterates through each example in example_range and runs it against all semantic theories.
        For each example:
        1. Prints example name and details (premises and conclusions)
        2. Translates operators according to each theory's dictionary
        3. Compares semantic theories by finding maximum model sizes
        4. Prints results showing which theories could handle larger models
        """
        # Delegate to comparison module
        if not hasattr(self, 'comparison'):
            from model_checker.builder.comparison import ModelComparison
            self.comparison = ModelComparison(self)
        return self.comparison.run_comparison()

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
        # Delegate to runner
        return self.runner.process_example(example_name, example_case, theory_name, semantic_theory)
    
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
