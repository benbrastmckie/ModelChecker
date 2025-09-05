"""BuildModule implementation for managing model checking examples.

This module provides the BuildModule class for loading and executing model checking 
examples from Python modules. It handles dynamic module loading, configuration 
settings, and coordinating the model checking process.
"""

# Standard library imports
import os
import sys


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
        
        # Create loader instance first, before loading module
        from model_checker.builder.loader import ModuleLoader
        self.loader = ModuleLoader(self.module_name, self.module_path)
        
        self.module = self.loader.load_module()
        
        # Load core attributes
        self.semantic_theories = self.loader.load_attribute(self.module, "semantic_theories")
        self.example_range = self.loader.load_attribute(self.module, "example_range")

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
                        self.runner.process_example(example_name, example_copy, theory_name, semantic_theory)
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
