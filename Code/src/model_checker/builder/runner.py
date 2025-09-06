"""Model checking execution engine.

This module handles the execution of model checking operations, including
running individual examples, handling iterations, and managing Z3 contexts.
"""

# Standard library imports
import gc
import importlib
import os
import sys
import time

import z3

# Package imports
from ..output.progress import Spinner, UnifiedProgress
from ..syntactic import Syntax

# Local imports
from .serialize import serialize_semantic_theory, deserialize_semantic_theory
from .runner_utils import (
    format_model_output,
    calculate_model_statistics,
    validate_runner_state,
    create_progress_tracker_for_iteration,
    store_timing_information,
    handle_iteration_error,
    extract_iteration_settings,
    prepare_example_case_with_settings,
    calculate_model_differences,
    format_comparison_results,
    validate_iteration_count,
    should_show_progress,
)


def try_single_N_static(theory_name, theory_config, example_case):
    """Static version of try_single_N that can be pickled for multiprocessing.
    
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
            f"N = {settings['N']}.{RESET}\n"
        )
        print(output, end='', flush=True)
    
    return success, run_time


class ModelRunner:
    """Executes model checking for theories."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule for settings.
        
        Args:
            build_module: Parent BuildModule instance for accessing settings
                          and utility methods like translate
        """
        self.build_module = build_module
        self.settings = build_module.general_settings
    
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
            example_case = self.build_module.translation.translate(example_case, dictionary)
        
        # Start progress tracking
        spinner = Spinner()
        spinner.start()
        
        try:
            example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
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
        
        # Different theories have different initialization patterns
        if hasattr(semantics_class, '__name__') and 'Logos' in semantics_class.__name__:
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
        
        self._print_timing_result(model_structure, theory_name, run_time, settings, success)
        return success, run_time
    
    def _print_timing_result(self, model_structure, theory_name, run_time, settings, success):
        """Print timing results for a model checking attempt."""
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
                f"N = {settings['N']}."
            )
    
    def try_single_N_serialized(self, theory_name, theory_config, example_case):
        """Try a single N value with serialized theory config.
        
        This method handles the serialization aspect for ProcessPoolExecutor usage
        while reusing the existing try_single_N logic.
        
        Args:
            theory_name: Name of the theory
            theory_config: Serialized theory configuration dictionary
            example_case: Example case with premises, conclusions, settings
            
        Returns:
            tuple: (success, runtime)
        """
        # Reconstruct the semantic theory from serialized data
        semantic_theory = deserialize_semantic_theory(theory_config)
        
        # Call the original method with reconstructed objects
        return self.try_single_N(theory_name, semantic_theory, example_case)
    
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
        from model_checker.builder.example import BuildExample
        
        # Initialize Z3 context and logging
        self._initialize_z3_context()
        
        # Prepare example case with translations and settings
        example_case = self._prepare_example_case(example_case, semantic_theory)
        
        # Get iteration configuration
        iterate_count = self._get_iterate_count(example_case)
        
        # Handle simple case without iteration
        if iterate_count == 1:
            return self._process_single_model(example_name, example_case, theory_name, semantic_theory)
        
        # Process example with iteration support
        return self._process_with_iterations(example_name, example_case, theory_name, 
                                            semantic_theory, iterate_count)
    
    def _initialize_z3_context(self):
        """Initialize Z3 context and configure logging for clean output."""
        from model_checker.utils import Z3ContextManager
        import logging
        import z3
        
        # Always reset Z3 context at the start of processing a new example
        Z3ContextManager.reset_context()
        
        # Disable all debug logs for cleaner output
        logging.getLogger().setLevel(logging.ERROR)
        # Specifically disable iteration logs
        for logger_name in ["model_checker", "model_checker.builder", "model_checker.iterate"]:
            logging.getLogger(logger_name).setLevel(logging.ERROR)
        
        # Reset Z3 solver to ensure clean state for each example
        z3.reset_params()
        z3.set_param(verbose=0)
    
    def _prepare_example_case(self, example_case, semantic_theory):
        """Apply translations and settings to the example case.
        
        Args:
            example_case: The example case to prepare
            semantic_theory: Theory configuration for translations
            
        Returns:
            Modified example_case with applied translations and settings
        """
        # Apply translation if needed
        dictionary = semantic_theory.get("dictionary", None) 
        if dictionary:
            example_case = self.build_module.translation.translate(example_case, dictionary)
        
        # Apply additional settings from flags
        return prepare_example_case_with_settings(
            example_case, semantic_theory, self.build_module.module_flags
        )
    
    def _get_iterate_count(self, example_case):
        """Extract iteration count from example case settings.
        
        Args:
            example_case: The example case containing settings
            
        Returns:
            int: Number of iterations to perform
        """
        settings = extract_iteration_settings(example_case)
        return settings['iterate']
    
    def _process_single_model(self, example_name, example_case, theory_name, semantic_theory):
        """Process a single model without iteration.
        
        Args:
            example_name: Name of the example
            example_case: Example case data
            theory_name: Name of the theory
            semantic_theory: Theory configuration
            
        Returns:
            BuildExample: The processed example
        """
        from model_checker.builder.example import BuildExample
        
        example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
        self.build_module._capture_and_save_output(example, example_name, theory_name)
        return example
    
    def _process_with_iterations(self, example_name, example_case, theory_name, 
                                semantic_theory, iterate_count):
        """Process example with iteration support and progress tracking.
        
        Args:
            example_name: Name of the example
            example_case: Example case data
            theory_name: Name of the theory
            semantic_theory: Theory configuration
            iterate_count: Number of models to find
            
        Returns:
            BuildExample: The processed example
        """
        from model_checker.builder.example import BuildExample
        
        # Create progress tracker
        progress = self._create_progress_tracker(example_case, iterate_count)
        
        # Process first model with progress tracking
        print()  # Add vertical space before first progress bar
        model_1_start = time.time()
        progress.start_model_search(1, start_time=model_1_start)
        
        example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
        progress.model_checked()
        
        # Store timing information
        self._store_timing_info(example, model_1_start)
        
        # Check if model was found
        if not example.model_structure.z3_model_status:
            progress.complete_model_search(found=False)
            progress.finish()
            self.build_module._capture_and_save_output(example, example_name, theory_name)
            return example
        
        progress.complete_model_search(found=True)
        print()  # Add vertical space after first progress bar
        
        # Set up for iteration
        if iterate_count > 1:
            example._unified_progress = progress
        
        # Handle interactive vs batch mode
        iterate_count = self._handle_iteration_mode(example, example_name, theory_name, 
                                                    iterate_count, progress)
        
        # Process remaining iterations
        try:
            if iterate_count > 1:
                self.process_iterations(example, example_name, example_case, theory_name, 
                                      semantic_theory, iterate_count, progress)
        finally:
            progress.finish()
        
        return example
    
    def _create_progress_tracker(self, example_case, iterate_count):
        """Create a unified progress tracker for model iterations.
        
        Args:
            example_case: Example case with settings
            iterate_count: Total models to find
            
        Returns:
            UnifiedProgress: Progress tracker instance
        """
        return create_progress_tracker_for_iteration(example_case, iterate_count)
    
    def _store_timing_info(self, example, start_time):
        """Store timing information in the example for reporting.
        
        Args:
            example: The BuildExample instance
            start_time: When model search started
        """
        store_timing_information(example.model_structure, start_time)
    
    def _handle_iteration_mode(self, example, example_name, theory_name, iterate_count, progress):
        """Handle interactive vs batch mode for iterations.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            theory_name: Name of the theory
            iterate_count: Current iteration count
            progress: Progress tracker
            
        Returns:
            int: Updated iteration count
        """
        if self.build_module.interactive_manager and self.build_module.interactive_manager.is_interactive():
            # Interactive mode
            self.build_module._capture_and_save_output(example, example_name, theory_name)
            
            user_iterations = self.prompt_for_iterations()
            if user_iterations == 0:
                return 1  # No more iterations
            
            # Override iterate count with user's choice (plus 1 for the model already shown)
            iterate_count = user_iterations + 1
            progress.total_models = iterate_count
            example._unified_progress = progress
        else:
            # Batch mode
            self.build_module._capture_and_save_output(example, example_name, theory_name)
            
            if iterate_count > 1:
                print()  # Add vertical space before iteration starts
        
        return iterate_count
    
    def process_iterations(self, example, example_name, example_case, theory_name, 
                           semantic_theory, iterate_count, progress):
        """Process iterations for an example that supports model iteration.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            example_case: Example case with premises, conclusions, settings  
            theory_name: Name of the theory
            semantic_theory: Theory configuration
            iterate_count: Total number of models to find
            progress: UnifiedProgress instance for tracking
        """
        try:
            # Get the theory-specific iterate_example function
            try:
                # Dynamically discover the theory module from the semantic theory
                module_name = self.build_module.loader.discover_theory_module_for_iteration(theory_name, semantic_theory)
                
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
                return
            
            # Check if theory supports generator interface
            if hasattr(theory_iterate_example, '__wrapped__') and \
               hasattr(theory_iterate_example.__wrapped__, 'returns_generator'):
                # Use generator interface for incremental display
                self._run_generator_iteration(example, theory_iterate_example, example_name, theory_name, iterate_count)
                return
            
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
                        self.build_module._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
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
                        self.build_module._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
                    
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
                self.build_module._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
                
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
        """Get information about why iteration terminated.
        
        Args:
            example: The BuildExample that was iterated
            found_count: Number of models actually found
            requested_count: Number of models requested
            
        Returns:
            str: Human-readable termination reason, or None
        """
        if found_count < requested_count:
            # Try to get reason from iterator if available
            if hasattr(example, '_last_iterator'):
                iterator = example._last_iterator
                reason = self._get_termination_reason(iterator, found_count, requested_count)
                if reason:
                    return reason
            
            # Generic reason
            return f"Found all {found_count} possible models (requested {requested_count})"
        else:
            return f"Found requested {requested_count} models"
    
    def _get_termination_reason(self, iterator, found_count, requested_count):
        """Extract termination reason from iterator if available.
        
        Args:
            iterator: The model iterator instance
            found_count: Number of models found
            requested_count: Number requested
            
        Returns:
            str: Termination reason or None
        """
        if hasattr(iterator, 'termination_reason'):
            return iterator.termination_reason
        elif hasattr(iterator, 'exhausted') and iterator.exhausted:
            return "Search space exhausted"
        elif hasattr(iterator, 'timeout_count') and iterator.timeout_count > 0:
            return f"Stopped after {iterator.timeout_count} timeouts"
        else:
            return None
    
    def run_examples(self):
        """Process and execute each example case with all semantic theories.
        
        Iterates through example cases and theories, translating operators if needed.
        Runs model checking with progress indicator and timeout handling.
        Prints results or timeout message for each example/theory combination.
        """
        # CRITICAL: This method includes the Z3 context isolation logic
        # that prevents state leakage between examples
        
        try:
            for example_name, example_case in self.build_module.example_range.items():
                # Force garbage collection to clean up any lingering Z3 objects
                gc.collect()
                
                # Reset Z3 context to create a fresh environment for this example
                # This is the critical fix for ensuring proper Z3 state isolation
                # Each example gets its own fresh Z3 context, preventing any state leakage
                if hasattr(z3, '_main_ctx'):
                    z3._main_ctx = None
                
                # Force another garbage collection to ensure clean state
                gc.collect()
                
                # Run the system in a clean state
                for theory_name, semantic_theory in self.build_module.semantic_theories.items():
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
            if self.build_module.output_manager.should_save() and self.build_module.output_manager.output_dir is not None:
                self.build_module.output_manager.finalize()
                print(f"\nPartial output saved to: {os.path.abspath(self.build_module.output_manager.output_dir)}")
            sys.exit(1)
                    
        # Finalize output saving if enabled
        if self.build_module.output_manager.should_save():
            self.build_module.output_manager.finalize()
            
            # Only print path if output was actually saved
            if self.build_module.output_manager.output_dir is not None:
                # Get full path for display
                full_path = os.path.abspath(self.build_module.output_manager.output_dir)
                
                # Prompt for directory change
                if self.build_module.interactive_manager:
                    self.build_module.interactive_manager.prompt_change_directory(full_path)
                else:
                    # No interactive manager - show instructions directly
                    print(f"\nOutput saved to: {full_path}")
                    print(f"To change to output directory, run:")
                    print(f"  cd {full_path}")
    
    def prompt_for_iterations(self):
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
                return self.prompt_for_iterations()
            return num_iterations
        except ValueError:
            print("Please enter a valid number or hit return to continue.")
            return self.prompt_for_iterations()