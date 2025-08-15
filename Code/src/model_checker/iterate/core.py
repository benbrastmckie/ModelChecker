"""Base implementation for model iteration.

This module provides the orchestrating BaseModelIterator class that coordinates
between the modular components for finding multiple semantically distinct models.

The iteration framework delegates to specialized modules:
- iterator.py: Main iteration loop and control flow
- constraints.py: Constraint generation and management  
- models.py: Model creation and validation (including difference calculation)
- isomorphism.py: Graph-based isomorphism detection
- iteration_control.py: Termination logic and result formatting
- metrics.py: Progress tracking and statistics
"""

import logging
import time
import sys
from model_checker.iterate.iterator import IteratorCore
from model_checker.iterate.constraints import ConstraintGenerator
from model_checker.iterate.models import ModelBuilder, DifferenceCalculator
from model_checker.iterate.graph import IsomorphismChecker
from model_checker.iterate.metrics import TerminationManager, ResultFormatter
from model_checker.iterate.statistics import SearchStatistics, IterationReportGenerator

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[ITERATION] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.ERROR)  # Changed to ERROR to see full tracebacks


class BaseModelIterator:
    """Orchestrating class for model iteration using modular components.
    
    This class coordinates between specialized modules to provide the complete
    iteration functionality while maintaining a clean separation of concerns.
    
    Attributes:
        build_example: The BuildExample instance with the initial model
        max_iterations: Maximum number of models to find
        found_models: List of Z3 models found so far
        model_structures: List of model structures found so far
        current_iteration: Current iteration count
        settings: Validated iteration settings
    """
    
    def __init__(self, build_example):
        """Initialize with a BuildExample that already has a valid model.
        
        Args:
            build_example: BuildExample instance with a valid model
            
        Raises:
            ValueError: If the build_example has no valid model
            TypeError: If build_example is not a BuildExample instance
        """
        # Initialize the core iterator component
        self.iterator_core = IteratorCore(build_example)
        
        # Expose key attributes for compatibility
        self.build_example = self.iterator_core.build_example
        self.settings = self.iterator_core.settings
        self.max_iterations = self.iterator_core.max_iterations
        self.current_iteration = self.iterator_core.current_iteration
        self.found_models = self.iterator_core.found_models
        self.model_structures = self.iterator_core.model_structures
        self.debug_messages = self.iterator_core.debug_messages
        self.checked_model_count = self.iterator_core.checked_model_count
        self.isomorphic_model_count = self.iterator_core.isomorphic_model_count
        self.search_stats = self.iterator_core.search_stats
        self.current_search_skipped = self.iterator_core.current_search_skipped
        self.current_search_start = self.iterator_core.current_search_start
        self.current_search_checked = self.iterator_core.current_search_checked
        
        # Initialize component modules
        self.constraint_generator = ConstraintGenerator(build_example)
        self.model_builder = ModelBuilder(build_example)
        self.isomorphism_checker = IsomorphismChecker()
        self.termination_manager = TerminationManager(self.settings)
        self.difference_calculator = DifferenceCalculator()
        self.result_formatter = ResultFormatter()
        
        # Create solver reference for compatibility
        self.solver = self.constraint_generator.solver
        
        # Initialize statistics and progress (delegated to IteratorCore)
        self.stats = self.iterator_core.stats
        
        # Use unified progress if provided, otherwise use no-op stub
        self.search_progress = getattr(build_example, '_unified_progress', None)
        if self.search_progress:
            # Disable old progress system
            self.progress = None
        else:
            # Create no-op stub for backward compatibility
            class NoOpProgress:
                def update(self, *args, **kwargs): pass
                def finish(self, *args, **kwargs): pass
            self.progress = NoOpProgress()
        
        # Initialize isomorphism cache (formerly model_graphs)
        self.model_graphs = []
        
        logger.debug(f"BaseModelIterator initialized with {self.max_iterations} max iterations")
    
    def iterate(self):
        """Find multiple distinct models up to max_iterations.
        
        This method orchestrates the complete iteration process by delegating
        to the specialized modular components while using the IteratorCore
        for debug message collection.
        
        Returns:
            list: All found model structures (including the initial one)
        """
        # Consume the generator to build a list for backward compatibility
        models = list(self.iterate_generator())
        
        # Include the initial model if we have one
        if self.build_example.model_structure.z3_model_status and len(self.model_structures) == 0:
            # If generator didn't run (e.g., max_iterations=1), include initial model
            return [self.build_example.model_structure]
        
        return self.model_structures
    
    def iterate_generator(self):
        """Generator version of iterate that yields models incrementally.
        
        This hybrid approach maintains internal state (model_structures, found_models)
        for constraint generation and isomorphism checking while yielding models
        as they are found.
        
        Yields:
            ModelStructure: Each model as it's found
            
        Note:
            Internal state is still maintained for correctness. The generator
            interface provides incremental delivery while preserving the
            necessary history for constraint generation.
        """
        # Proceed only if first model was successful
        if not self.build_example.model_structure.z3_model_status:
            logger.error("Cannot iterate - first model was not satisfiable")
            return
            
        # Single model case - no iteration needed
        if self.max_iterations == 1:
            logger.debug("Single model requested - no iteration needed")
            return
        
        logger.info(f"Starting generator iteration to find {self.max_iterations} models")
        
        # Check if NetworkX is available for isomorphism detection
        if hasattr(self.isomorphism_checker, 'get_cache_stats'):
            stats = self.isomorphism_checker.get_cache_stats()
            if not stats.get('has_networkx', True):
                logger.warning(
                    "NetworkX is not installed. Isomorphism detection is disabled, "
                    "which may result in finding duplicate models. "
                    "To enable isomorphism detection, install NetworkX: pip install networkx"
                )
        
        # Start timing
        self.termination_manager.start_timing()
        iteration_start_time = time.time()
        
        consecutive_invalid_count = 0
        MAX_CONSECUTIVE_INVALID = self.settings.get('max_invalid_attempts', 20)
        
        # Initialize search for model 2
        self.current_search_start = time.time()
        self.current_search_checked = 0
        self.current_search_skipped = 0
        
        # Track which model we're currently searching for
        current_search_model = 0
        
        try:
            while self.current_iteration < self.max_iterations:
                # Check termination conditions
                should_terminate, reason = self.termination_manager.should_terminate(
                    self.current_iteration, self.max_iterations, 
                    consecutive_invalid_count, self.checked_model_count
                )
                
                if should_terminate:
                    logger.info(reason)
                    break
                
                # Model number we're searching for
                model_number = len(self.model_structures) + 1
                
                # Check timeout for current model search
                elapsed = time.time() - self.current_search_start
                timeout = self.settings.get('max_time', 300)  # Default 5 minutes
                if elapsed > timeout:
                    logger.warning(f"Model {model_number} search timeout ({timeout}s) reached")
                    self.debug_messages.append(f"Model {model_number} search timeout ({timeout}s) reached")
                    
                    # Record incomplete search due to timeout
                    # Use exactly the timeout duration, not total elapsed time
                    search_duration = timeout
                    self.search_stats.append(SearchStatistics(
                        model_number=model_number,
                        found=False,
                        isomorphic_skipped=self.current_search_skipped,
                        models_checked=self.current_search_checked,
                        search_duration=search_duration,
                        termination_reason=f"timeout after {timeout}s"
                    ))
                    
                    # Complete the progress bar for this model search
                    if self.search_progress:
                        self.search_progress.complete_model_search(found=False)
                    
                    break
                
                # Update old progress system if still in use (only if no unified progress)
                if not self.search_progress:
                    self.progress.update(
                        len(self.model_structures) + 1,  # Show the model number we're looking for
                        self.current_search_skipped
                    )
                
                # Start search with new progress system if available (only if not already searching for this model)
                if self.search_progress and current_search_model != model_number:
                    # Pass the current_search_start time to progress for synchronization
                    self.search_progress.start_model_search(model_number, start_time=self.current_search_start)
                    current_search_model = model_number
                
                logger.info(f"Searching for model {model_number}/{self.max_iterations}...")
                
                try:
                    # Generate constraints to exclude previous models
                    extended_constraints = self.constraint_generator.create_extended_constraints(self.found_models)
                    
                    # Check satisfiability with new constraints
                    check_result = self.constraint_generator.check_satisfiability(extended_constraints)
                    self.checked_model_count += 1
                    self.current_search_checked += 1
                    
                    # Update progress with checked count
                    if self.search_progress:
                        self.search_progress.model_checked()
                    
                    if check_result != 'sat':
                        logger.info(f"No more models found (solver returned {check_result})")
                        self.debug_messages.append(f"No more models found (solver returned {check_result})")
                        
                        # Record incomplete search due to exhaustion
                        search_duration = time.time() - self.current_search_start
                        self.search_stats.append(SearchStatistics(
                            model_number=model_number,
                            found=False,
                            isomorphic_skipped=self.current_search_skipped,
                            models_checked=self.current_search_checked,
                            search_duration=search_duration,
                            termination_reason="exhausted search space"
                        ))
                        
                        # Complete search as not found
                        if self.search_progress:
                            self.search_progress.complete_model_search(found=False)
                        break
                        
                    # Get the new model
                    new_model = self.constraint_generator.get_model()
                    if new_model is None:
                        logger.warning("Solver returned sat but no model available")
                        self.debug_messages.append("Solver returned sat but no model available")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive invalid models - stopping iteration")
                            self.debug_messages.append("Too many consecutive invalid models - stopping iteration")
                            # Complete search as not found
                            if self.search_progress:
                                self.search_progress.complete_model_search(found=False)
                            break
                        continue
                        
                    # Build model structure for the new model
                    new_structure = self.model_builder.build_new_model_structure(new_model)
                    
                    if new_structure is None:
                        logger.warning("Failed to build model structure for new model")
                        self.debug_messages.append("Failed to build model structure for new model")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive model building failures - stopping iteration")
                            self.debug_messages.append("Too many consecutive model building failures - stopping iteration")
                            # Complete search as not found
                            if self.search_progress:
                                self.search_progress.complete_model_search(found=False)
                            break
                        continue
                    
                    # Check for invalid models (e.g., no world states)
                    if hasattr(new_structure, 'z3_world_states') and len(new_structure.z3_world_states) == 0:
                        logger.warning("Found model with no world states - invalid model")
                        self.debug_messages.append("Found model with no world states - invalid model")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive invalid models - stopping iteration")
                            self.debug_messages.append("Too many consecutive invalid models - stopping iteration")
                            # Complete search as not found
                            if self.search_progress:
                                self.search_progress.complete_model_search(found=False)
                            break
                        continue
                        
                    # Check for isomorphism with previous models
                    is_isomorphic, isomorphic_model = self.isomorphism_checker.check_isomorphism(
                        new_structure, new_model, self.model_structures, self.found_models
                    )
                    
                    if is_isomorphic:
                        self.isomorphic_model_count += 1
                        self.current_search_skipped += 1
                        
                        # Update progress with skipped count
                        if self.search_progress:
                            self.search_progress.model_skipped_isomorphic()
                        
                        logger.info(f"Found isomorphic model #{self.checked_model_count} - will try different constraints")
                        # Generate stronger constraint to avoid this specific isomorphic model
                        stronger_constraint = self.constraint_generator.create_stronger_constraint(isomorphic_model)
                        if stronger_constraint is not None:
                            extended_constraints.append(stronger_constraint)
                        continue
                        
                    # Found a genuinely new model
                    consecutive_invalid_count = 0  # Reset counter
                    
                    # Record search statistics for this model
                    search_duration = time.time() - self.current_search_start
                    self.search_stats.append(SearchStatistics(
                        model_number=model_number,
                        found=True,
                        isomorphic_skipped=self.current_search_skipped,
                        models_checked=self.current_search_checked,
                        search_duration=search_duration
                    ))
                    
                    self.found_models.append(new_model)
                    
                    # Track search timing
                    new_structure._found_at = time.time()
                    new_structure._search_duration = search_duration
                    
                    self.model_structures.append(new_structure)
                    self.current_iteration += 1
                    
                    # Reset for next search
                    self.current_search_skipped = 0
                    self.current_search_checked = 0
                    self.current_search_start = time.time()
                    
                    # Complete search as found
                    if self.search_progress:
                        self.search_progress.complete_model_search(found=True)
                    
                    # Calculate differences from previous model
                    if len(self.model_structures) >= 2:
                        differences = self.difference_calculator.calculate_differences(
                            new_structure, self.model_structures[-2]
                        )
                    else:
                        differences = {}
                    
                    # Store differences on the model structure for access
                    new_structure.model_differences = differences
                    
                    # Add to statistics
                    self.stats.add_model(new_structure, differences)
                    
                    logger.info(f"Found distinct model #{len(self.model_structures)}")
                    
                    # Clear the progress line before yielding
                    if not self.search_progress:
                        # Just add a newline to move past the progress bar
                        sys.stdout.write("\n")
                        sys.stdout.flush()
                    
                    # YIELD the model instead of just collecting
                    yield new_structure
                    
                except Exception as e:
                    logger.error(f"Error during iteration: {str(e)}")
                    self.debug_messages.append(f"Iteration error: {str(e)}")
                    break
                    
        except KeyboardInterrupt:
            logger.info("Iteration interrupted by user")
            
        finally:
            # Finish old progress (only if no unified progress)
            if not self.search_progress:
                # Check if we added extra space after the last model
                # If iterate was requested but we found fewer models, BuildModule
                # may have added extra space after what turned out to be the last model
                found_all_requested = len(self.model_structures) >= self.max_iterations
                self.progress.finish(add_newline=found_all_requested)
            # New progress is managed by BuildModule
            
        # Final summary
        elapsed_time = self.termination_manager.get_elapsed_time()
        found_count = len(self.model_structures)
        
        if found_count == self.max_iterations:
            logger.info(f"Successfully found all {self.max_iterations} requested models")
        else:
            logger.info(f"Found {found_count}/{self.max_iterations} distinct models.")
            
        self.stats.set_completion_time(elapsed_time)
        
        # Ensure any active progress bars are properly completed before printing the report
        if self.search_progress:
            # Check if there's an active progress bar that wasn't completed
            if self.search_progress.model_progress_bars:
                last_bar = self.search_progress.model_progress_bars[-1]
                if hasattr(last_bar, 'active') and last_bar.active:
                    # Force complete any remaining active progress bar
                    last_bar.complete(False)
        
        # Generate and print detailed report
        report_generator = IterationReportGenerator()
        # Get initial model search time - use total search time to match progress bar
        initial_time = getattr(self.build_example.model_structure, '_total_search_time',
                              getattr(self.build_example.model_structure, 'z3_model_runtime', 0.0))
        report = report_generator.generate_report(
            self.search_stats, 
            self.max_iterations, 
            elapsed_time,
            initial_time
        )
        
        # Check if we need extra spacing before the iteration report
        # If the last search timed out, the progress bar was cleared leaving a blank line
        # Otherwise, we need to add a blank line after the last model's separator
        needs_spacing = True
        if self.search_stats:
            last_search = self.search_stats[-1]
            if last_search.termination_reason and "timeout" in last_search.termination_reason:
                needs_spacing = False  # Timeout already created spacing
        
        # Add spacing if needed
        if needs_spacing:
            sys.stdout.write("\n")
        
        # Print report
        sys.stdout.write(report)
        sys.stdout.write("\n")  # Add final newline after report
        
        # Sync the debug messages back to IteratorCore
        self.iterator_core.debug_messages = self.debug_messages
    
    def _orchestrated_iterate(self):
        """Orchestrate the iteration using modular components."""
        # Proceed only if first model was successful
        if not self.build_example.model_structure.z3_model_status:
            logger.error("Cannot iterate - first model was not satisfiable")
            return self.model_structures
            
        # Single model case - no iteration needed
        if self.max_iterations == 1:
            logger.debug("Single model requested - no iteration needed")
            return self.model_structures
        
        logger.info(f"Starting iteration to find {self.max_iterations} models")
        
        # Check if NetworkX is available for isomorphism detection
        if hasattr(self.isomorphism_checker, 'get_cache_stats'):
            stats = self.isomorphism_checker.get_cache_stats()
            if not stats.get('has_networkx', True):
                logger.warning(
                    "NetworkX is not installed. Isomorphism detection is disabled, "
                    "which may result in finding duplicate models. "
                    "To enable isomorphism detection, install NetworkX: pip install networkx"
                )
        
        # Start timing
        self.termination_manager.start_timing()
        iteration_start_time = time.time()
        
        consecutive_invalid_count = 0
        MAX_CONSECUTIVE_INVALID = self.settings.get('max_invalid_attempts', 20)
        
        try:
            while self.current_iteration < self.max_iterations:
                # Check termination conditions
                should_terminate, reason = self.termination_manager.should_terminate(
                    self.current_iteration, self.max_iterations, 
                    consecutive_invalid_count, self.checked_model_count
                )
                
                if should_terminate:
                    logger.info(reason)
                    break
                
                # Check timeout first
                elapsed = time.time() - iteration_start_time
                timeout = self.settings.get('max_time', 300)  # Default 5 minutes
                if elapsed > timeout:
                    logger.warning(f"Iteration timeout ({timeout}s) reached")
                    self.debug_messages.append(f"Iteration timeout ({timeout}s) reached")
                    break
                
                # Update progress
                self.progress.update(
                    len(self.model_structures) + 1,  # Show the model number we're looking for
                    self.isomorphic_model_count
                )
                
                logger.info(f"Searching for model {len(self.model_structures) + 1}/{self.max_iterations}...")
                
                try:
                    # Generate constraints to exclude previous models
                    extended_constraints = self.constraint_generator.create_extended_constraints(self.found_models)
                    
                    # Check satisfiability with new constraints
                    check_result = self.constraint_generator.check_satisfiability(extended_constraints)
                    self.checked_model_count += 1
                    
                    if check_result != 'sat':
                        logger.info(f"No more models found (solver returned {check_result})")
                        self.debug_messages.append(f"No more models found (solver returned {check_result})")
                        break
                        
                    # Get the new model
                    new_model = self.constraint_generator.get_model()
                    if new_model is None:
                        logger.warning("Solver returned sat but no model available")
                        self.debug_messages.append("Solver returned sat but no model available")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive invalid models - stopping iteration")
                            self.debug_messages.append("Too many consecutive invalid models - stopping iteration")
                            break
                        continue
                        
                    # Build model structure for the new model
                    new_structure = self.model_builder.build_new_model_structure(new_model)
                    
                    if new_structure is None:
                        logger.warning("Failed to build model structure for new model")
                        self.debug_messages.append("Failed to build model structure for new model")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive model building failures - stopping iteration")
                            self.debug_messages.append("Too many consecutive model building failures - stopping iteration")
                            break
                        continue
                    
                    # Check for invalid models (e.g., no world states)
                    if hasattr(new_structure, 'z3_world_states') and len(new_structure.z3_world_states) == 0:
                        logger.warning("Found model with no world states - invalid model")
                        self.debug_messages.append("Found model with no world states - invalid model")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive invalid models - stopping iteration")
                            self.debug_messages.append("Too many consecutive invalid models - stopping iteration")
                            break
                        continue
                        
                    # Check for isomorphism with previous models
                    is_isomorphic, isomorphic_model = self.isomorphism_checker.check_isomorphism(
                        new_structure, new_model, self.model_structures, self.found_models
                    )
                    
                    if is_isomorphic:
                        self.isomorphic_model_count += 1
                        self.current_search_skipped += 1
                        
                        # Update progress with skipped count
                        if self.search_progress:
                            self.search_progress.model_skipped_isomorphic()
                        
                        logger.info(f"Found isomorphic model #{self.checked_model_count} - will try different constraints")
                        # Generate stronger constraint to avoid this specific isomorphic model
                        stronger_constraint = self.constraint_generator.create_stronger_constraint(isomorphic_model)
                        if stronger_constraint is not None:
                            extended_constraints.append(stronger_constraint)
                        continue
                        
                    # Found a genuinely new model
                    consecutive_invalid_count = 0  # Reset counter
                    self.found_models.append(new_model)
                    self.model_structures.append(new_structure)
                    self.current_iteration += 1
                    
                    # Calculate differences from previous model
                    if len(self.model_structures) >= 2:
                        differences = self.difference_calculator.calculate_differences(
                            new_structure, self.model_structures[-2]
                        )
                    else:
                        differences = {}
                    
                    # Store differences on the model structure for access
                    new_structure.model_differences = differences
                    
                    # Add to statistics
                    self.stats.add_model(new_structure, differences)
                    
                    logger.info(f"Found distinct model #{len(self.model_structures)}")
                    
                except Exception as e:
                    logger.error(f"Error during iteration: {str(e)}")
                    self.debug_messages.append(f"Iteration error: {str(e)}")
                    break
                    
        except KeyboardInterrupt:
            logger.info("Iteration interrupted by user")
            
        finally:
            self.progress.finish()
            
        # Final summary
        elapsed_time = self.termination_manager.get_elapsed_time()
        found_count = len(self.model_structures)
        
        if found_count == self.max_iterations:
            logger.info(f"Successfully found all {self.max_iterations} requested models")
        else:
            logger.info(f"Found {found_count}/{self.max_iterations} distinct models.")
            
        self.stats.set_completion_time(elapsed_time)
        return self.model_structures
    
    def get_debug_messages(self):
        """Get all debug messages collected during iteration.
        
        Returns:
            list: List of debug message strings
        """
        return self.iterator_core.get_debug_messages()
    
    def get_iteration_summary(self):
        """Get summary statistics for the iteration.
        
        Returns:
            dict: Summary statistics
        """
        return self.iterator_core.get_iteration_summary()
    
    def print_iteration_summary(self):
        """Print a summary of the iteration results."""
        self.iterator_core.print_iteration_summary()
    
    def reset_iterator(self):
        """Reset the iterator to initial state.
        
        This removes all models except the first one and resets counters.
        Useful for re-running iterations with different settings.
        """
        # Reset core components
        self.iterator_core.reset_iterator()
        
        # Reset our exposed attributes
        self.current_iteration = self.iterator_core.current_iteration
        self.found_models = self.iterator_core.found_models
        self.model_structures = self.iterator_core.model_structures
        self.debug_messages = self.iterator_core.debug_messages
        self.checked_model_count = self.iterator_core.checked_model_count
        
        # Reset modular components
        self.isomorphism_checker.clear_cache()
        self.model_graphs = []
        
        # Reinitialize termination manager with fresh settings
        self.termination_manager = TerminationManager(self.settings)
        
        logger.debug("BaseModelIterator reset to initial state")
    
    
    def _create_difference_constraint(self, previous_models):
        """Theory-specific constraint creation method.
        
        This method should be overridden by theory-specific implementations
        to provide custom difference constraint logic.
        
        Args:
            previous_models: List of Z3 models to differentiate from
            
        Returns:
            z3.BoolRef: Difference constraint
            
        Raises:
            NotImplementedError: If not overridden by subclass
        """
        raise NotImplementedError("Theory-specific implementation required for _create_difference_constraint")
    
    def _create_non_isomorphic_constraint(self, isomorphic_model):
        """Theory-specific non-isomorphic constraint creation method.
        
        This method should be overridden by theory-specific implementations
        to provide custom non-isomorphic constraint logic.
        
        Args:
            isomorphic_model: Z3 model that was found to be isomorphic
            
        Returns:
            z3.BoolRef: Non-isomorphic constraint
            
        Raises:
            NotImplementedError: If not overridden by subclass
        """
        raise NotImplementedError("Theory-specific implementation required for _create_non_isomorphic_constraint")
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Theory-specific stronger constraint creation method.
        
        This method should be overridden by theory-specific implementations
        to provide custom stronger constraint logic.
        
        Args:
            isomorphic_model: Z3 model that was found to be isomorphic
            
        Returns:
            z3.BoolRef: Stronger constraint
            
        Raises:
            NotImplementedError: If not overridden by subclass
        """
        raise NotImplementedError("Theory-specific implementation required for _create_stronger_constraint")
    
