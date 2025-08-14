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
        self.progress = self.iterator_core.progress
        
        # Initialize search progress (for future progress system updates)
        self.search_progress = None
        
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
                timeout = self.settings.get('iteration_timeout', self.settings.get('timeout', 300))  # Default 5 minutes
                if elapsed > timeout:
                    logger.warning(f"Iteration timeout ({timeout}s) reached")
                    self.debug_messages.append(f"Iteration timeout ({timeout}s) reached")
                    break
                
                # Model number we're searching for
                model_number = len(self.model_structures) + 1
                
                # Track search start time
                search_start_time = time.time()
                
                # Update old progress system if still in use (only if no unified progress)
                if not self.search_progress:
                    self.progress.update(
                        len(self.model_structures), 
                        self.checked_model_count
                    )
                
                # Start search with new progress system if available
                if self.search_progress:
                    self.search_progress.start_search(model_number)
                
                logger.info(f"Searching for model {model_number}/{self.max_iterations}...")
                
                try:
                    # Generate constraints to exclude previous models
                    extended_constraints = self.constraint_generator.create_extended_constraints(self.found_models)
                    
                    # Check satisfiability with new constraints
                    check_result = self.constraint_generator.check_satisfiability(extended_constraints)
                    self.checked_model_count += 1
                    
                    if check_result != 'sat':
                        logger.info(f"No more models found (solver returned {check_result})")
                        self.debug_messages.append(f"No more models found (solver returned {check_result})")
                        # Complete search as not found
                        if self.search_progress:
                            self.search_progress.complete_search(model_number, found=False)
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
                                self.search_progress.complete_search(model_number, found=False)
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
                                self.search_progress.complete_search(model_number, found=False)
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
                                self.search_progress.complete_search(model_number, found=False)
                            break
                        continue
                        
                    # Check for isomorphism with previous models
                    is_isomorphic, isomorphic_model = self.isomorphism_checker.check_isomorphism(
                        new_structure, new_model, self.model_structures, self.found_models
                    )
                    
                    if is_isomorphic:
                        logger.info(f"Found isomorphic model #{self.checked_model_count} - will try different constraints")
                        # Generate stronger constraint to avoid this specific isomorphic model
                        stronger_constraint = self.constraint_generator.create_stronger_constraint(isomorphic_model)
                        if stronger_constraint is not None:
                            extended_constraints.append(stronger_constraint)
                        continue
                        
                    # Found a genuinely new model
                    consecutive_invalid_count = 0  # Reset counter
                    self.found_models.append(new_model)
                    
                    # Track search timing
                    search_duration = time.time() - search_start_time
                    new_structure._found_at = time.time()
                    new_structure._search_duration = search_duration
                    
                    self.model_structures.append(new_structure)
                    self.current_iteration += 1
                    
                    # Complete search as found
                    if self.search_progress:
                        self.search_progress.complete_search(model_number, found=True)
                    
                    # Calculate differences from previous model
                    if len(self.model_structures) >= 2:
                        differences = self.difference_calculator.calculate_differences(
                            new_structure, self.model_structures[-2]
                        )
                    else:
                        differences = {}
                    
                    # Add to statistics
                    self.stats.add_model(new_structure, differences)
                    
                    logger.info(f"Found distinct model #{len(self.model_structures)}")
                    
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
                self.progress.finish()
            # New progress is managed by BuildModule
            
        # Final summary
        elapsed_time = self.termination_manager.get_elapsed_time()
        found_count = len(self.model_structures)
        
        if found_count == self.max_iterations:
            logger.info(f"Successfully found all {self.max_iterations} requested models")
        else:
            logger.info(f"Found {found_count}/{self.max_iterations} distinct models.")
            
        self.stats.set_completion_time(elapsed_time)
        
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
                timeout = self.settings.get('iteration_timeout', self.settings.get('timeout', 300))  # Default 5 minutes
                if elapsed > timeout:
                    logger.warning(f"Iteration timeout ({timeout}s) reached")
                    self.debug_messages.append(f"Iteration timeout ({timeout}s) reached")
                    break
                
                # Update progress
                self.progress.update(
                    len(self.model_structures), 
                    self.checked_model_count
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
    
