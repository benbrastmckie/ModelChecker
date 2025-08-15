"""Main iteration logic and control flow.

This module contains the core iteration loop and high-level iteration management
for finding multiple semantically distinct models. It coordinates between
constraint generation, model building, and termination logic.
"""

import logging
import sys
import time
from model_checker.iterate.metrics import IterationStatistics
from model_checker.iterate.statistics import SearchStatistics, IterationReportGenerator

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[ITERATION] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.ERROR)


class IteratorCore:
    """Core iteration logic and control flow management."""
    
    def __init__(self, build_example):
        """Initialize iterator with build example.
        
        Args:
            build_example: BuildExample instance with a valid model
        """
        # Model validation
        if not hasattr(build_example, 'model_structure') or build_example.model_structure is None:
            raise ValueError("BuildExample has no model_structure")
            
        if not hasattr(build_example.model_structure, 'z3_model_status') or \
           not build_example.model_structure.z3_model_status:
            raise ValueError("BuildExample does not have a valid model")
            
        if not hasattr(build_example.model_structure, 'z3_model') or \
           build_example.model_structure.z3_model is None:
            raise ValueError("BuildExample has no Z3 model")
            
        # Initialize properties
        self.build_example = build_example
        self.settings = self._get_iteration_settings()
        
        # Debug settings
        logger.debug(f"Settings: {self.settings}")
        logger.debug(f"Original settings: {getattr(build_example, 'settings', {})}")
            
        self.max_iterations = self.settings.get('iterate', 1)
        self.current_iteration = 1  # First model is already found
        
        # Initialize statistics (progress is now handled by UnifiedProgress)
        self.stats = IterationStatistics()
        # Legacy progress attribute kept for compatibility
        self.progress = None
        
        # Store the initial model and model structure
        self.found_models = [build_example.model_structure.z3_model]
        self.model_structures = [build_example.model_structure]
        
        # Initialize diagnostic tracking
        self.debug_messages = []
        self.checked_model_count = 1
        self.isomorphic_model_count = 0  # Track skipped isomorphic models
        
        # Per-search tracking
        self.search_stats = []  # List of per-model search statistics
        self.current_search_skipped = 0  # Isomorphic skipped in current search
        self.current_search_start = None  # Start time of current search
        self.current_search_checked = 0  # Models checked in current search
        
        # Initialize stats for the first model
        self.stats.add_model(self.build_example.model_structure, {})
    
    def iterate(self):
        """Find multiple distinct models up to max_iterations.
        
        Returns:
            list: All found model structures (including the initial one)
        """
        # Proceed only if first model was successful
        if not self.build_example.model_structure.z3_model_status:
            logger.error("Cannot iterate - first model was not satisfiable")
            return self.model_structures
            
        # Single model case - no iteration needed
        if self.max_iterations == 1:
            logger.debug("Single model requested - no iteration needed")
            return self.model_structures
        
        logger.info(f"Starting iteration to find {self.max_iterations} models")
        iteration_start_time = time.time()
        
        # Progress tracking (no explicit start method needed)
        consecutive_invalid_count = 0
        MAX_CONSECUTIVE_INVALID = self.settings.get('max_invalid_attempts', 20)
        
        # Initialize search for model 2
        self.current_search_start = time.time()
        self.current_search_checked = 0
        self.current_search_skipped = 0
        
        try:
            while self.current_iteration < self.max_iterations:
                # Update progress with current search skipped count
                self.progress.update(
                    len(self.model_structures), 
                    self.current_search_skipped
                )
                
                # Check timeout
                elapsed = time.time() - iteration_start_time
                timeout = self.settings.get('iteration_timeout', self.settings.get('timeout', 300))  # Default 5 minutes
                if elapsed > timeout:
                    logger.warning(f"Iteration timeout ({timeout}s) reached")
                    self.debug_messages.append(f"Iteration timeout ({timeout}s) reached")
                    
                    # Record incomplete search due to timeout
                    search_duration = time.time() - self.current_search_start
                    self.search_stats.append(SearchStatistics(
                        model_number=len(self.model_structures) + 1,
                        found=False,
                        isomorphic_skipped=self.current_search_skipped,
                        models_checked=self.current_search_checked,
                        search_duration=search_duration,
                        termination_reason=f"timeout after {timeout}s"
                    ))
                    break
                    
                logger.info(f"Searching for model {len(self.model_structures) + 1}/{self.max_iterations}...")
                
                try:
                    # Generate constraints to exclude previous models
                    from model_checker.iterate.constraints import ConstraintGenerator
                    constraint_gen = ConstraintGenerator(self.build_example)
                    extended_constraints = constraint_gen.create_extended_constraints(self.found_models)
                    
                    # Check satisfiability with new constraints
                    check_result = constraint_gen.check_satisfiability(extended_constraints)
                    self.checked_model_count += 1
                    self.current_search_checked += 1
                    
                    if check_result != 'sat':
                        logger.info(f"No more models found (solver returned {check_result})")
                        self.debug_messages.append(f"No more models found (solver returned {check_result})")
                        
                        # Record incomplete search due to exhaustion
                        search_duration = time.time() - self.current_search_start
                        self.search_stats.append(SearchStatistics(
                            model_number=len(self.model_structures) + 1,
                            found=False,
                            isomorphic_skipped=self.current_search_skipped,
                            models_checked=self.current_search_checked,
                            search_duration=search_duration,
                            termination_reason="exhausted search space"
                        ))
                        break
                        
                    # Get the new model
                    new_model = constraint_gen.get_model()
                    if new_model is None:
                        logger.warning("Solver returned sat but no model available")
                        self.debug_messages.append("Solver returned sat but no model available")
                        consecutive_invalid_count += 1
                        if consecutive_invalid_count >= MAX_CONSECUTIVE_INVALID:
                            logger.error("Too many consecutive invalid models - stopping iteration")
                            self.debug_messages.append("Too many consecutive invalid models - stopping iteration")
                            
                            # Record incomplete search due to invalid models
                            search_duration = time.time() - self.current_search_start
                            self.search_stats.append(SearchStatistics(
                                model_number=len(self.model_structures) + 1,
                                found=False,
                                isomorphic_skipped=self.current_search_skipped,
                                models_checked=self.current_search_checked,
                                search_duration=search_duration,
                                termination_reason="too many consecutive invalid models"
                            ))
                            break
                        continue
                        
                    # Build model structure for the new model
                    from model_checker.iterate.models import ModelBuilder
                    model_builder = ModelBuilder(self.build_example)
                    new_structure = model_builder.build_new_model_structure(new_model)
                    
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
                            
                            # Record incomplete search due to invalid models
                            search_duration = time.time() - self.current_search_start
                            self.search_stats.append(SearchStatistics(
                                model_number=len(self.model_structures) + 1,
                                found=False,
                                isomorphic_skipped=self.current_search_skipped,
                                models_checked=self.current_search_checked,
                                search_duration=search_duration,
                                termination_reason="too many consecutive invalid models"
                            ))
                            break
                        continue
                        
                    # Check for isomorphism with previous models
                    from model_checker.iterate.graph import IsomorphismChecker
                    iso_checker = IsomorphismChecker()
                    is_isomorphic, isomorphic_model = iso_checker.check_isomorphism(
                        new_structure, new_model, self.model_structures, self.found_models
                    )
                    
                    if is_isomorphic:
                        self.isomorphic_model_count += 1
                        self.current_search_skipped += 1
                        logger.info(f"Found isomorphic model #{self.checked_model_count} - will try different constraints")
                        # Generate stronger constraint to avoid this specific isomorphic model
                        stronger_constraint = constraint_gen.create_stronger_constraint(isomorphic_model)
                        if stronger_constraint is not None:
                            extended_constraints.append(stronger_constraint)
                        continue
                        
                    # Found a genuinely new model
                    consecutive_invalid_count = 0  # Reset counter
                    
                    # Record search statistics for this model
                    search_duration = time.time() - self.current_search_start
                    self.search_stats.append(SearchStatistics(
                        model_number=len(self.model_structures) + 1,
                        found=True,
                        isomorphic_skipped=self.current_search_skipped,
                        models_checked=self.current_search_checked,
                        search_duration=search_duration
                    ))
                    
                    self.found_models.append(new_model)
                    self.model_structures.append(new_structure)
                    self.current_iteration += 1
                    
                    # Reset for next search
                    self.current_search_skipped = 0
                    self.current_search_checked = 0
                    self.current_search_start = time.time()
                    
                    # Calculate differences from previous model
                    from model_checker.iterate.models import DifferenceCalculator
                    diff_calc = DifferenceCalculator()
                    differences = diff_calc.calculate_differences(new_structure, self.model_structures[-2])
                    
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
            # Check if we found all requested models
            found_all_requested = len(self.model_structures) >= self.max_iterations
            self.progress.finish(add_newline=found_all_requested)
            
        # Final summary
        elapsed_time = time.time() - iteration_start_time
        found_count = len(self.model_structures)
        
        if found_count == self.max_iterations:
            logger.info(f"Successfully found all {self.max_iterations} requested models")
        else:
            logger.info(f"Found {found_count}/{self.max_iterations} distinct models.")
            
        self.stats.set_completion_time(elapsed_time)
        
        # Generate and print detailed report
        report_generator = IterationReportGenerator()
        # Get initial model search time - prefer z3_model_runtime over _search_duration
        initial_time = getattr(self.build_example.model_structure, 'z3_model_runtime', 
                              getattr(self.build_example.model_structure, '_search_duration', 0.0))
        report = report_generator.generate_report(
            self.search_stats, 
            self.max_iterations, 
            elapsed_time,
            initial_time
        )
        # Print report directly - progress.finish() already added one newline
        sys.stdout.write(report)
        sys.stdout.write("\n")  # Add final newline after report
        
        return self.model_structures
    
    def get_debug_messages(self):
        """Get all debug messages collected during iteration.
        
        Returns:
            list: List of debug message strings
        """
        return self.debug_messages.copy()
    
    def get_iteration_summary(self):
        """Get summary statistics for the iteration.
        
        Returns:
            dict: Summary statistics
        """
        return self.stats.get_summary()
    
    def print_iteration_summary(self):
        """Print a summary of the iteration results."""
        self.stats.print_summary()
    
    def reset_iterator(self):
        """Reset the iterator to initial state.
        
        This removes all models except the first one and resets counters.
        Useful for re-running iterations with different settings.
        """
        # Keep only the first model
        self.found_models = self.found_models[:1]
        self.model_structures = self.model_structures[:1]
        self.current_iteration = 1
        
        # Reset tracking
        self.debug_messages = []
        self.checked_model_count = 1
        
        # Reset statistics (progress is now handled by UnifiedProgress)
        self.stats = IterationStatistics()
        self.stats.add_model(self.build_example.model_structure, {})
        
        logger.debug("Iterator reset to initial state")
    
    def _get_iteration_settings(self):
        """Get and validate iteration settings from the build example.
        
        Returns:
            dict: Validated iteration settings
        """
        settings = getattr(self.build_example, 'settings', {}).copy()
        
        # Set defaults for iteration settings
        defaults = {
            'iterate': 1,
            'timeout': 300,  # 5 minutes default
            'max_consecutive_invalid': 20,
            'enable_progress': True,
            'enable_statistics': True
        }
        
        for key, default_value in defaults.items():
            if key not in settings:
                settings[key] = default_value
        
        # Validation
        if not isinstance(settings['iterate'], int) or settings['iterate'] < 1:
            raise ValueError(f"iterate must be a positive integer, got {settings['iterate']}")
            
        if not isinstance(settings['timeout'], (int, float)) or settings['timeout'] <= 0:
            raise ValueError(f"timeout must be positive, got {settings['timeout']}")
            
        return settings