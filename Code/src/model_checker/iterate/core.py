"""Base implementation for model iteration.

This module provides the abstract base class and theory-agnostic utilities for
finding multiple semantically distinct models for logical examples. Specific
theory implementations extend the BaseModelIterator class to provide
theory-specific functionality.

The iteration framework handles:
1. Creating constraints that ensure each new model differs from previous models
2. Checking for model isomorphism to avoid structural duplicates
3. Managing the iteration process and termination conditions
"""

import z3
import itertools
import time
import traceback
import logging
import sys

from model_checker.builder.example import BuildExample
from model_checker.builder.progress import Spinner
from model_checker.iterate.graph_utils import ModelGraph
from model_checker.iterate.progress import IterationProgress
from model_checker.iterate.stats import IterationStatistics

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[ITERATION] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)

# Check if NetworkX is available for isomorphism checking
try:
    import networkx as nx
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False


class BaseModelIterator:
    """Base class for all model iterators.
    
    This class provides the core iteration framework but relies on 
    theory-specific subclasses to implement certain methods.
    
    Attributes:
        build_example: The BuildExample instance with the initial model
        max_iterations: Maximum number of models to find (from settings)
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
        # Type validation
        if not isinstance(build_example, BuildExample):
            raise TypeError(
                f"Expected BuildExample instance, got {type(build_example).__name__}"
            )
            
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
        
        # Store the initial model and model structure
        self.found_models = [build_example.model_structure.z3_model]
        self.model_structures = [build_example.model_structure]
        
        # Create a persistent solver that will accumulate constraints
        self.solver = self._create_persistent_solver()
        
        # Initialize graph representation for the model
        self.model_graphs = []
        if HAS_NETWORKX:
            try:
                initial_graph = ModelGraph(
                    self.build_example.model_structure,
                    self.found_models[0]
                )
                self.model_graphs.append(initial_graph)
                # Store the graph with the model structure for reference
                self.build_example.model_structure.model_graph = initial_graph
            except Exception as e:
                logger.warning(f"Could not create graph for initial model: {str(e)}")
        
        # Initialize diagnostic tracking
        self.debug_messages = []
        self.checked_model_count = 1
        
        # Initialize isomorphism cache
        self._isomorphism_cache = {}
        self.distinct_models_found = 1
        
        # Initialize statistics tracking
        self.stats = IterationStatistics()
        # Add initial model stats
        self.stats.add_model(self.build_example.model_structure, {})
    
    def _create_persistent_solver(self):
        """Create a persistent solver with the initial model's constraints."""
        # Try to get the solver, fallback to stored_solver if solver was cleaned up
        original_solver = self.build_example.model_structure.solver
        if original_solver is None:
            original_solver = getattr(self.build_example.model_structure, 'stored_solver', None)
            
        if original_solver is None:
            raise RuntimeError("No solver available - both solver and stored_solver are None")
            
        persistent_solver = z3.Solver()
        for assertion in original_solver.assertions():
            persistent_solver.add(assertion)
        return persistent_solver
    
    def iterate(self):
        """Find multiple distinct models up to max_iterations.
        
        Returns:
            list: All found model structures (including the initial one)
        """
        # Proceed only if first model was successful
        if not self.build_example.model_structure.z3_model_status:
            raise RuntimeError("Cannot iterate when no initial model was found")
        
        # Set up timeout for the entire process
        max_time = self.settings.get('max_time', 1.0)
        iteration_timeout = max(max_time * 10, 30.0)
        start_time = time.time()
        
        # Set solver timeout
        solver_timeout = self.settings.get('iteration_solver_timeout', 5000)  # 5 seconds default
        self.solver.set("timeout", solver_timeout)
        
        # Track attempts to escape isomorphic models
        self.escape_attempts = 0
        escape_attempts = self.settings.get('escape_attempts', 3)
        
        # Track consecutive invalid models to prevent infinite loops
        consecutive_invalid = 0
        max_consecutive_invalid = self.settings.get('max_invalid_attempts', 5)
        
        # Initialize progress bar if enabled
        progress = None
        if self.settings.get('show_progress', True):
            progress = IterationProgress(
                self.max_iterations,
                f"Finding {self.max_iterations} models"
            )
            progress.update(self.distinct_models_found, self.checked_model_count)
        
        # Start iteration from second model
        while self.current_iteration < self.max_iterations:
            try:
                # Show progress (store for later display)
                self.debug_messages.append(f"[ITERATION] Searching for model {self.current_iteration + 1}/{self.max_iterations}...")
                
                # Check timeout
                current_time = time.time()
                if current_time - start_time > iteration_timeout:
                    self.debug_messages.append(f"Iteration process exceeded timeout of {iteration_timeout} seconds")
                    self.debug_messages.append(f"[ITERATION] Timeout exceeded after {iteration_timeout} seconds")
                    break
                
                # Create extended constraints requiring difference from all previous models
                try:
                    extended_constraints = self._create_extended_constraints()
                except RuntimeError as e:
                    self.debug_messages.append(f"Could not create extended constraints: {str(e)}")
                    break
                
                # Solve with extended constraints
                check_start = time.time()
                result = self.solver.check()
                check_time = time.time() - check_start
                
                # Log slow checks
                if check_time > 1.0:
                    logger.warning(f"Solver check took {check_time:.2f} seconds for model {self.current_iteration + 1}")
                else:
                    logger.debug(f"Solver check took {check_time:.2f} seconds, result: {result}")
                
                if result != z3.sat:
                    # Better error messages based on context
                    if self.current_iteration == 1:
                        message = "No additional models exist that satisfy all constraints"
                    else:
                        message = f"Found {self.distinct_models_found} distinct models (requested {self.max_iterations})"
                    
                    self.debug_messages.append(f"[ITERATION] {message}")
                    # Don't finish progress here - let it finish at the end
                    break
                
                # Get the new model
                new_model = self.solver.model()
                self.checked_model_count += 1
                
                # Update progress
                if progress:
                    progress.update(self.distinct_models_found, self.checked_model_count)
                
                # Build a completely new model structure with the extended constraints
                new_structure = self._build_new_model_structure(new_model)
                
                if not new_structure:
                    self.debug_messages.append("Could not create new model structure, stopping iteration")
                    break
                
                # Validate the new model has at least one possible world
                if not hasattr(new_structure, 'z3_world_states') or not new_structure.z3_world_states:
                    self.debug_messages.append("Found model with no possible worlds - skipping as invalid")
                    consecutive_invalid += 1
                    self.debug_messages.append(f"[ITERATION] Found invalid model (no possible worlds) - attempt {consecutive_invalid}/{max_consecutive_invalid}")
                    
                    if consecutive_invalid >= max_consecutive_invalid:
                        self.debug_messages.append(f"Found {max_consecutive_invalid} consecutive invalid models - stopping search")
                        self.debug_messages.append(f"[ITERATION] Too many consecutive invalid models ({max_consecutive_invalid}) - no more valid models exist")
                        break
                    
                    # Add constraint to exclude this invalid model
                    logger.debug("Adding constraint to exclude invalid model")
                    self.solver.add(self._create_difference_constraint([new_model]))
                    continue
                
                # Check for isomorphism if NetworkX is available
                is_isomorphic = False
                if HAS_NETWORKX:
                    is_isomorphic = self._check_isomorphism(new_structure, new_model)
                
                if is_isomorphic:
                    # Mark the structure as isomorphic for reference
                    new_structure._is_isomorphic = True
                    logger.debug(f"Found an isomorphic model (check #{self.checked_model_count})")
                    self.debug_messages.append(f"[ITERATION] Found isomorphic model #{self.checked_model_count} - will try different constraints")
                    
                    # Track number of consecutive isomorphic models found
                    if not hasattr(self, '_isomorphic_attempts'):
                        self._isomorphic_attempts = 0
                    self._isomorphic_attempts += 1
                    
                    # If we've found too many isomorphic models in a row, apply stronger constraints
                    iteration_attempts = self.settings.get('iteration_attempts', 5)
                    if self._isomorphic_attempts >= iteration_attempts:
                        self.escape_attempts += 1
                        
                        if self.escape_attempts >= escape_attempts:
                            self.debug_messages.append(f"Made {escape_attempts} attempts to escape isomorphic models without success. Stopping search.")
                            self.debug_messages.append(f"[ITERATION] Exhausted {escape_attempts} escape attempts - no more distinct models found")
                            break
                            
                        # Store the message instead of printing it immediately
                        self.debug_messages.append(f"Skipping after {iteration_attempts} consecutive isomorphic models. Applying stronger constraints (attempt {self.escape_attempts}/{escape_attempts})...")
                        
                        # Create stronger constraints and continue
                        stronger_constraint = self._create_stronger_constraint(new_model)
                        if stronger_constraint is not None:
                            self.solver.add(stronger_constraint)
                            self._isomorphic_attempts = 0  # Reset counter
                            
                            # Add a timeout for this attempt - use a longer timeout for stronger constraints
                            attempt_timeout = min(max_time * 4, 10.0)  # Longer timeout for stronger constraints
                            self.debug_messages.append(f"  Attempting to satisfy stronger constraints (timeout: {attempt_timeout}s)")
                            attempt_start = time.time()
                            
                            # Set solver timeout
                            self.solver.set("timeout", int(attempt_timeout * 1000))
                            
                            # First check immediately
                            result = self.solver.check()
                            if result == z3.sat:
                                self.debug_messages.append("  Found satisfiable model with stronger constraints!")
                                # Continue with the loop to process this model
                                continue
                            
                            # If not immediately satisfiable, try a few more times with short intervals
                            retry_count = 0
                            max_retries = 3
                            while retry_count < max_retries and time.time() - attempt_start < attempt_timeout:
                                retry_count += 1
                                self.debug_messages.append(f"  Retry attempt {retry_count}/{max_retries}...")
                                
                                # Try with different solver seeds or tactics
                                self.solver.push()  # Save the current solver state
                                self.solver.add(z3.Int(f"retry_seed_{retry_count}") == retry_count)  # Add a dummy constraint to change the solver's behavior
                                result = self.solver.check()
                                if result == z3.sat:
                                    self.debug_messages.append("  Found satisfiable model on retry!")
                                    break
                                self.solver.pop()  # Restore the solver state
                                
                                # Brief pause between retries
                                time.sleep(0.1)
                            
                            # If we couldn't satisfy the constraint within timeout, stop
                            if self.solver.check() != z3.sat:
                                self.debug_messages.append("Failed to satisfy stronger constraints, stopping search")
                                self.debug_messages.append(f"[ITERATION] Failed to satisfy stronger constraints - stopping")
                                break
                        else:
                            self.debug_messages.append("Could not create stronger constraints, stopping search")
                            self.debug_messages.append(f"[ITERATION] Could not create stronger constraints - stopping")
                            break
                        # Continue to next iteration to try the stronger constraints
                        continue
                    
                    # Add a non-isomorphism constraint and try again
                    iso_constraint = self._create_non_isomorphic_constraint(new_model)
                    if iso_constraint is not None:  # Check for None explicitly instead of using truth value
                        self.solver.add(iso_constraint)
                        continue  # Skip to next attempt without incrementing
                    else:
                        self.debug_messages.append("Could not create non-isomorphic constraint, stopping search")
                        break
                
                # This is a genuine new model
                new_structure._is_isomorphic = False
                self.distinct_models_found += 1
                
                # Reset counters on successful distinct model
                self._isomorphic_attempts = 0
                self.escape_attempts = 0
                consecutive_invalid = 0  # Reset invalid counter too
                
                # Calculate and store differences for the presentation layer to use
                differences = self._calculate_differences(new_structure, self.model_structures[-1])
                new_structure.model_differences = differences
                # print(f"DEBUG CORE: Setting model_differences = {bool(differences)}, differences = {differences}")
                
                # Store reference to previous structure for comparison
                new_structure.previous_structure = self.model_structures[-1]
                
                # Add the new model and structure to our results
                self.found_models.append(new_model)
                self.model_structures.append(new_structure)
                self.current_iteration += 1
                
                # Add statistics for this model
                self.stats.add_model(new_structure, differences)
                
                # Update progress with new distinct model
                if progress:
                    progress.update(self.distinct_models_found, self.checked_model_count)
                
                # Add the new model to the solver constraints to ensure the next model is different
                self.solver.add(self._create_difference_constraint([new_model]))
                
            except Exception as e:
                self.debug_messages.append(f"Error during iteration: {str(e)}")
                
                # Print the traceback to stderr for debugging but don't show it to the user
                print(traceback.format_exc(), file=sys.stderr)
                break
        
        # Complete progress display
        if progress:
            if self.distinct_models_found == self.max_iterations:
                progress.finish(f"Successfully found all {self.max_iterations} requested models")
            else:
                progress.finish(f"Found {self.distinct_models_found} distinct models (requested {self.max_iterations})")
        
        # Return all model structures without printing summary here
        # Summary will be printed by the presentation layer (process_example)
        return self.model_structures
    
    def get_debug_messages(self):
        """Get all debug messages collected during iteration.
        
        Returns:
            list: List of debug messages to display
        """
        # Filter to only return [ITERATION] messages for user display
        return [msg for msg in self.debug_messages if "[ITERATION]" in msg]
    
    def get_iteration_summary(self):
        """Get a summary of the iteration statistics.
        
        Returns:
            dict: Dictionary containing iteration statistics
        """
        return self.stats.get_summary()
    
    def print_iteration_summary(self):
        """Print a summary of iteration statistics."""
        self.stats.print_summary()
    
    def reset_iterator(self):
        """Reset the iterator to its initial state.
        
        Clears:
        - All found models except the initial one
        - Any added differentiation constraints
        - Iteration counters
        - Status flags
        
        Returns:
            self: For method chaining
        """
        # Keep only the initial model
        if self.found_models:
            initial_model = self.found_models[0]
            self.found_models = [initial_model]
            
        # Keep only the initial model structure
        if self.model_structures:
            initial_structure = self.model_structures[0]
            self.model_structures = [initial_structure]
            
        # Reset all counters and flags
        self.current_iteration = 1
        self._isomorphic_attempts = 0
        self.distinct_models_found = 1
        self.checked_model_count = 1
        self.escape_attempts = 0
        self.debug_messages = []
        
        # Reset solver to original constraints
        self.solver = self._create_persistent_solver()
        
        # Reset graph representations
        if HAS_NETWORKX:
            if self.model_structures:
                # Keep only the initial model graph
                try:
                    initial_structure = self.model_structures[0]
                    initial_model = self.found_models[0]
                    initial_graph = ModelGraph(initial_structure, initial_model)
                    self.model_graphs = [initial_graph]
                except Exception as e:
                    logger.warning(f"Failed to reset model graphs: {str(e)}")
                    self.model_graphs = []
            else:
                self.model_graphs = []
        
        return self
    
    def _create_extended_constraints(self):
        """Create extended constraints that require difference from all previous models.
        
        Returns:
            list: Z3 constraints requiring difference from all previous models
            
        Raises:
            RuntimeError: If constraint generation fails
        """
        # Get original constraints from the first model
        # Try to get the solver, fallback to stored_solver if solver was cleaned up
        original_solver = self.build_example.model_structure.solver
        if original_solver is None:
            original_solver = getattr(self.build_example.model_structure, 'stored_solver', None)
            
        if original_solver is None:
            raise RuntimeError("No solver available - both solver and stored_solver are None")
            
        original_constraints = list(original_solver.assertions())
        
        # Create difference constraints for all previous models
        difference_constraints = []
        for model in self.found_models:
            diff_constraint = self._create_difference_constraint([model])
            difference_constraints.append(diff_constraint)
        
        # Add structural constraints to help find different models
        if HAS_NETWORKX:
            for model in self.found_models:
                iso_constraint = self._create_non_isomorphic_constraint(model)
                if iso_constraint is not None:  # Check for None explicitly instead of using truth value
                    difference_constraints.append(iso_constraint)
        
        return original_constraints + difference_constraints
        
    def _build_new_model_structure(self, z3_model):
        """Build a completely new model structure from a Z3 model.
        
        Instead of updating an existing model structure, this creates a fresh
        model structure from scratch, proper initialization with the Z3 model.
        
        Args:
            z3_model: Z3 model to use for the new structure
            
        Returns:
            ModelStructure: A new model structure built from scratch
        """
        try:
            # Get original build example to extract settings and constraints
            original_build_example = self.build_example
            
            # Create a fresh ModelConstraints instance but without the Z3 model
            model_constraints = original_build_example.model_constraints
            
            # Create a new bare model structure 
            # DO NOT use the constructor that tries to evaluate Z3 values
            klass = original_build_example.model_structure.__class__
            new_structure = object.__new__(klass)
            
            # Initialize only the attributes needed before Z3 model evaluation
            self._initialize_base_attributes(new_structure, model_constraints, original_build_example.settings)
            
            # Now set the Z3 model after basic initialization
            new_structure.z3_model = z3_model
            new_structure.z3_model_status = True
            
            # Transfer runtime from original model structure
            new_structure.z3_model_runtime = original_build_example.model_structure.z3_model_runtime
            
            # Properly initialize Z3-dependent attributes
            self._initialize_z3_dependent_attributes(new_structure, z3_model)
            
            # Interpret sentences
            sentence_objects = new_structure.premises + new_structure.conclusions
            new_structure.interpret(sentence_objects)
            
            return new_structure
            
        except Exception as e:
            logger.error(f"Error building new model structure: {str(e)}")
            logger.debug(traceback.format_exc())
            return None
            
    def _initialize_base_attributes(self, model_structure, model_constraints, settings):
        """Initialize basic attributes of a model structure that don't depend on the Z3 model.
        
        This initializes the core attributes needed before Z3 model evaluation,
        following a proper two-phase initialization pattern.
        
        Args:
            model_structure: The model structure to initialize
            model_constraints: The model constraints to use
            settings: The settings to use
        """
        # Define ANSI color codes (copied from ModelDefaults.__init__)
        model_structure.COLORS = {
            "default": "\033[37m",  # WHITE
            "world": "\033[34m",    # BLUE
            "possible": "\033[36m", # CYAN
            "impossible": "\033[35m", # MAGENTA
            "initial": "\033[33m",  # YELLOW
        }
        model_structure.RESET = "\033[0m"
        model_structure.WHITE = model_structure.COLORS["default"]
        
        # Copy attributes from ModelDefaults.__init__
        model_structure.model_constraints = model_constraints
        model_structure.settings = settings
        model_structure.max_time = settings.get("max_time", 1.0)
        model_structure.expectation = settings.get("expectation", True)
        
        # Set semantics and related attributes
        model_structure.semantics = model_constraints.semantics
        model_structure.main_point = model_structure.semantics.main_point
        model_structure.all_states = model_structure.semantics.all_states
        model_structure.N = model_structure.semantics.N
        
        # Set syntax and related attributes
        model_structure.syntax = model_constraints.syntax
        model_structure.start_time = model_structure.syntax.start_time
        model_structure.premises = model_structure.syntax.premises
        model_structure.conclusions = model_structure.syntax.conclusions
        model_structure.sentence_letters = model_structure.syntax.sentence_letters
        
        # Set proposition class and solver
        model_structure.proposition_class = model_constraints.proposition_class
        model_structure.solver = z3.Solver()
        for assertion in model_constraints.all_constraints:
            model_structure.solver.add(assertion)
        
        # Initialize Z3 model attributes as None
        model_structure.z3_model = None
        model_structure.z3_model_status = None
        model_structure.z3_model_runtime = None
        model_structure.timeout = None
        model_structure.unsat_core = None
        
        # Get main world from main_point
        if hasattr(model_structure.main_point, "get"):
            model_structure.main_world = model_structure.main_point.get("world")
        
        # Initialize Z3 values as None
        model_structure.z3_main_world = None
        model_structure.z3_possible_states = None 
        model_structure.z3_world_states = None
        
        # Initialize difference tracking
        # model_structure.model_differences = None  # Don't initialize, will be set later
        
    def _initialize_z3_dependent_attributes(self, model_structure, z3_model):
        """Initialize attributes that depend on the Z3 model.
        
        This is the second phase of initialization that evaluates Z3 model values.
        
        Args:
            model_structure: The model structure to initialize
            z3_model: The Z3 model to use
        """
        # Initialize main world evaluation
        model_structure.z3_main_world = z3_model.eval(model_structure.main_world, model_completion=True) 
        model_structure.main_point["world"] = model_structure.z3_main_world
        
        # Initialize possible states
        semantics = model_structure.semantics
        model_structure.z3_possible_states = [
            state for state in model_structure.all_states
            if bool(z3_model.eval(semantics.possible(state), model_completion=True))
        ]
        
        # Initialize world states 
        model_structure.z3_world_states = [
            state for state in model_structure.z3_possible_states
            if bool(z3_model.eval(semantics.is_world(state), model_completion=True))
        ]
        
        # Allow theory-specific initialization
        if hasattr(model_structure, 'initialize_from_z3_model'):
            model_structure.initialize_from_z3_model(z3_model)
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two model structures.
        
        This is the base implementation that handles theory-agnostic difference detection.
        Theory-specific subclasses should override this method with their own
        difference detection logic.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences between models
        """
        # Fall back to the basic difference detection which is theory-agnostic
        return self._calculate_basic_differences(new_structure, previous_structure)
    
    def _calculate_basic_differences(self, new_structure, previous_structure):
        """Theory-agnostic method to calculate basic differences between two model structures.
        
        This provides a minimal difference detection focused on sentence letters and Z3 functions,
        without any theory-specific semantic interpretation.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure to compare against
            
        Returns:
            dict: Basic differences between the models
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize basic differences structure
        differences = {
            "sentence_letters": {},
            "semantic_functions": {},
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []}
        }
        
        # Compare worlds and possible states
        old_worlds = getattr(previous_structure, "z3_world_states", [])
        new_worlds = getattr(new_structure, "z3_world_states", [])
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Compare possible states
        old_states = getattr(previous_structure, "z3_possible_states", [])
        new_states = getattr(new_structure, "z3_possible_states", [])
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare sentence letter valuations (common to all theories)
        for letter in new_structure.sentence_letters:
            try:
                prev_value = previous_model.eval(letter, model_completion=True)
                new_value = new_model.eval(letter, model_completion=True)
                
                if str(prev_value) != str(new_value):
                    differences["sentence_letters"][str(letter)] = {
                        "old": prev_value,
                        "new": new_value
                    }
            except z3.Z3Exception:
                pass
        
        # Compare semantic function interpretations (common to all theories)
        semantics = new_structure.semantics
        for attr_name in dir(semantics):
            if attr_name.startswith('_'):
                continue
                
            attr = getattr(semantics, attr_name)
            if not isinstance(attr, z3.FuncDeclRef):
                continue
                
            arity = attr.arity()
            if arity == 0:
                continue
            
            # For unary and binary functions, check specific values
            if arity <= 2:
                n_worlds = len(getattr(new_structure, 'z3_world_states', [])) or 5  # Default to 5 if not available
                
                func_diffs = {}
                for inputs in self._generate_input_combinations(arity, n_worlds):
                    try:
                        args = [z3.IntVal(i) for i in inputs]
                        prev_value = previous_model.eval(attr(*args), model_completion=True)
                        new_value = new_model.eval(attr(*args), model_completion=True)
                        
                        if str(prev_value) != str(new_value):
                            func_diffs[str(inputs)] = {
                                "old": prev_value,
                                "new": new_value
                            }
                    except z3.Z3Exception:
                        pass
                
                if func_diffs:
                    differences["semantic_functions"][attr_name] = func_diffs
        
        return differences
    
    def _check_isomorphism(self, new_structure, new_model):
        """Check if a model is isomorphic to any previous model with caching.
        
        This uses NetworkX to check graph isomorphism between models.
        Theory-specific subclasses should override this method if they
        need custom isomorphism checking.
        
        Args:
            new_structure: The model structure to check
            new_model: The Z3 model to check
            
        Returns:
            bool: True if the model is isomorphic to any previous model
        """
        if not HAS_NETWORKX:
            return False
            
        try:
            # Create a graph representation of the new model
            new_graph = ModelGraph(new_structure, new_model)
            
            # Generate cache key based on graph properties
            cache_key = self._generate_graph_cache_key(new_graph)
            
            # Check cache first
            if cache_key in self._isomorphism_cache:
                return self._isomorphism_cache[cache_key]
            
            # Store the graph with the model structure
            new_structure.model_graph = new_graph
            
            # Check if this model is isomorphic to any previous model
            is_isomorphic = False
            
            # Calculate isomorphism with a timeout
            start_time = time.time()
            iteration_timeout = self.settings.get('iteration_timeout', 1.0)
            
            for prev_graph in self.model_graphs:
                # Check if timeout exceeded
                if time.time() - start_time > iteration_timeout:
                    logger.warning("Isomorphism check timed out, skipping further checks.")
                    break
                    
                # Check isomorphism
                if new_graph.is_isomorphic(prev_graph):
                    is_isomorphic = True
                    # Mark the structure as isomorphic
                    new_structure.isomorphic_to_previous = True
                    break
            
            # Cache the result
            self._isomorphism_cache[cache_key] = is_isomorphic
            
            # If not isomorphic, add the graph to our collection
            if not is_isomorphic:
                self.model_graphs.append(new_graph)
                
            return is_isomorphic
            
        except Exception as e:
            logger.warning(f"Isomorphism check failed: {str(e)}")
            return False
    
    def _generate_graph_cache_key(self, graph):
        """Generate a cache key based on graph structure.
        
        Args:
            graph: ModelGraph instance
            
        Returns:
            tuple: Cache key based on graph invariants
        """
        # Use graph invariants as cache key
        return (
            graph.graph.number_of_nodes(),
            graph.graph.number_of_edges(),
            tuple(sorted(graph.graph.degree())),
            # Add more invariants as needed
        )
    
    # Abstract methods that must be implemented by theory-specific subclasses
    
    def _create_difference_constraint(self, previous_models):
        """Create a Z3 constraint requiring difference from all previous models.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Args:
            previous_models: List of Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint expression
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create a constraint that forces structural differences to avoid isomorphism.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints after multiple isomorphism failures.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
    
    def _get_iteration_settings(self):
        """Extract and validate iteration settings from BuildExample.
        
        Settings:
        - iterate: Maximum number of models to find (int > 0)
        - iterate_timeout: Maximum time to spend on all iterations (optional)
        - iteration_attempts: Maximum consecutive isomorphic models before applying stronger constraints
        - escape_attempts: Maximum attempts to escape from isomorphic models before giving up
        
        Returns:
            dict: Validated iteration settings
            
        Raises:
            ValueError: If settings are invalid
        """
        # Get settings from the build example
        settings = getattr(self.build_example, 'settings', {})
        if not settings:
            # If no settings found, use defaults
            return {
                'iterate': 1,
                'iteration_attempts': 5,
                'escape_attempts': 3
            }
            
        # Validate iterate
        iterate = settings.get('iterate', 1)
        if not isinstance(iterate, int):
            try:
                iterate = int(iterate)
            except (ValueError, TypeError):
                raise ValueError(
                    f"The 'iterate' setting must be an integer, got {type(iterate).__name__}"
                )
                
        if iterate < 1:
            raise ValueError(f"The 'iterate' setting must be positive, got {iterate}")
            
        # Copy settings to avoid modifying the original
        validated_settings = settings.copy()
        validated_settings['iterate'] = iterate
        
        # Add and validate iteration_attempts (default to 5)
        iteration_attempts = settings.get('iteration_attempts', settings.get('max_attempts', 5))
        if not isinstance(iteration_attempts, int) or iteration_attempts <= 0:
            iteration_attempts = 5
        validated_settings['iteration_attempts'] = iteration_attempts
        
        # Add and validate escape_attempts (default to 3)
        escape_attempts = settings.get('escape_attempts', 3)
        if not isinstance(escape_attempts, int) or escape_attempts <= 0:
            escape_attempts = 3
        validated_settings['escape_attempts'] = escape_attempts
        
        # Add iteration timeout setting (default to 1.0 seconds)
        iteration_timeout = settings.get('iteration_timeout', settings.get('isomorphism_timeout', 1.0))
        if not isinstance(iteration_timeout, (int, float)) or iteration_timeout <= 0:
            iteration_timeout = 1.0
        validated_settings['iteration_timeout'] = iteration_timeout
        
        # Validate iterate_timeout if present (overall timeout)
        if 'iterate_timeout' in settings:
            timeout = settings['iterate_timeout']
            if not isinstance(timeout, (int, float)) or timeout <= 0:
                raise ValueError(
                    f"The 'iterate_timeout' setting must be a positive number, got {timeout}"
                )
                
        return validated_settings
    
    def _generate_input_combinations(self, arity, domain_size):
        """Generate all relevant input combinations for a function of given arity.
        
        Args:
            arity: Number of arguments the function takes
            domain_size: Size of the domain (typically number of worlds)
            
        Returns:
            list: All relevant input combinations
        """
        # For n-ary functions, generate all combinations of inputs
        # from the domain, which is typically the world indices
        domain = range(domain_size)
        return itertools.product(domain, repeat=arity)


# Module-level convenience function with theory-agnostic implementation
def iterate_example(example, max_iterations=None):
    """Iterate a BuildExample to find multiple models.
    
    This function is designed to be imported and used by theory-specific implementations
    that will provide their own iterator class.
    
    Args:
        example: A BuildExample instance.
        max_iterations: Maximum number of models to find.
        
    Returns:
        list: List of BuildExample instances with distinct models.
        
    Raises:
        NotImplementedError: This base function should not be called directly.
    """
    # This base implementation should not be called directly
    raise NotImplementedError(
        "iterate_example in core.py should not be called directly. "
        "Theory packages should provide their own iterate_example implementations "
        "that use their specific iterator class."
    )
