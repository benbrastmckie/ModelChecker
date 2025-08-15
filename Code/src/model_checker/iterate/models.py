"""Model creation and validation for iteration.

This module handles building new model structures from Z3 models,
managing model interpretation, validating model constraints, and
calculating differences between models.
"""

import logging
import z3
from typing import Any

logger = logging.getLogger(__name__)


class ModelBuilder:
    """Builds and validates model structures for iteration."""
    
    def __init__(self, build_example):
        """Initialize model builder.
        
        Args:
            build_example: Original BuildExample instance
        """
        self.build_example = build_example
    
    def build_new_model_structure(self, z3_model):
        """Build a new model structure with fresh constraints.
        
        This creates new ModelConstraints using the current model's verify/falsify
        functions, ensuring constraint consistency for MODEL 2+.
        
        Args:
            z3_model: Z3 model to use for the new structure
            
        Returns:
            ModelStructure: A new model structure with fresh constraints
        """
        try:
            # Import required modules
            from model_checker.syntactic import Syntax
            from model_checker.models.constraints import ModelConstraints
            import z3
            
            # Get original build example components
            original_build = self.build_example
            settings = original_build.settings.copy()
            
            # Create fresh syntax (reuses sentence parsing)
            syntax = Syntax(
                original_build.premises,
                original_build.conclusions,
                original_build.semantic_theory.get("operators")
            )
            
            # Create new semantics WITHOUT state transfer
            semantics_class = original_build.semantic_theory["semantics"]
            semantics = semantics_class(settings)
            
            # Create fresh ModelConstraints with current context
            proposition_class = original_build.semantic_theory["proposition"]
            model_constraints = ModelConstraints(
                settings,
                syntax,
                semantics,
                proposition_class
            )
            
            # We need to inject the concrete constraints into the model constraints
            # BEFORE creating the model structure, so it solves with them included
            
            # Get semantics from model_constraints
            semantics = model_constraints.semantics
            
            # Create a new solver with the base constraints AND concrete values
            temp_solver = z3.Solver()
            
            # Add the base constraints from model_constraints
            for constraint in model_constraints.all_constraints:
                temp_solver.add(constraint)
            
            # Extract concrete values from Z3 model and add them as constraints
            # Constrain world states
            for state in range(2**semantics.N):
                # Is this state a world in the iterator model?
                is_world_val = z3_model.eval(semantics.is_world(state), model_completion=True)
                if z3.is_true(is_world_val):
                    temp_solver.add(semantics.is_world(state))
                else:
                    temp_solver.add(z3.Not(semantics.is_world(state)))
                
                # Is this state possible in the iterator model?
                # Note: Not all theories have a 'possible' predicate (e.g., bimodal theory)
                if hasattr(semantics, 'possible'):
                    is_possible_val = z3_model.eval(semantics.possible(state), model_completion=True)
                    if z3.is_true(is_possible_val):
                        temp_solver.add(semantics.possible(state))
                    else:
                        temp_solver.add(z3.Not(semantics.possible(state)))
            
            # Constrain verify/falsify for sentence letters
            # Note: Some theories (e.g., bimodal) use truth_condition instead of verify/falsify
            if hasattr(semantics, 'verify'):
                for letter_obj in syntax.sentence_letters:
                    if hasattr(letter_obj, 'sentence_letter'):
                        atom = letter_obj.sentence_letter
                        for state in range(2**semantics.N):
                            # Verify value
                            verify_val = z3_model.eval(semantics.verify(state, atom), model_completion=True)
                            if z3.is_true(verify_val):
                                temp_solver.add(semantics.verify(state, atom))
                            else:
                                temp_solver.add(z3.Not(semantics.verify(state, atom)))
                            
                            # Falsify value (if it exists)
                            if hasattr(semantics, 'falsify'):
                                falsify_val = z3_model.eval(semantics.falsify(state, atom), model_completion=True)
                                if z3.is_true(falsify_val):
                                    temp_solver.add(semantics.falsify(state, atom))
                                else:
                                    temp_solver.add(z3.Not(semantics.falsify(state, atom)))
            
            # Store the constraints in model_constraints so the model will use them
            model_constraints.all_constraints = list(temp_solver.assertions())
            
            # Now create the model structure which will solve with all constraints
            model_structure_class = original_build.model_structure_class
            model_structure = model_structure_class(model_constraints, settings)
            
            # The model structure constructor already solved with all constraints
            # Check if it was successful
            if not model_structure.z3_model_status:
                logger.warning("Model structure creation was not successful")
                return None
            
            # Interpret the premises and conclusions
            all_sentences = syntax.premises + syntax.conclusions
            model_structure.interpret(all_sentences)
            
            return model_structure
            
        except Exception as e:
            logger.error(f"Failed to build model structure: {str(e)}")
            return None
    
    def _initialize_base_attributes(self, model_structure, model_constraints, settings):
        """Initialize basic model structure attributes.
        
        Args:
            model_structure: Model structure to initialize
            model_constraints: Model constraints object
            settings: Model settings dictionary
        """
        # Set basic attributes from model constraints
        model_structure.settings = settings
        model_structure.model_constraints = model_constraints
        model_structure.semantics = model_constraints.semantics
        
        # Initialize collections
        model_structure.z3_atoms = []
        model_structure.z3_sentence_letters = []
        model_structure.z3_worlds = []
        model_structure.z3_world_states = []
        model_structure.z3_possible_states = []
        model_structure.z3_impossible_states = []
        
        # Initialize interpretation results
        model_structure.premises = []
        model_structure.conclusions = []
        
        # Set solver reference
        model_structure.solver = model_constraints.solver if hasattr(model_constraints, 'solver') else None
    
    def _initialize_z3_dependent_attributes(self, model_structure, z3_model):
        """Initialize attributes that depend on the Z3 model.
        
        Args:
            model_structure: Model structure to initialize  
            z3_model: Z3 model to extract values from
        """
        try:
            semantics = model_structure.semantics
            N = model_structure.settings.get('N', 3)
            
            # Initialize state collections
            world_states = []
            possible_states = []
            impossible_states = []
            
            # Evaluate states using Z3 model
            for state in range(N):
                try:
                    if hasattr(semantics, 'is_world'):
                        # Check if this state is a world
                        is_world_val = self._evaluate_z3_boolean(z3_model, semantics.is_world(state))
                        if is_world_val:
                            world_states.append(state)
                    
                    if hasattr(semantics, 'possible'):
                        # Check if this state is possible
                        is_possible_val = self._evaluate_z3_boolean(z3_model, semantics.possible(state))
                        if is_possible_val:
                            possible_states.append(state)
                        else:
                            impossible_states.append(state)
                            
                except Exception as e:
                    logger.warning(f"Error evaluating state {state}: {e}")
                    continue
            
            # Set the collections
            model_structure.z3_world_states = world_states
            model_structure.z3_possible_states = possible_states
            model_structure.z3_impossible_states = impossible_states
            
            # Also store as attribute for compatibility
            model_structure.z3_worlds = world_states
            
        except Exception as e:
            logger.warning(f"Error initializing Z3-dependent attributes: {e}")
    
    def _evaluate_z3_boolean(self, z3_model, expression):
        """Safely evaluate a Z3 boolean expression.
        
        Args:
            z3_model: Z3 model to use for evaluation
            expression: Z3 expression to evaluate
            
        Returns:
            bool: Evaluation result, defaults to False on error
        """
        try:
            if expression is None:
                return False
                
            # Use Z3 model evaluation with completion
            result = z3_model.eval(expression, model_completion=True)
            
            # Check if the result is a Z3 boolean
            if z3.is_bool(result):
                return z3.is_true(result)
            
            # Handle numeric results (0 = False, non-zero = True)
            if z3.is_int_value(result) or z3.is_real_value(result):
                try:
                    numeric_val = result.as_long() if z3.is_int_value(result) else float(result.as_decimal(6).replace('?', ''))
                    return numeric_val != 0
                except:
                    return False
            
            # Handle string representation as fallback
            result_str = str(result).strip()
            if result_str.lower() in ['true', '1']:
                return True
            elif result_str.lower() in ['false', '0']:
                return False
                
            logger.debug(f"Unknown Z3 result type for {expression}: {result} (type: {type(result)})")
            return False
            
        except Exception as e:
            logger.warning(f"Error evaluating Z3 expression {expression}: {e}")
            return False


class DifferenceCalculator:
    """Calculates differences between model structures."""
    
    def calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two model structures.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure to compare against
            
        Returns:
            dict: Dictionary containing all calculated differences
        """
        differences = {}
        
        try:
            # Calculate basic differences
            basic_diffs = self._calculate_basic_differences(new_structure, previous_structure)
            differences.update(basic_diffs)
            
            # Calculate semantic differences if available
            semantic_diffs = self._calculate_semantic_differences(new_structure, previous_structure)
            differences.update(semantic_diffs)
            
            # Calculate state differences
            state_diffs = self._calculate_state_differences(new_structure, previous_structure)
            differences.update(state_diffs)
            
        except Exception as e:
            logger.warning(f"Error calculating differences: {e}")
            differences['error'] = str(e)
            
        return differences
    
    def _calculate_basic_differences(self, new_structure, previous_structure):
        """Calculate basic structural differences.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Basic difference information
        """
        differences = {}
        
        try:
            # World state differences
            new_worlds = set(getattr(new_structure, 'z3_world_states', []))
            prev_worlds = set(getattr(previous_structure, 'z3_world_states', []))
            
            world_added = new_worlds - prev_worlds
            world_removed = prev_worlds - new_worlds
            
            differences['world_changes'] = {
                'added': list(world_added),
                'removed': list(world_removed),
                'total_change_count': len(world_added) + len(world_removed)
            }
            
            # Possible state differences
            new_possible = set(getattr(new_structure, 'z3_possible_states', []))
            prev_possible = set(getattr(previous_structure, 'z3_possible_states', []))
            
            possible_added = new_possible - prev_possible
            possible_removed = prev_possible - new_possible
            
            differences['possible_changes'] = {
                'added': list(possible_added),
                'removed': list(possible_removed),
                'total_change_count': len(possible_added) + len(possible_removed)
            }
            
        except Exception as e:
            logger.warning(f"Error calculating basic differences: {e}")
            differences['basic_error'] = str(e)
            
        return differences
    
    def _calculate_semantic_differences(self, new_structure, previous_structure):
        """Calculate semantic differences between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Semantic difference information
        """
        differences = {}
        
        try:
            # Atomic proposition changes
            atomic_changes = self._calculate_atomic_differences(new_structure, previous_structure)
            if atomic_changes:
                differences['atomic_changes'] = atomic_changes
            
            # Other semantic changes can be added here
            
        except Exception as e:
            logger.warning(f"Error calculating semantic differences: {e}")
            differences['semantic_error'] = str(e)
            
        return differences
    
    def _calculate_atomic_differences(self, new_structure, previous_structure):
        """Calculate differences in atomic proposition evaluations.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Atomic proposition differences
        """
        changes = {
            'verification_changes': {},
            'falsification_changes': {}
        }
        
        # Get sentence letters from structures
        new_letters = getattr(new_structure, 'z3_sentence_letters', [])
        prev_letters = getattr(previous_structure, 'z3_sentence_letters', [])
        
        # Compare atomic evaluations
        # This is a simplified implementation - extend as needed
        
        return changes if any(changes.values()) else None
    
    def _calculate_state_differences(self, new_structure, previous_structure):
        """Calculate differences in state properties.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: State-level differences
        """
        differences = {}
        
        try:
            # Count of impossible states
            new_impossible = set(getattr(new_structure, 'z3_impossible_states', []))
            prev_impossible = set(getattr(previous_structure, 'z3_impossible_states', []))
            
            if new_impossible != prev_impossible:
                differences['impossible_state_changes'] = {
                    'added': list(new_impossible - prev_impossible),
                    'removed': list(prev_impossible - new_impossible)
                }
                
        except Exception as e:
            logger.warning(f"Error calculating state differences: {e}")
            
        return differences
    
    def _compare_state_evaluations(self, new_structure, previous_structure):
        """Compare state-level evaluations between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: State evaluation comparisons
        """
        comparisons = {}
        
        try:
            # Get all states from both structures
            new_worlds = set(getattr(new_structure, 'z3_world_states', []))
            prev_worlds = set(getattr(previous_structure, 'z3_world_states', []))
            all_states = new_worlds.union(prev_worlds)
            
            for state in all_states:
                state_info = {}
                
                # Check world status change
                was_world = state in prev_worlds
                is_world = state in new_worlds
                
                if was_world != is_world:
                    state_info['world_status_changed'] = {
                        'was_world': was_world,
                        'is_world': is_world
                    }
                
                if state_info:
                    comparisons[f'state_{state}'] = state_info
                    
        except Exception as e:
            logger.warning(f"Error comparing state evaluations: {e}")
            
        return comparisons


def evaluate_z3_boolean(z3_model: z3.ModelRef, expression: Any) -> bool:
    """Safely evaluate a Z3 expression to a Python boolean.
    
    This method handles the complexity of evaluating Z3 expressions that may
    be symbolic, concrete, or have various internal representations.
    
    Args:
        z3_model: The Z3 model to evaluate against
        expression: The Z3 expression to evaluate
        
    Returns:
        bool: The boolean value of the expression
        
    Note:
        This replaces the complex fallback logic with a simpler approach
        that handles the common cases more reliably.
    """
    if expression is None:
        return False
        
    # Handle Python booleans directly
    if isinstance(expression, bool):
        return expression
        
    # Handle Z3 boolean values
    if z3.is_bool(expression):
        try:
            # Try direct evaluation
            evaluated = z3_model.evaluate(expression, model_completion=True)
            
            # Check various ways Z3 might represent true/false
            if z3.is_true(evaluated):
                return True
            elif z3.is_false(evaluated):
                return False
            else:
                # Try string comparison as last resort
                str_val = str(evaluated)
                return str_val.lower() == 'true'
                
        except z3.Z3Exception:
            # If evaluation fails, default to False
            return False
    
    # For non-boolean expressions, evaluate and check if non-zero
    try:
        evaluated = z3_model.evaluate(expression, model_completion=True)
        if z3.is_int(evaluated) or z3.is_real(evaluated):
            return evaluated.as_long() != 0
        elif z3.is_bv(evaluated):
            return evaluated.as_long() != 0
        else:
            # Unknown type, try string comparison
            return str(evaluated).lower() == 'true'
    except:
        return False


def is_valid_model(model_structure, settings: dict) -> bool:
    """Check if a model structure satisfies basic validity requirements.
    
    Args:
        model_structure: The model structure to validate
        settings: The iteration settings
        
    Returns:
        bool: True if model is valid, False otherwise
    """
    # Check for required attributes
    required_attrs = ['z3_model', 'premise_formulas', 'conclusion_formulas']
    for attr in required_attrs:
        if not hasattr(model_structure, attr):
            return False
    
    # Check non-empty settings if specified
    if settings.get('non_empty', False):
        # Theory-specific check for non-empty models
        if hasattr(model_structure, 'z3_possible_states'):
            if not model_structure.z3_possible_states:
                return False
        elif hasattr(model_structure, 'world_histories'):
            if not model_structure.world_histories:
                return False
    
    # Check contingent settings if specified
    if settings.get('contingent', False):
        # Theory-specific check for contingent models
        # This would need to be customized per theory
        pass
    
    return True


def validate_premises(model_structure, z3_model) -> bool:
    """Check if all premises are satisfied in the model.
    
    Args:
        model_structure: The model structure containing premises
        z3_model: The Z3 model to evaluate against
        
    Returns:
        bool: True if all premises are satisfied
    """
    if not hasattr(model_structure, 'premise_formulas'):
        return True  # No premises to check
    
    for premise in model_structure.premise_formulas:
        if hasattr(premise, 'z3_formula'):
            formula = premise.z3_formula
        else:
            formula = premise
        
        if not evaluate_z3_boolean(z3_model, formula):
            return False
    
    return True


def validate_conclusions(model_structure, z3_model, expectation: bool) -> bool:
    """Check if conclusions match expectation in the model.
    
    Args:
        model_structure: The model structure containing conclusions
        z3_model: The Z3 model to evaluate against
        expectation: True if expecting conclusions to be true (theorem),
                    False if expecting them to be false (countermodel)
        
    Returns:
        bool: True if conclusions match expectation
    """
    if not hasattr(model_structure, 'conclusion_formulas'):
        return True  # No conclusions to check
    
    for conclusion in model_structure.conclusion_formulas:
        if hasattr(conclusion, 'z3_formula'):
            formula = conclusion.z3_formula
        else:
            formula = conclusion
        
        is_true = evaluate_z3_boolean(z3_model, formula)
        
        # For countermodels (expectation=True), we want at least one false conclusion
        # For theorems (expectation=False), we want all conclusions true
        if expectation and not is_true:
            return True  # Found a false conclusion for countermodel
        elif not expectation and not is_true:
            return False  # Found a false conclusion for theorem
    
    # If expectation=True (countermodel) and all conclusions are true, invalid
    # If expectation=False (theorem) and all conclusions are true, valid
    return not expectation