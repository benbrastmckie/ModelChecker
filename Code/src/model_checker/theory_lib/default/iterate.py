"""Default theory specific model iteration implementation.

This module provides the DefaultModelIterator implementation which handles:
1. Detecting differences between models using default theory semantics
2. Creating constraints to differentiate models with default theory primitives
3. Checking model isomorphism for default theory models
4. Visualizing differences between default theory models
"""

import z3
import sys
import logging

from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_substates, pretty_set_print
import model_checker.syntactic as syntactic

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[DEFAULT-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class DefaultModelIterator(BaseModelIterator):
    """Model iterator for the default theory.
    
    This class extends BaseModelIterator with default theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for default theory models.
    
    The default theory uses a state-based semantics with:
    - States represented as bit vectors
    - Verification and falsification as primitive relations
    - Possible worlds as maximal possible states
    - Part-whole relationships between states
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two default theory model structures.
        
        Delegates to the theory-specific difference detection method in ModelStructure.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Try to use the theory-specific detect_model_differences method
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    # Store the differences with the new structure
                    new_structure.model_differences = differences
                    
                    # Store a reference to the previous structure for display purposes
                    new_structure.previous_structure = previous_structure
                    
                    return differences
            except Exception as e:
                logger.warning(f"Error in default theory difference detection: {e}")
        
        # Fall back to the base implementation if theory-specific method fails
        return super()._calculate_differences(new_structure, previous_structure)
    
    def _create_difference_constraint(self, previous_models):
        """Create default theory-specific constraints to differentiate models.
        
        Builds constraints that force the next model to differ from previous ones
        by focusing on verification, falsification, and part-whole relationships.
        
        Args:
            previous_models: List of previous Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint requiring difference from all previous models
        """
        logger.debug("\n==== DEBUG: _create_difference_constraint for default theory ====")
        logger.debug(f"Creating difference constraints from {len(previous_models)} previous models")
        
        # Get key structures from build_example
        model_structure = self.build_example.model_structure
        model_constraints = self.build_example.model_constraints
        semantics = model_constraints.semantics
        
        # For each previous model, create a constraint requiring at least one difference
        model_diff_constraints = []
        
        for model_idx, prev_model in enumerate(previous_models):
            logger.debug(f"\nProcessing previous model #{model_idx+1}:")
            
            # Try to use theory-specific difference constraints from the semantics
            if hasattr(semantics, 'create_difference_constraints'):
                try:
                    theory_constraints = semantics.create_difference_constraints(prev_model)
                    if theory_constraints:
                        logger.debug(f"  Using default theory-specific difference constraints")
                        model_diff_constraints.append(z3.Or(theory_constraints))
                        continue
                except Exception as e:
                    logger.debug(f"  Error in theory-specific constraints: {e}")
            
            # Fall back to the method using differentiable functions
            diff_components = []
            
            # Use theory's differentiable functions
            if hasattr(semantics, 'get_differentiable_functions'):
                try:
                    diff_funcs = semantics.get_differentiable_functions()
                    logger.debug(f"  Using {len(diff_funcs)} default theory differentiable functions")
                    
                    for func, arity, description in diff_funcs:
                        logger.debug(f"    Function {description} (arity {arity}):")
                        
                        # For unary and binary functions, check specific values
                        if arity <= 2:
                            # Get the domain size (number of worlds)
                            n_worlds = getattr(model_structure, 'num_worlds', 5)  # Default to 5 if not available
                            logger.debug(f"      Domain size (num_worlds): {n_worlds}")
                            
                            # Skip if part-whole relation function since it requires bit vectors instead of integers
                            if description == "part-whole relation":
                                logger.debug("      Skipping part-whole relation - requires bit vectors instead of integers")
                                continue
                                
                            if func == semantics.is_part_of:
                                logger.debug("      Skipping is_part_of - requires bit vectors instead of integers")
                                continue
                            
                            # Create constraints for all relevant inputs
                            input_count = 0
                            for inputs in self._generate_input_combinations(arity, n_worlds):
                                try:
                                    # Check what this function returns in the previous model
                                    args = [z3.IntVal(i) for i in inputs]
                                    prev_value = prev_model.eval(func(*args), model_completion=True)
                                    
                                    # Add constraint requiring it to be different
                                    diff_components.append(func(*args) != prev_value)
                                    input_count += 1
                                    
                                    if input_count <= 3 or input_count % 10 == 0:  # Limit log output
                                        logger.debug(f"        Added constraint for input {inputs}: must differ from {prev_value}")
                                except z3.Z3Exception as e:
                                    if input_count <= 3:
                                        logger.debug(f"        Skipped input {inputs}: {str(e)}")
                            
                            logger.debug(f"      Added {input_count} input constraints for this function")
                except Exception as e:
                    logger.debug(f"  Error processing differentiable functions: {e}")
            
            # Create a single constraint for this model requiring at least one difference
            if diff_components:
                model_diff_constraints.append(z3.Or(diff_components))
                logger.debug(f"  Total differentiable components for model #{model_idx+1}: {len(diff_components)}")
            else:
                logger.warning(f"  WARNING: No differentiable components found for model #{model_idx+1}")
        
        # The new model must be different from ALL previous models
        if model_diff_constraints:
            combined_constraint = z3.And(model_diff_constraints)
            logger.debug(f"\nCreated combined constraint requiring difference from all {len(previous_models)} previous models")
            return combined_constraint
        else:
            logger.error("\nERROR: Could not create any difference constraints")
            raise RuntimeError("Could not create any difference constraints")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create a constraint that forces structural differences to avoid isomorphism.
        
        For default theory, this focuses on accessibility patterns, truth value
        distributions, and other structural properties.
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        logger.debug("\n==== DEBUG: _create_non_isomorphic_constraint for default theory ====")
        
        # Get model structure and constraints
        model_structure = self.build_example.model_structure
        model_constraints = self.build_example.model_constraints
        semantics = model_constraints.semantics
        
        # Create constraints to force structural differences
        constraints = []
        
        # Try theory-specific structural constraints if available
        if hasattr(model_structure, 'get_structural_constraints'):
            try:
                theory_constraints = model_structure.get_structural_constraints(z3_model)
                if theory_constraints:
                    logger.debug(f"  Adding {len(theory_constraints)} default theory structural constraints")
                    constraints.extend(theory_constraints)
                    
                    # Return the combined constraints
                    if constraints:
                        return z3.Or(constraints)
            except Exception as e:
                logger.debug(f"  Error getting theory-specific structural constraints: {e}")
                
        return None if not constraints else z3.Or(constraints)
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints to escape from isomorphic models.
        
        This creates more aggressive constraints for default theory when multiple
        isomorphic models have been found in a row.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        # Get model structure
        model_structure = self.build_example.model_structure
        
        # Try theory-specific stronger constraints
        if hasattr(model_structure, 'get_stronger_constraints'):
            try:
                # Pass the escape attempt counter to calibrate constraint strength
                escape_attempt = getattr(self, 'escape_attempts', 1)
                theory_constraints = model_structure.get_stronger_constraints(isomorphic_model, escape_attempt)
                
                if theory_constraints:
                    logger.debug(f"Using {len(theory_constraints)} default theory stronger constraints")
                    return z3.Or(theory_constraints) if len(theory_constraints) > 1 else theory_constraints[0]
            except Exception as e:
                logger.debug(f"Error creating stronger constraints: {e}")
                
        return None

    def display_model_differences(self, model_structure, output=sys.stdout):
        """Display differences between models using default theory's formatting.
        
        Delegates to the format_model_differences method in ModelStructure.
        
        Args:
            model_structure: The model structure with differences to display
            output: Output stream to write to
        """
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            # If no model_differences are found but we have a previous_structure reference,
            # try to calculate differences on the fly
            if hasattr(model_structure, 'previous_structure') and model_structure.previous_structure is not None:
                model_structure.model_differences = self._calculate_differences(
                    model_structure, model_structure.previous_structure)
            else:
                return
            
        # Use the theory-specific format_model_differences method
        if hasattr(model_structure, 'format_model_differences'):
            try:
                model_structure.format_model_differences(model_structure.model_differences, output)
                return
            except Exception as e:
                logger.warning(f"Error in default theory difference formatting: {e}")
        
        # Fall back to the base class implementation
        super().display_model_differences(model_structure, output)