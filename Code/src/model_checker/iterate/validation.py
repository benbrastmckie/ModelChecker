"""Model validation utilities for the iteration framework.

This module provides utilities for validating models during iteration,
including safe Z3 boolean evaluation and model validity checking.
"""

import z3
from typing import Any, Optional


class ModelValidator:
    """Utilities for validating models during iteration."""
    
    @staticmethod
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
    
    @staticmethod
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
    
    @staticmethod
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
            
            if not ModelValidator.evaluate_z3_boolean(z3_model, formula):
                return False
        
        return True
    
    @staticmethod
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
            
            is_true = ModelValidator.evaluate_z3_boolean(z3_model, formula)
            
            # For countermodels (expectation=True), we want at least one false conclusion
            # For theorems (expectation=False), we want all conclusions true
            if expectation and not is_true:
                return True  # Found a false conclusion for countermodel
            elif not expectation and not is_true:
                return False  # Found a false conclusion for theorem
        
        # If expectation=True (countermodel) and all conclusions are true, invalid
        # If expectation=False (theorem) and all conclusions are true, valid
        return not expectation