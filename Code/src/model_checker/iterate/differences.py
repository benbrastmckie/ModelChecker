"""Model difference calculation utilities for iteration framework.

This module provides utilities for calculating differences between models
to help generate constraints that ensure new models are distinct.
"""

import z3
from typing import Dict, List, Any, Set, Tuple, Optional
from model_checker.utils import bitvec_to_substates


class DifferenceCalculator:
    """Calculates differences between model structures.
    
    This class provides utilities for finding semantic differences
    between models, which is crucial for generating constraints
    that ensure each new model is distinct from previous ones.
    """
    
    @staticmethod
    def calculate_basic_differences(new_structure, previous_structure) -> Dict[str, Any]:
        """Calculate basic theory-agnostic differences between models.
        
        This method looks for differences in:
        - Variable assignments
        - Truth values of formulas
        - Structural properties
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            Dictionary containing categorized differences
        """
        differences = {
            "variables": {},
            "formulas": {},
            "structural": {}
        }
        
        new_model = new_structure.z3_model
        prev_model = previous_structure.z3_model
        
        # Compare variable assignments
        all_vars = set()
        
        # Collect variables from both models
        for m in [new_model, prev_model]:
            for decl in m.decls():
                all_vars.add(decl)
        
        # Compare each variable's value
        for var_decl in all_vars:
            var = var_decl()
            
            try:
                new_val = new_model.eval(var, model_completion=True)
                prev_val = prev_model.eval(var, model_completion=True)
                
                if str(new_val) != str(prev_val):
                    differences["variables"][str(var)] = {
                        "old": str(prev_val),
                        "new": str(new_val)
                    }
            except:
                # Variable might not exist in one of the models
                pass
        
        # Compare formula truth values
        for attr in ['premise_formulas', 'conclusion_formulas']:
            if hasattr(new_structure, attr):
                formulas = getattr(new_structure, attr)
                for i, formula in enumerate(formulas):
                    if hasattr(formula, 'z3_formula'):
                        z3_formula = formula.z3_formula
                        
                        try:
                            new_truth = new_model.eval(z3_formula, model_completion=True)
                            prev_truth = prev_model.eval(z3_formula, model_completion=True)
                            
                            if str(new_truth) != str(prev_truth):
                                formula_str = str(formula) if hasattr(formula, '__str__') else f"{attr}[{i}]"
                                differences["formulas"][formula_str] = {
                                    "old": str(prev_truth),
                                    "new": str(new_truth)
                                }
                        except:
                            pass
        
        return differences
    
    @staticmethod
    def find_distinguishing_variables(new_model: z3.ModelRef, 
                                     previous_models: List[z3.ModelRef]) -> Set[z3.ExprRef]:
        """Find variables that distinguish the new model from previous ones.
        
        Args:
            new_model: The new Z3 model
            previous_models: List of previous Z3 models
            
        Returns:
            Set of Z3 variables that have different values
        """
        distinguishing_vars = set()
        
        # Get all variables from new model
        new_vars = {decl: decl() for decl in new_model.decls()}
        
        # Compare with each previous model
        for prev_model in previous_models:
            for decl, var in new_vars.items():
                try:
                    new_val = new_model.eval(var, model_completion=True)
                    prev_val = prev_model.eval(var, model_completion=True)
                    
                    if not z3.eq(new_val, prev_val):
                        distinguishing_vars.add(var)
                except:
                    # Variable might not exist in previous model
                    distinguishing_vars.add(var)
        
        return distinguishing_vars
    
    @staticmethod
    def create_difference_constraint(new_model: z3.ModelRef, 
                                   previous_model: z3.ModelRef,
                                   variables: List[z3.ExprRef]) -> z3.BoolRef:
        """Create a constraint ensuring models differ on given variables.
        
        Args:
            new_model: The new model to differentiate
            previous_model: The previous model to differ from
            variables: Variables to check for differences
            
        Returns:
            Z3 constraint ensuring at least one variable differs
        """
        constraints = []
        
        for var in variables:
            try:
                prev_val = previous_model.eval(var, model_completion=True)
                # Create constraint that this variable must differ
                constraints.append(var != prev_val)
            except:
                # If variable doesn't exist in previous model, any value is fine
                pass
        
        if constraints:
            return z3.Or(*constraints)
        else:
            # If no variables to differentiate on, return True (no constraint)
            return z3.BoolVal(True)
    
    @staticmethod
    def get_state_differences(new_structure, previous_structure, 
                            state_attr: str = 'z3_possible_states') -> Dict[str, List]:
        """Find differences in state-based properties.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            state_attr: Attribute name containing states
            
        Returns:
            Dictionary with added/removed states
        """
        old_states = set(getattr(previous_structure, state_attr, []))
        new_states = set(getattr(new_structure, state_attr, []))
        
        return {
            "added": list(new_states - old_states),
            "removed": list(old_states - new_states)
        }
    
    @staticmethod
    def format_differences(differences: Dict[str, Any], 
                          theory_name: Optional[str] = None) -> str:
        """Format differences for display.
        
        Args:
            differences: Dictionary of differences
            theory_name: Optional theory name for specialized formatting
            
        Returns:
            Formatted string representation of differences
        """
        lines = []
        
        if differences.get("variables"):
            lines.append("Variable Changes:")
            for var, change in differences["variables"].items():
                lines.append(f"  {var}: {change['old']} → {change['new']}")
        
        if differences.get("formulas"):
            lines.append("\nFormula Truth Values:")
            for formula, change in differences["formulas"].items():
                lines.append(f"  {formula}: {change['old']} → {change['new']}")
        
        if differences.get("structural"):
            lines.append("\nStructural Changes:")
            for prop, change in differences["structural"].items():
                lines.append(f"  {prop}: {change}")
        
        return "\n".join(lines) if lines else "No differences found"