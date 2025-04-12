"""Z3 model utilities for model checker.

This module provides utilities for working with Z3 models, including model
creation, difference constraints, and model inspection.
"""

import z3

def create_difference_constraint(old_model, variables):
    """Create a constraint requiring the new model to differ from the old one.
    
    Args:
        old_model: Previous Z3 model to differentiate from
        variables: List of Z3 variables that should be considered for differences
        
    Returns:
        z3.BoolRef: Constraint requiring at least one variable to have a different value
        
    Raises:
        z3.Z3Exception: If constraint creation fails
        ValueError: If old_model is None or variables list is empty
    """
    if old_model is None:
        raise ValueError("Cannot create difference constraint from None model")
        
    if not variables:
        raise ValueError("No variables provided for difference constraint")
        
    constraints = []
    
    for var in variables:
        if not isinstance(var, z3.ExprRef):
            continue
            
        try:
            old_value = old_model.eval(var, model_completion=True)
            if old_value is not None:
                constraints.append(var != old_value)
        except z3.Z3Exception as e:
            raise z3.Z3Exception(f"Failed to evaluate variable {var}: {e}")
            
    if not constraints:
        raise ValueError("No valid variables provided for difference constraint")
        
    return z3.Or(*constraints)

def extract_model_values(model, variables):
    """Extract values from a Z3 model for the given variables.
    
    Args:
        model: Z3 model to extract values from
        variables: List of variables to extract
        
    Returns:
        dict: Mapping of variable names to their values
        
    Raises:
        ValueError: If model is None
        z3.Z3Exception: If evaluation fails
    """
    if model is None:
        raise ValueError("Cannot extract values from None model")
        
    result = {}
    for var in variables:
        if not isinstance(var, z3.ExprRef):
            continue
            
        try:
            value = model.eval(var, model_completion=True)
            result[str(var)] = value
        except z3.Z3Exception as e:
            raise z3.Z3Exception(f"Failed to evaluate variable {var}: {e}")
            
    return result

def find_next_model(solver, old_model, variables):
    """Find a new model that differs from the previous one.
    
    Args:
        solver: Z3 solver to use for finding the next model
        old_model: Previous Z3 model to differentiate from
        variables: Variables that should differ in the new model
        
    Returns:
        tuple: (found, model) where:
            - found (bool): True if a new model was found
            - model: The new Z3 model if found, None otherwise
            
    Raises:
        ValueError: If parameters are invalid
        z3.Z3Exception: If Z3 operations fail
    """
    if solver is None:
        raise ValueError("Solver cannot be None")
        
    if old_model is None:
        raise ValueError("Previous model cannot be None")
        
    # Create difference constraint
    diff_constraint = create_difference_constraint(old_model, variables)
    
    # Add constraint to solver
    solver.push()
    try:
        solver.add(diff_constraint)
        
        # Check for satisfiability
        result = solver.check()
        if result == z3.sat:
            return True, solver.model()
        else:
            return False, None
    finally:
        solver.pop()  # Remove the added constraint