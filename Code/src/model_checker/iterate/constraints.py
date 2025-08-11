"""Constraint generation and management for model iteration.

This module handles creating constraints that ensure each new model differs 
from previously found models. It manages Z3 solver interaction and constraint
validation.
"""

import z3
import itertools
import logging

logger = logging.getLogger(__name__)


class ConstraintGenerator:
    """Generates and manages constraints for model iteration."""
    
    def __init__(self, build_example):
        """Initialize constraint generator.
        
        Args:
            build_example: BuildExample instance with original model
        """
        self.build_example = build_example
        self.solver = self._create_persistent_solver()
        
        # Preserve original constraints for iteration
        original_constraints = []
        if hasattr(build_example, 'model_constraints') and \
           hasattr(build_example.model_constraints, 'all_constraints'):
            original_constraints = build_example.model_constraints.all_constraints
        
        logger.debug(f"Preserved {len(original_constraints)} original constraints for iteration")
    
    def _create_persistent_solver(self):
        """Create a persistent solver with original constraints.
        
        Returns:
            z3.Solver: Solver with original constraints loaded
        """
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
    
    def create_extended_constraints(self, previous_models):
        """Create constraints that exclude all previous models.
        
        Args:
            previous_models: List of Z3 models to exclude
            
        Returns:
            list: List of Z3 constraints
        """
        extended_constraints = []
        
        # Add difference constraints for each previous model
        for model in previous_models:
            difference_constraint = self._create_difference_constraint([model])
            if difference_constraint is not None:
                extended_constraints.append(difference_constraint)
        
        return extended_constraints
    
    def check_satisfiability(self, additional_constraints=None):
        """Check if the current constraint set is satisfiable.
        
        This method adds the additional constraints to the persistent solver
        so that get_model() can retrieve the actual model.
        
        Args:
            additional_constraints: Optional additional constraints to check
            
        Returns:
            str: 'sat', 'unsat', or 'unknown'
        """
        # Add additional constraints to the persistent solver
        if additional_constraints:
            for constraint in additional_constraints:
                if constraint is not None:
                    self.solver.add(constraint)
        
        # Check satisfiability with the persistent solver
        result = self.solver.check()
        return str(result)
    
    def get_model(self):
        """Get the current model from the solver.
        
        Returns:
            z3.ModelRef or None: Current Z3 model if available
        """
        try:
            return self.solver.model()
        except z3.Z3Exception:
            return None
    
    def create_stronger_constraint(self, isomorphic_model):
        """Create a stronger constraint to avoid specific isomorphic model.
        
        Args:
            isomorphic_model: Z3 model that was found to be isomorphic
            
        Returns:
            z3.BoolRef or None: Stronger constraint
        """
        return self._create_non_isomorphic_constraint(isomorphic_model)
    
    def _create_difference_constraint(self, previous_models):
        """Create constraint ensuring the new model differs from previous ones.
        
        Args:
            previous_models: List of Z3 models to differentiate from
            
        Returns:
            z3.BoolRef or None: Difference constraint
        """
        if not previous_models:
            return None
            
        difference_constraints = []
        
        for prev_model in previous_models:
            # Create constraints based on state differences
            state_differences = self._create_state_difference_constraints(prev_model)
            if state_differences:
                difference_constraints.extend(state_differences)
                
        if difference_constraints:
            # Filter out any None or invalid constraints - check if they are valid Z3 expressions
            valid_constraints = []
            for c in difference_constraints:
                if c is not None:
                    try:
                        # Test if it's a valid Z3 expression by trying to use it in a simple operation
                        test_expr = z3.And(c, z3.BoolVal(True))
                        valid_constraints.append(c)
                    except Exception:
                        logger.warning(f"Skipping invalid constraint: {c} (type: {type(c)})")
            
            if valid_constraints:
                if len(valid_constraints) == 1:
                    return valid_constraints[0]
                return z3.Or(valid_constraints)
        return None
    
    def _create_state_difference_constraints(self, prev_model):
        """Create constraints based on state-level differences.
        
        Args:
            prev_model: Z3 model to differentiate from
            
        Returns:
            list: List of difference constraints
        """
        constraints = []
        
        try:
            # Get semantics from the build example
            semantics = self.build_example.model_constraints.semantics
            N = self.build_example.settings.get('N', 3)
            
            # Generate constraints for world states
            if hasattr(semantics, 'is_world'):
                for combination in self._generate_input_combinations(1, N):
                    state = combination[0]
                    
                    # Get the is_world expression
                    is_world_expr = semantics.is_world(state)
                    if is_world_expr is None:
                        continue
                        
                    try:
                        prev_value = prev_model.eval(is_world_expr, model_completion=True)
                        
                        if z3.is_true(prev_value):
                            # Previous model had this as world, new model should not
                            not_world_expr = z3.Not(is_world_expr)
                            if not_world_expr is not None:
                                constraints.append(not_world_expr)
                        else:
                            # Previous model didn't have this as world, new model should
                            if is_world_expr is not None:
                                constraints.append(is_world_expr)
                    except Exception as eval_error:
                        logger.warning(f"Error evaluating is_world({state}): {eval_error}")
                        continue
                        
        except Exception as e:
            logger.warning(f"Error creating state difference constraints: {e}")
            
        return constraints
    
    def _create_non_isomorphic_constraint(self, isomorphic_model):
        """Create constraint to avoid specific isomorphic model.
        
        Args:
            isomorphic_model: Z3 model that was isomorphic
            
        Returns:
            z3.BoolRef or None: Non-isomorphic constraint
        """
        try:
            # Get semantics from the build example
            semantics = self.build_example.model_constraints.semantics
            N = self.build_example.settings.get('N', 3)
            
            # Create constraint that forces at least one difference
            difference_constraints = []
            
            if hasattr(semantics, 'is_world'):
                for combination in self._generate_input_combinations(1, N):
                    state = combination[0]
                    
                    # Get the is_world expression
                    is_world_expr = semantics.is_world(state)
                    if is_world_expr is None:
                        continue
                        
                    try:
                        iso_value = isomorphic_model.eval(is_world_expr, model_completion=True)
                        
                        if z3.is_true(iso_value):
                            not_world_expr = z3.Not(is_world_expr)
                            if not_world_expr is not None:
                                difference_constraints.append(not_world_expr)
                        else:
                            if is_world_expr is not None:
                                difference_constraints.append(is_world_expr)
                    except Exception as eval_error:
                        logger.warning(f"Error evaluating is_world({state}) in isomorphic constraint: {eval_error}")
                        continue
                        
            if difference_constraints:
                # Filter out any None or invalid constraints - check if they are valid Z3 expressions
                valid_constraints = []
                for c in difference_constraints:
                    if c is not None:
                        try:
                            # Test if it's a valid Z3 expression by trying to use it in a simple operation
                            test_expr = z3.And(c, z3.BoolVal(True))
                            valid_constraints.append(c)
                        except Exception:
                            logger.warning(f"Skipping invalid constraint: {c} (type: {type(c)})")
                
                if valid_constraints:
                    if len(valid_constraints) == 1:
                        return valid_constraints[0]
                    return z3.Or(valid_constraints)
                
        except Exception as e:
            logger.warning(f"Error creating non-isomorphic constraint: {e}")
            
        return None
    
    def _generate_input_combinations(self, arity, domain_size):
        """Generate all possible input combinations for given arity and domain.
        
        Args:
            arity: Number of arguments
            domain_size: Size of the domain (N)
            
        Returns:
            list: List of input combinations
        """
        if arity == 1:
            # For unary predicates, generate single states
            return [(i,) for i in range(domain_size)]
        else:
            # For higher arity, generate all combinations
            domain = range(domain_size)
            return list(itertools.product(domain, repeat=arity))