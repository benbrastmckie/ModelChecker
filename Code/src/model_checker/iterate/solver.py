"""Solver management for the iteration framework.

This module provides utilities for managing Z3 solver instances during
model iteration, including constraint preservation and solver lifecycle.
"""

import z3
from typing import List, Optional, Any
import logging

logger = logging.getLogger(__name__)


class IterationSolver:
    """Manages Z3 solver lifecycle for model iteration.
    
    This class encapsulates solver creation, constraint management,
    and solver state preservation during the iteration process.
    """
    
    def __init__(self, build_example):
        """Initialize solver with constraints from build example.
        
        Args:
            build_example: The BuildExample instance containing initial constraints
        """
        self.build_example = build_example
        self.original_constraints = self._extract_original_constraints()
        self.solver = self._create_persistent_solver()
        self.iteration_constraints = []  # Track constraints added during iteration
    
    def _extract_original_constraints(self) -> List[z3.BoolRef]:
        """Extract the original model constraints from the build example.
        
        Returns:
            List of Z3 constraints from the original model
        """
        constraints = []
        
        # Get constraints from model_constraints
        if hasattr(self.build_example, 'model_constraints'):
            model_constraints = self.build_example.model_constraints
            
            # Get raw constraints
            if hasattr(model_constraints, 'constraints'):
                for constraint in model_constraints.constraints:
                    if constraint is not None:
                        constraints.append(constraint)
            
            # Get solver assertions if available
            if hasattr(model_constraints, 'solver') and model_constraints.solver:
                try:
                    assertions = model_constraints.solver.assertions()
                    constraints.extend(assertions)
                except:
                    pass
        
        # Get constraints from the Z3 model's solver if available
        if hasattr(self.build_example, 'model_structure'):
            model_structure = self.build_example.model_structure
            if hasattr(model_structure, 'z3_model') and model_structure.z3_model:
                # The model itself doesn't contain constraints, but we can get them
                # from the solver that generated it if available
                pass
        
        return constraints
    
    def _create_persistent_solver(self) -> z3.Solver:
        """Create a new solver with original constraints.
        
        This creates a fresh solver instance and adds all the original
        constraints from the first model. This solver will persist
        throughout the iteration process.
        
        Returns:
            Z3 Solver instance with original constraints
        """
        solver = z3.Solver()
        
        # Add all original constraints
        for constraint in self.original_constraints:
            solver.add(constraint)
        
        # Configure solver settings for iteration
        # Use incremental solving for better performance
        solver.set("timeout", 5000)  # 5 second timeout
        
        return solver
    
    def add_iteration_constraint(self, constraint: z3.BoolRef):
        """Add a constraint for iteration (e.g., to ensure difference).
        
        Args:
            constraint: Z3 constraint to add
        """
        self.solver.add(constraint)
        self.iteration_constraints.append(constraint)
    
    def check_sat(self, timeout: Optional[int] = None) -> z3.CheckSatResult:
        """Check if the current constraints are satisfiable.
        
        Args:
            timeout: Optional timeout in milliseconds
            
        Returns:
            Z3 check result (sat, unsat, or unknown)
        """
        if timeout:
            old_timeout = self.solver.get_param("timeout")
            self.solver.set("timeout", timeout)
            result = self.solver.check()
            self.solver.set("timeout", old_timeout)
            return result
        else:
            return self.solver.check()
    
    def get_model(self) -> Optional[z3.ModelRef]:
        """Get the current model if satisfiable.
        
        Returns:
            Z3 model if satisfiable, None otherwise
        """
        if self.solver.check() == z3.sat:
            return self.solver.model()
        return None
    
    def push_context(self):
        """Push a new context on the solver stack."""
        self.solver.push()
    
    def pop_context(self):
        """Pop a context from the solver stack."""
        self.solver.pop()
    
    def get_assertions(self) -> List[z3.BoolRef]:
        """Get all current assertions in the solver.
        
        Returns:
            List of Z3 constraints currently in solver
        """
        return self.solver.assertions()
    
    def get_num_assertions(self) -> int:
        """Get the number of assertions in the solver.
        
        Returns:
            Number of constraints in solver
        """
        return len(self.solver.assertions())
    
    def reset_to_original(self):
        """Reset solver to only original constraints.
        
        This removes all iteration constraints and resets to the
        initial state with only the original model constraints.
        """
        self.solver = self._create_persistent_solver()
        self.iteration_constraints = []
    
    def clone(self) -> 'IterationSolver':
        """Create a copy of this solver with all current constraints.
        
        Returns:
            New IterationSolver instance with same constraints
        """
        new_solver = IterationSolver.__new__(IterationSolver)
        new_solver.build_example = self.build_example
        new_solver.original_constraints = self.original_constraints.copy()
        new_solver.iteration_constraints = self.iteration_constraints.copy()
        
        # Create new solver with all constraints
        new_solver.solver = z3.Solver()
        for constraint in self.original_constraints:
            new_solver.solver.add(constraint)
        for constraint in self.iteration_constraints:
            new_solver.solver.add(constraint)
        
        return new_solver