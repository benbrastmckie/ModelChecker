"""
Solver management interface for iterator refactoring.

This module defines interfaces for Z3 solver lifecycle management,
ensuring proper constraint handling and solver state isolation.
"""

from abc import ABC, abstractmethod
from typing import List, Optional, Any
import z3
from contextlib import contextmanager


class SolverInterface(ABC):
    """Abstract interface for solver management."""
    
    @abstractmethod
    def push(self) -> None:
        """Push a new solver context."""
        pass
    
    @abstractmethod
    def pop(self, num: int = 1) -> None:
        """Pop solver context(s)."""
        pass
    
    @abstractmethod
    def add(self, constraint: z3.BoolRef) -> None:
        """Add a constraint to the solver."""
        pass
    
    @abstractmethod
    def check(self) -> z3.CheckSatResult:
        """Check satisfiability of current constraints."""
        pass
    
    @abstractmethod
    def model(self) -> z3.ModelRef:
        """Get the current model (only valid after SAT check)."""
        pass
    
    @abstractmethod
    def assertions(self) -> List[z3.BoolRef]:
        """Get current assertions in the solver."""
        pass
    
    @abstractmethod
    def reset(self) -> None:
        """Reset the solver to initial state."""
        pass
    
    @abstractmethod
    def set_timeout(self, timeout_ms: int) -> None:
        """Set solver timeout in milliseconds."""
        pass


class SolverManager:
    """
    Manages Z3 solver lifecycle with proper isolation.
    
    This ensures that iterator solver operations don't interfere
    with the original model's solver state.
    """
    
    def __init__(self, base_constraints: Optional[List[z3.BoolRef]] = None):
        """Initialize with optional base constraints."""
        self.solver = z3.Solver()
        self.base_constraints = base_constraints or []
        self.context_depth = 0
        
        # Add base constraints if provided
        if self.base_constraints:
            for constraint in self.base_constraints:
                self.solver.add(constraint)
    
    def push(self) -> None:
        """Push a new solver context."""
        self.solver.push()
        self.context_depth += 1
    
    def pop(self, num: int = 1) -> None:
        """Pop solver context(s)."""
        if num > self.context_depth:
            raise ValueError(f"Cannot pop {num} contexts, only {self.context_depth} available")
        self.solver.pop(num)
        self.context_depth -= num
    
    def add(self, constraint: z3.BoolRef) -> None:
        """Add a constraint to the solver."""
        self.solver.add(constraint)
    
    def check(self) -> z3.CheckSatResult:
        """Check satisfiability of current constraints."""
        return self.solver.check()
    
    def model(self) -> z3.ModelRef:
        """Get the current model (only valid after SAT check)."""
        return self.solver.model()
    
    def assertions(self) -> List[z3.BoolRef]:
        """Get current assertions in the solver."""
        return self.solver.assertions()
    
    def reset(self) -> None:
        """Reset the solver to initial state."""
        self.solver.reset()
        self.context_depth = 0
        # Re-add base constraints
        for constraint in self.base_constraints:
            self.solver.add(constraint)
    
    def set_timeout(self, timeout_ms: int) -> None:
        """Set solver timeout in milliseconds."""
        self.solver.set("timeout", timeout_ms)
    
    @contextmanager
    def isolated_context(self):
        """
        Context manager for isolated solver operations.
        
        Usage:
            with solver_manager.isolated_context():
                solver_manager.add(new_constraint)
                result = solver_manager.check()
                # Context automatically popped on exit
        """
        self.push()
        try:
            yield self
        finally:
            self.pop()
    
    def fork(self) -> 'SolverManager':
        """
        Create a new solver manager with the same base constraints.
        
        This is useful for parallel exploration of different constraint paths.
        """
        # Get current assertions as base for new solver
        current_assertions = self.assertions()
        return SolverManager(current_assertions)
    
    @property
    def is_clean(self) -> bool:
        """Check if solver is in clean state (no pushed contexts)."""
        return self.context_depth == 0