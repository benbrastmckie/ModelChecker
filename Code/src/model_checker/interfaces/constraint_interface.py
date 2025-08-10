"""
Constraint building interface for iterator refactoring.

This module defines interfaces for building and managing constraints
in a theory-agnostic way, reducing duplication across theory implementations.
"""

from abc import ABC, abstractmethod
from typing import Dict, Set, List, Any, Optional, Callable
import z3


class ConstraintInterface(ABC):
    """Abstract interface for constraint generation."""
    
    @abstractmethod
    def create_difference_constraint(self, 
                                   current_model: Any,
                                   previous_models: List[Any]) -> z3.BoolRef:
        """Create constraint ensuring difference from previous models."""
        pass
    
    @abstractmethod
    def create_isomorphism_constraint(self,
                                    model1: Any,
                                    model2: Any) -> z3.BoolRef:
        """Create constraint preventing isomorphic models."""
        pass
    
    @abstractmethod
    def create_validity_constraint(self, model: Any) -> z3.BoolRef:
        """Create constraint ensuring model validity."""
        pass


class ConstraintBuilder:
    """
    Provides common constraint building patterns for iteration.
    
    This reduces duplication across theory implementations by providing
    reusable constraint building blocks.
    """
    
    def __init__(self, theory_name: str = "default"):
        """Initialize with theory name for debugging."""
        self.theory_name = theory_name
    
    def create_state_difference(self,
                              states1: Set[str],
                              states2: Set[str],
                              state_vars: Dict[str, z3.BoolRef]) -> z3.BoolRef:
        """
        Create constraint ensuring different state sets.
        
        Args:
            states1: First set of states
            states2: Second set of states  
            state_vars: Mapping from state names to Z3 variables
            
        Returns:
            Z3 constraint ensuring the sets differ
        """
        differences = []
        
        # States in first but not second
        for state in states1 - states2:
            if state in state_vars:
                differences.append(z3.Not(state_vars[state]))
        
        # States in second but not first
        for state in states2 - states1:
            if state in state_vars:
                differences.append(state_vars[state])
        
        return z3.Or(*differences) if differences else z3.BoolVal(False)
    
    def create_relation_difference(self,
                                 rel1: Set[tuple],
                                 rel2: Set[tuple],
                                 rel_var_func: Callable[[tuple], z3.BoolRef]) -> z3.BoolRef:
        """
        Create constraint ensuring different relations.
        
        Args:
            rel1: First relation (set of tuples)
            rel2: Second relation (set of tuples)
            rel_var_func: Function mapping relation tuples to Z3 variables
            
        Returns:
            Z3 constraint ensuring the relations differ
        """
        differences = []
        
        # Tuples in first but not second
        for pair in rel1 - rel2:
            try:
                var = rel_var_func(pair)
                differences.append(z3.Not(var))
            except (KeyError, ValueError):
                continue
        
        # Tuples in second but not first
        for pair in rel2 - rel1:
            try:
                var = rel_var_func(pair)
                differences.append(var)
            except (KeyError, ValueError):
                continue
        
        return z3.Or(*differences) if differences else z3.BoolVal(False)
    
    def create_set_membership_difference(self,
                                       elem: str,
                                       set1: Set[str],
                                       set2: Set[str],
                                       membership_var: z3.BoolRef) -> z3.BoolRef:
        """
        Create constraint for element membership difference between sets.
        
        Args:
            elem: Element to check
            set1: First set
            set2: Second set
            membership_var: Z3 variable for membership
            
        Returns:
            Z3 constraint ensuring different membership
        """
        in_set1 = elem in set1
        in_set2 = elem in set2
        
        if in_set1 != in_set2:
            # Different membership - require var to match set2
            return membership_var if in_set2 else z3.Not(membership_var)
        else:
            # Same membership - no constraint
            return z3.BoolVal(True)
    
    def create_non_empty_constraint(self,
                                  set_vars: Dict[str, z3.BoolRef],
                                  min_size: int = 1) -> z3.BoolRef:
        """
        Create constraint ensuring set has minimum size.
        
        Args:
            set_vars: Mapping from elements to membership variables
            min_size: Minimum required size
            
        Returns:
            Z3 constraint ensuring minimum size
        """
        if min_size <= 0:
            return z3.BoolVal(True)
        
        # At least min_size elements must be true
        return z3.AtLeast(*set_vars.values(), min_size)
    
    def create_symmetry_breaking(self,
                               states: List[str],
                               state_vars: Dict[str, z3.BoolRef]) -> z3.BoolRef:
        """
        Create symmetry breaking constraints for states.
        
        This helps avoid exploring equivalent models by imposing
        an arbitrary ordering on symmetric elements.
        
        Args:
            states: Ordered list of state names
            state_vars: Mapping from states to Z3 variables
            
        Returns:
            Z3 constraint breaking symmetries
        """
        constraints = []
        
        # Lexicographic ordering on state inclusion
        for i in range(len(states) - 1):
            if states[i] in state_vars and states[i+1] in state_vars:
                # If state i+1 is included, state i must be included
                constraints.append(
                    z3.Implies(state_vars[states[i+1]], state_vars[states[i]])
                )
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def combine_constraints(self, constraints: List[z3.BoolRef]) -> z3.BoolRef:
        """
        Safely combine multiple constraints with AND.
        
        Args:
            constraints: List of Z3 constraints
            
        Returns:
            Combined constraint
        """
        # Filter out trivial True constraints
        non_trivial = [c for c in constraints if not z3.is_true(c)]
        
        if not non_trivial:
            return z3.BoolVal(True)
        elif len(non_trivial) == 1:
            return non_trivial[0]
        else:
            return z3.And(*non_trivial)