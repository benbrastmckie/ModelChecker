"""Abstract base class for model iterators.

This module defines the abstract interface that all theory-specific
iterators must implement.
"""

from typing import List, Optional, Any
import z3


class BaseModelIterator:
    """Abstract base class for model iteration.
    
    Theory-specific iterators must extend this class and implement
    the abstract methods to provide theory-specific behavior.
    """
    
    def __init__(self, build_example):
        """Initialize the iterator with a build example.
        
        Args:
            build_example: BuildExample instance containing the initial model
        """
        self.build_example = build_example
        self.found_models = []
        self.debug_messages = []
    
    def _calculate_differences(self, new_structure, previous_structure) -> dict:
        """Calculate semantic differences between two models.
        
        This method should identify meaningful differences between models
        according to the specific theory's semantics.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            Dictionary describing the differences
        """
        raise NotImplementedError("Subclasses must implement _calculate_differences")
    
    def _create_difference_constraint(self, previous_models: List[z3.ModelRef]) -> z3.BoolRef:
        """Create constraints ensuring the next model differs from previous ones.
        
        This method should generate Z3 constraints that, when added to the
        solver, ensure the next model found will be structurally different
        from all previous models.
        
        Args:
            previous_models: List of Z3 models found so far
            
        Returns:
            Z3 constraint ensuring difference
        """
        raise NotImplementedError("Subclasses must implement _create_difference_constraint")
    
    def _create_non_isomorphic_constraint(self, z3_model: z3.ModelRef) -> z3.BoolRef:
        """Create constraints preventing isomorphic models.
        
        This method should generate constraints that prevent finding models
        that are structurally identical (isomorphic) to the given model.
        
        Args:
            z3_model: Z3 model to avoid isomorphism with
            
        Returns:
            Z3 constraint preventing isomorphism
        """
        raise NotImplementedError("Subclasses must implement _create_non_isomorphic_constraint")
    
    def _create_stronger_constraint(self, isomorphic_model: z3.ModelRef) -> Optional[z3.BoolRef]:
        """Create stronger constraints after finding isomorphic models.
        
        This optional method can be overridden to provide theory-specific
        strategies for escaping loops of isomorphic models.
        
        Args:
            isomorphic_model: The isomorphic model to escape from
            
        Returns:
            Stronger constraint or None
        """
        # Default implementation returns None (no stronger constraint)
        return None
    
    def iterate(self) -> List[Any]:
        """Perform model iteration to find multiple distinct models.
        
        This is the main entry point for iteration. Implementations should
        find up to max_iterations distinct models.
        
        Returns:
            List of distinct model structures found
        """
        raise NotImplementedError("Subclasses must implement iterate")