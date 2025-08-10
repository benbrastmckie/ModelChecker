"""
Model access interface for iterator refactoring.

This module defines interfaces for accessing model structures without
direct attribute access, enabling clean separation between iterator
and model implementation details.
"""

from abc import ABC, abstractmethod
from typing import Dict, Set, List, Any, Optional
import z3


class ModelInterface(ABC):
    """Abstract interface for model structure access."""
    
    @abstractmethod
    def get_worlds(self) -> Set[str]:
        """Get the set of world states."""
        pass
    
    @abstractmethod
    def get_possible_worlds(self) -> Set[str]:
        """Get the set of possible world states."""
        pass
    
    @abstractmethod
    def get_impossible_worlds(self) -> Set[str]:
        """Get the set of impossible world states."""
        pass
    
    @abstractmethod
    def get_designated_world(self) -> str:
        """Get the designated world."""
        pass
    
    @abstractmethod
    def get_verifier_sets(self) -> Dict[str, Set[str]]:
        """Get verifier sets for all propositions."""
        pass
    
    @abstractmethod
    def get_falsifier_sets(self) -> Dict[str, Set[str]]:
        """Get falsifier sets for all propositions."""
        pass
    
    @abstractmethod
    def get_relation(self, relation_name: str) -> Set[tuple]:
        """Get a specific semantic relation."""
        pass
    
    @abstractmethod
    def get_z3_model(self) -> Optional[z3.ModelRef]:
        """Get the underlying Z3 model if available."""
        pass
    
    @abstractmethod
    def get_solver(self) -> Optional[z3.Solver]:
        """Get the Z3 solver if available."""
        pass
    
    @abstractmethod
    def get_constraints(self) -> List[z3.BoolRef]:
        """Get the list of constraints used to build this model."""
        pass


class ModelAccessor:
    """
    Adapter that provides ModelInterface access to existing model structures.
    
    This allows gradual migration from direct attribute access to interface-based access.
    """
    
    def __init__(self, model_structure):
        """Initialize with an existing model structure."""
        self.model = model_structure
    
    def get_worlds(self) -> Set[str]:
        """Get the set of world states."""
        # Handle different attribute names for compatibility
        if hasattr(self.model, 'z3_world_states'):
            return set(self.model.z3_world_states.keys())
        elif hasattr(self.model, 'world_states'):
            return set(self.model.world_states.keys())
        else:
            raise AttributeError("Model structure has no world states attribute")
    
    def get_possible_worlds(self) -> Set[str]:
        """Get the set of possible world states."""
        if hasattr(self.model, 'z3_possible_states'):
            return self.model.z3_possible_states
        elif hasattr(self.model, 'possible_states'):
            return self.model.possible_states
        else:
            # Fallback: possible worlds are worlds that are marked as possible
            worlds = self.get_worlds()
            return {w for w in worlds if self._is_possible(w)}
    
    def get_impossible_worlds(self) -> Set[str]:
        """Get the set of impossible world states."""
        if hasattr(self.model, 'z3_impossible_states'):
            return self.model.z3_impossible_states
        elif hasattr(self.model, 'impossible_states'):
            return self.model.impossible_states
        else:
            # Calculate as complement of possible worlds
            return self.get_worlds() - self.get_possible_worlds()
    
    def get_designated_world(self) -> str:
        """Get the designated world."""
        if hasattr(self.model, 'designated_world'):
            return self.model.designated_world
        elif hasattr(self.model, 'z3_designated_world'):
            return self.model.z3_designated_world
        else:
            # Common default
            return "□"
    
    def get_verifier_sets(self) -> Dict[str, Set[str]]:
        """Get verifier sets for all propositions."""
        if hasattr(self.model, 'z3_verify_sets'):
            return self.model.z3_verify_sets
        elif hasattr(self.model, 'verify_sets'):
            return self.model.verify_sets
        else:
            raise AttributeError("Model structure has no verifier sets")
    
    def get_falsifier_sets(self) -> Dict[str, Set[str]]:
        """Get falsifier sets for all propositions."""
        if hasattr(self.model, 'z3_falsify_sets'):
            return self.model.z3_falsify_sets
        elif hasattr(self.model, 'falsify_sets'):
            return self.model.falsify_sets
        else:
            raise AttributeError("Model structure has no falsifier sets")
    
    def get_relation(self, relation_name: str) -> Set[tuple]:
        """Get a specific semantic relation."""
        # Try various attribute patterns
        attr_names = [
            f"z3_{relation_name}",
            relation_name,
            f"{relation_name}_relation"
        ]
        
        for attr in attr_names:
            if hasattr(self.model, attr):
                return getattr(self.model, attr)
        
        # Check if it's in a relations dict
        if hasattr(self.model, 'relations') and relation_name in self.model.relations:
            return self.model.relations[relation_name]
        
        return set()  # Empty relation if not found
    
    def get_z3_model(self) -> Optional[z3.ModelRef]:
        """Get the underlying Z3 model if available."""
        if hasattr(self.model, 'z3_model'):
            return self.model.z3_model
        return None
    
    def get_solver(self) -> Optional[z3.Solver]:
        """Get the Z3 solver if available."""
        # Try different solver attributes
        for attr in ['solver', 'stored_solver', 'z3_solver']:
            if hasattr(self.model, attr):
                solver = getattr(self.model, attr)
                if solver is not None:
                    return solver
        return None
    
    def get_constraints(self) -> List[z3.BoolRef]:
        """Get the list of constraints used to build this model."""
        if hasattr(self.model, 'constraints'):
            return self.model.constraints
        elif hasattr(self.model, 'z3_constraints'):
            return self.model.z3_constraints
        else:
            return []
    
    def _is_possible(self, world: str) -> bool:
        """Check if a world is possible (helper method)."""
        # Check world_states dict if available
        if hasattr(self.model, 'z3_world_states'):
            world_data = self.model.z3_world_states.get(world, {})
            return world_data.get('possible', False)
        return True  # Default to possible if no info