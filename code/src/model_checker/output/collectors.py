"""Model data collectors for extracting information from model structures."""

from typing import Dict, List, Any, Optional


class ModelDataCollector:
    """Collects and structures model data for export.
    
    This class extracts relevant information from model structures
    and formats it into a structured dictionary suitable for JSON export.
    It handles different theory types and extracts states, relations,
    propositions, and other model properties.
    """
    
    def collect_model_data(self, model_structure, example_name: str, 
                          theory_name: str) -> Dict[str, Any]:
        """Extract model data into structured format.
        
        Args:
            model_structure: The model structure object containing the model
            example_name: Name of the example
            theory_name: Name of the theory
            
        Returns:
            Dictionary containing all model data
        """
        # Check if model was found
        has_model = getattr(model_structure, 'z3_model_status', False)
        
        if not has_model:
            # Return minimal data for no model case
            return {
                "example": example_name,
                "theory": theory_name,
                "has_model": False,
                "evaluation_world": None,
                "states": {"possible": [], "impossible": [], "worlds": []},
                "relations": {},
                "propositions": {}
            }
            
        # Collect full model data
        return {
            "example": example_name,
            "theory": theory_name,
            "has_model": True,
            "evaluation_world": self._get_evaluation_world(model_structure),
            "states": self._collect_states(model_structure),
            "relations": self._collect_relations(model_structure),
            "propositions": self._collect_propositions(model_structure)
        }
        
    def _collect_states(self, model_structure) -> Dict[str, List[str]]:
        """Collect state information with types.
        
        Args:
            model_structure: The model structure
            
        Returns:
            Dictionary with possible, impossible, and world states
        """
        # Use new extraction method if available
        if hasattr(model_structure, 'extract_states'):
            return model_structure.extract_states()
        
        # Fallback to empty structure
        return {"possible": [], "impossible": [], "worlds": []}
        
    def _get_evaluation_world(self, model_structure) -> Optional[str]:
        """Get the evaluation world from the model.
        
        Args:
            model_structure: The model structure
            
        Returns:
            String representation of evaluation world or None
        """
        # Use new extraction method if available
        if hasattr(model_structure, 'extract_evaluation_world'):
            return model_structure.extract_evaluation_world()
            
        # Fallback for models without extraction method
        return None
        
    def _collect_propositions(self, model_structure) -> Dict[str, Dict[str, bool]]:
        """Collect proposition truth values at each world.
        
        Args:
            model_structure: The model structure
            
        Returns:
            Dictionary mapping propositions to their truth values at worlds
        """
        # Use new extraction method if available
        if hasattr(model_structure, 'extract_propositions'):
            return model_structure.extract_propositions()
            
        # Fallback to empty structure
        return {}
        
    def _collect_relations(self, model_structure) -> Dict[str, Any]:
        """Collect relations between states.
        
        Args:
            model_structure: The model structure
            
        Returns:
            Dictionary mapping relation names to their connections
        """
        # Use new extraction method if available
        if hasattr(model_structure, 'extract_relations'):
            return model_structure.extract_relations()
            
        # Fallback to empty structure
        return {}