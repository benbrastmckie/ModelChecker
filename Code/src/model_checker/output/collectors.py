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
        states = {"possible": [], "impossible": [], "worlds": []}
        
        # Get all states if method exists
        if hasattr(model_structure, 'get_all_N_states'):
            all_states = model_structure.get_all_N_states()
            
            for state_num in all_states:
                state_name = f"s{state_num}"
                
                # Check if possible
                if hasattr(model_structure, 'is_possible_state'):
                    if model_structure.is_possible_state(state_num):
                        states["possible"].append(state_name)
                    else:
                        states["impossible"].append(state_name)
                        
                # Check if world state
                if hasattr(model_structure, 'is_world_state'):
                    if model_structure.is_world_state(state_num):
                        states["worlds"].append(state_name)
                        
        return states
        
    def _get_evaluation_world(self, model_structure) -> Optional[str]:
        """Get the evaluation world from the model.
        
        Args:
            model_structure: The model structure
            
        Returns:
            String representation of evaluation world or None
        """
        if not getattr(model_structure, 'z3_model_status', False):
            return None
            
        # Try to get main world
        if hasattr(model_structure, 'z3_main_world'):
            main_world = model_structure.z3_main_world
            if main_world is not None and hasattr(main_world, 'as_long'):
                return f"s{main_world.as_long()}"
                
        return None
        
    def _collect_propositions(self, model_structure) -> Dict[str, Dict[str, bool]]:
        """Collect proposition truth values at each world.
        
        Args:
            model_structure: The model structure
            
        Returns:
            Dictionary mapping propositions to their truth values at worlds
        """
        propositions = {}
        
        # Check if syntax with propositions exists
        if hasattr(model_structure, 'syntax') and hasattr(model_structure.syntax, 'propositions'):
            prop_dict = model_structure.syntax.propositions
            
            # Get world states
            world_states = []
            if hasattr(model_structure, 'get_all_N_states'):
                all_states = model_structure.get_all_N_states()
                for state in all_states:
                    if hasattr(model_structure, 'is_world_state'):
                        if model_structure.is_world_state(state):
                            world_states.append(state)
                            
            # Collect truth values
            for prop_name, prop_obj in prop_dict.items():
                if hasattr(prop_obj, 'letter'):
                    letter = prop_obj.letter
                    propositions[letter] = {}
                    
                    # Check truth at each world
                    for world in world_states:
                        state_name = f"s{world}"
                        if hasattr(prop_obj, 'is_true_at'):
                            propositions[letter][state_name] = prop_obj.is_true_at(world)
                            
        return propositions
        
    def _collect_relations(self, model_structure) -> Dict[str, Dict[str, List[str]]]:
        """Collect relations between states.
        
        Args:
            model_structure: The model structure
            
        Returns:
            Dictionary mapping relation names to their connections
        """
        relations = {}
        
        # Get all states
        if not hasattr(model_structure, 'get_all_N_states'):
            return relations
            
        all_states = model_structure.get_all_N_states()
        
        # Check for different relation types based on theory
        
        # Modal logic R relation
        if hasattr(model_structure, 'R') and hasattr(model_structure.R, 'related'):
            r_connections = {}
            
            for state1 in all_states:
                if hasattr(model_structure, 'is_world_state'):
                    if not model_structure.is_world_state(state1):
                        continue
                        
                state1_name = f"s{state1}"
                r_connections[state1_name] = []
                
                for state2 in all_states:
                    if hasattr(model_structure, 'is_world_state'):
                        if not model_structure.is_world_state(state2):
                            continue
                            
                    if model_structure.R.related(state1, state2):
                        r_connections[state1_name].append(f"s{state2}")
                        
            if r_connections:
                relations["R"] = r_connections
                
        # Add other relation types as needed (e.g., temporal relations)
        # This can be extended for different theory types
        
        return relations