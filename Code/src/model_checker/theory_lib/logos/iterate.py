"""Logos theory specific model iteration implementation.

This module provides the LogosModelIterator implementation which handles:
1. Detecting differences between models using logos theory semantics
2. Creating constraints to differentiate models with logos theory primitives
3. Checking model isomorphism for logos theory models
"""

import z3
import sys
import logging

from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_substates, pretty_set_print

# Configure logging
logger = logging.getLogger(__name__)


class LogosModelIterator(BaseModelIterator):
    """Model iterator for the logos theory.
    
    This class extends BaseModelIterator with logos theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for logos theory models.
    
    The logos theory uses hyperintensional semantics with:
    - States represented as bit vectors
    - Verification and falsification as primitive relations
    - Possible worlds as maximal possible states
    - Part-whole relationships between states
    - Support for modal, constitutive, and counterfactual operators
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two logos theory model structures.
        
        For logos theory, this focuses on:
        - Changes in which states are worlds
        - Changes in which states are possible
        - Changes in verification and falsification of sentence letters
        - Changes in part-whole relationships
        - Changes in modal accessibility relations
        - Changes in constitutive relations (ground, essence)
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Try to use the theory-specific detect_model_differences method on the structure
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    return differences
            except Exception as e:
                logger.warning(f"Error in logos theory difference detection: {e}")
        
        # Fall back to our own implementation
        differences = self._calculate_logos_differences(new_structure, previous_structure)
        
        return differences
    
    def _calculate_logos_differences(self, new_structure, previous_structure):
        """Logos theory specific implementation of difference detection.
        
        This is more sophisticated than the base _calculate_basic_differences method
        as it understands logos theory semantics like verifiers, falsifiers, and
        hyperintensional relations.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences with logos theory semantics
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Get semantics object early
        semantics = new_structure.semantics
        
        # Initialize logos theory-specific differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "sentence_letters": {},
            "parthood": {},
            "verify": {},
            "falsify": {}
        }
        
        # Compare worlds and possible states
        old_worlds = set(getattr(previous_structure, "z3_world_states", []))
        new_worlds = set(getattr(new_structure, "z3_world_states", []))
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Compare possible states
        old_states = set(getattr(previous_structure, "z3_possible_states", []))
        new_states = set(getattr(new_structure, "z3_possible_states", []))
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare sentence letter interpretations using verify/falsify
        for letter in new_structure.sentence_letters:
            try:
                # Get the Z3 atom for this sentence letter
                if hasattr(letter, 'sentence_letter') and letter.sentence_letter is not None:
                    atom = letter.sentence_letter
                else:
                    # Skip if we can't get the atom
                    continue
                
                # Check verification changes
                verify_diffs = {}
                for state in new_structure.all_states:
                    old_verify = previous_model.eval(semantics.verify(state, atom), model_completion=True)
                    new_verify = new_model.eval(semantics.verify(state, atom), model_completion=True)
                    
                    if bool(old_verify) != bool(new_verify):
                        state_str = bitvec_to_substates(state, new_structure.N)
                        verify_diffs[state_str] = {
                            "old": bool(old_verify),
                            "new": bool(new_verify)
                        }
                
                if verify_diffs:
                    differences["verify"][str(letter)] = verify_diffs
                
                # Check falsification changes
                falsify_diffs = {}
                for state in new_structure.all_states:
                    old_falsify = previous_model.eval(semantics.falsify(state, atom), model_completion=True)
                    new_falsify = new_model.eval(semantics.falsify(state, atom), model_completion=True)
                    
                    if bool(old_falsify) != bool(new_falsify):
                        state_str = bitvec_to_substates(state, new_structure.N)
                        falsify_diffs[state_str] = {
                            "old": bool(old_falsify),
                            "new": bool(new_falsify)
                        }
                
                if falsify_diffs:
                    differences["falsify"][str(letter)] = falsify_diffs
                    
            except z3.Z3Exception:
                pass
        
        # Compare parthood relations
        semantics = new_structure.semantics
        parthood_diffs = {}
        for s1 in new_structure.all_states:
            for s2 in new_structure.all_states:
                if s1 == s2:
                    continue
                    
                try:
                    old_part = previous_model.eval(semantics.is_part_of(s1, s2), model_completion=True)
                    new_part = new_model.eval(semantics.is_part_of(s1, s2), model_completion=True)
                    
                    if bool(old_part) != bool(new_part):
                        s1_str = bitvec_to_substates(s1, new_structure.N)
                        s2_str = bitvec_to_substates(s2, new_structure.N)
                        parthood_diffs[f"{s1_str} ⊑ {s2_str}"] = {
                            "old": bool(old_part),
                            "new": bool(new_part)
                        }
                except z3.Z3Exception:
                    pass
        
        if parthood_diffs:
            differences["parthood"] = parthood_diffs
        
        return differences
    
    
    
    


# Module-level convenience function
def iterate_example(example, max_iterations=None):
    """Iterate a logos theory example to find multiple models.
    
    Args:
        example: A BuildExample instance with logos theory.
        max_iterations: Maximum number of models to find.
        
    Returns:
        list: List of model structures with distinct models.
    """
    if max_iterations is not None:
        # Update the iterate setting
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator and run
    iterator = LogosModelIterator(example)
    models = iterator.iterate()
    
    # Store the iterator on the example for access to debug messages
    example._iterator = iterator
    
    return models