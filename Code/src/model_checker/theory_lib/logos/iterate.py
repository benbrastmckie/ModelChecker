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
    
    def _create_difference_constraint(self, previous_models):
        """Create a Z3 constraint requiring difference from all previous models.
        
        For logos theory, we create constraints that require at least one of:
        - Different verification/falsification for some sentence letter
        - Different world structure
        - Different possible states
        
        Args:
            previous_models: List of Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint expression
        """
        semantics = self.build_example.model_structure.semantics
        all_states = self.build_example.model_structure.all_states
        sentence_letters = self.build_example.model_structure.sentence_letters
        
        # For each previous model, create a constraint that ensures difference
        model_constraints = []
        
        for prev_model in previous_models:
            differences = []
            
            # Require different verification for at least one state/letter pair
            for state in all_states:
                for letter in sentence_letters:
                    # Get the Z3 atom for this sentence letter
                    if hasattr(letter, 'sentence_letter') and letter.sentence_letter is not None:
                        atom = letter.sentence_letter
                    else:
                        continue
                    
                    prev_verify = prev_model.eval(semantics.verify(state, atom), model_completion=True)
                    differences.append(
                        semantics.verify(state, atom) != prev_verify
                    )
            
            # Require different falsification for at least one state/letter pair
            for state in all_states:
                for letter in sentence_letters:
                    # Get the Z3 atom for this sentence letter
                    if hasattr(letter, 'sentence_letter') and letter.sentence_letter is not None:
                        atom = letter.sentence_letter
                    else:
                        continue
                        
                    prev_falsify = prev_model.eval(semantics.falsify(state, atom), model_completion=True)
                    differences.append(
                        semantics.falsify(state, atom) != prev_falsify
                    )
            
            # Require different world status for at least one state
            for state in all_states:
                prev_is_world = prev_model.eval(semantics.is_world(state), model_completion=True)
                differences.append(
                    semantics.is_world(state) != prev_is_world
                )
            
            # Require different possible status for at least one state
            for state in all_states:
                prev_possible = prev_model.eval(semantics.possible(state), model_completion=True)
                differences.append(
                    semantics.possible(state) != prev_possible
                )
            
            # Require at least one difference
            if differences:
                model_constraints.append(z3.Or(*differences))
        
        # Must differ from all previous models
        return z3.And(*model_constraints) if model_constraints else z3.BoolVal(True)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create a constraint that forces structural differences to avoid isomorphism.
        
        For logos theory, we focus on breaking symmetries in the state space
        by requiring specific structural differences.
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        try:
            semantics = self.build_example.model_structure.semantics
            all_states = self.build_example.model_structure.all_states
            
            # Create constraints that break symmetries
            constraints = []
            
            # Try to force a different number of worlds
            world_count = sum(1 for state in all_states
                            if bool(z3_model.eval(semantics.is_world(state), model_completion=True)))
            
            current_world_count = z3.Sum([z3.If(semantics.is_world(state), 1, 0) 
                                        for state in all_states])
            
            constraints.append(current_world_count != world_count)
            
            # Try to force different possible state count
            possible_count = sum(1 for state in all_states
                               if bool(z3_model.eval(semantics.possible(state), model_completion=True)))
            
            current_possible_count = z3.Sum([z3.If(semantics.possible(state), 1, 0)
                                           for state in all_states])
            
            constraints.append(current_possible_count != possible_count)
            
            return z3.Or(*constraints) if constraints else None
            
        except Exception as e:
            logger.warning(f"Failed to create non-isomorphic constraint: {e}")
            return None
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints after multiple isomorphism failures.
        
        This is called when we've found too many isomorphic models in a row.
        For logos theory, we create more aggressive constraints that force
        significant structural differences.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        try:
            semantics = self.build_example.model_structure.semantics
            all_states = self.build_example.model_structure.all_states
            sentence_letters = self.build_example.model_structure.sentence_letters
            
            # Create very strong constraints
            constraints = []
            
            # Force different world states
            for state in all_states[:min(3, len(all_states))]:  # Limit to first 3 states
                prev_is_world = isomorphic_model.eval(semantics.is_world(state), model_completion=True)
                constraints.append(semantics.is_world(state) != prev_is_world)
            
            # Force different possible state structure
            possible_count = sum(1 for state in all_states
                               if bool(isomorphic_model.eval(semantics.possible(state), model_completion=True)))
            
            current_possible_count = z3.Sum([z3.If(semantics.possible(state), 1, 0) 
                                           for state in all_states])
            
            # Require significantly different number of possible states (at least 2 difference)
            constraints.append(z3.Or(
                current_possible_count >= possible_count + 2,
                current_possible_count <= possible_count - 2
            ))
            
            return z3.And(*constraints) if constraints else None
            
        except Exception as e:
            logger.warning(f"Failed to create stronger constraint: {e}")
            return None


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