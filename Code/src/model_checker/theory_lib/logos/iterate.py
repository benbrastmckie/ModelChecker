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
    
    This class extends CoreModelIterator with logos theory-specific
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
        """Create constraints requiring difference from previous models.
        
        This implements a smart ordering of constraint generators based on
        the master branch approach. It tries simpler constraints first
        (world count, letter values) before more complex structural ones.
        
        Args:
            previous_models: List of Z3 models found so far
            
        Returns:
            Z3 constraint requiring structural difference
        """
        constraints = []
        
        # Get current semantics
        semantics = self.build_example.model_constraints.semantics
        
        # Try different types of constraints in order of complexity
        for prev_model in previous_models:
            model_constraints = []
            
            # 1. World count constraint (simplest)
            world_count_constraint = self._create_world_count_constraint(prev_model, semantics)
            if world_count_constraint is not None:
                model_constraints.append(world_count_constraint)
            
            # 2. Letter value constraints (verify/falsify differences)
            letter_constraints = self._create_letter_value_constraints(prev_model, semantics)
            if letter_constraints:
                model_constraints.extend(letter_constraints)
            
            # 3. Structural constraints (more complex)
            if len(model_constraints) < 5:  # Only add if we need more constraints
                structural_constraints = self._create_structural_constraints(prev_model, semantics)
                if structural_constraints:
                    model_constraints.extend(structural_constraints[:5-len(model_constraints)])
            
            # Combine constraints for this model
            if model_constraints:
                constraints.append(z3.Or(*model_constraints))
        
        # All models must be different
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def _create_world_count_constraint(self, prev_model, semantics):
        """Create constraint on different number of worlds."""
        # Count worlds in previous model
        prev_world_count = 0
        for state in range(2**semantics.N):
            if z3.is_true(prev_model.eval(semantics.is_world(state), model_completion=True)):
                prev_world_count += 1
        
        # Current model must have different number of worlds
        current_world_count = z3.Sum([
            z3.If(semantics.is_world(state), 1, 0) 
            for state in range(2**semantics.N)
        ])
        
        return current_world_count != prev_world_count
    
    def _create_letter_value_constraints(self, prev_model, semantics):
        """Create constraints on verify/falsify values differing."""
        constraints = []
        
        # Get sentence letters from syntax
        syntax = self.build_example.example_syntax
        if not hasattr(syntax, 'sentence_letters'):
            return constraints
        
        for letter_obj in syntax.sentence_letters:
            if hasattr(letter_obj, 'sentence_letter'):
                atom = letter_obj.sentence_letter
                
                # Check each state
                for state in range(2**semantics.N):
                    # Get previous values
                    prev_verify = prev_model.eval(
                        semantics.verify(state, atom), 
                        model_completion=True
                    )
                    prev_falsify = prev_model.eval(
                        semantics.falsify(state, atom), 
                        model_completion=True
                    )
                    
                    # Create constraints for differences
                    constraints.append(
                        semantics.verify(state, atom) != prev_verify
                    )
                    constraints.append(
                        semantics.falsify(state, atom) != prev_falsify
                    )
        
        return constraints
    
    def _create_structural_constraints(self, prev_model, semantics):
        """Create constraints on structural differences (parthood, etc)."""
        constraints = []
        
        # Parthood relation differences
        for s1 in range(2**semantics.N):
            for s2 in range(2**semantics.N):
                if s1 != s2:
                    prev_part = prev_model.eval(
                        semantics.is_part_of(s1, s2),
                        model_completion=True
                    )
                    constraints.append(
                        semantics.is_part_of(s1, s2) != prev_part
                    )
        
        return constraints
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraint preventing isomorphic models.
        
        For logos theory, isomorphism means there's a permutation of states
        that preserves all relations (verify, falsify, parthood, etc).
        
        Args:
            z3_model: The Z3 model to constrain against
            
        Returns:
            Z3 constraint preventing isomorphism
        """
        # For now, return a simple constraint
        # Full isomorphism checking would be more complex
        return z3.BoolVal(True)
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models.
        
        In logos theory, a stronger model typically has more verifiers
        or fewer falsifiers for the conclusion formulas.
        
        Args:
            isomorphic_model: An isomorphic model to strengthen against
            
        Returns:
            Z3 constraint for stronger model
        """
        # For now, return a simple constraint
        # Full implementation would compare conclusion truth values
        return z3.BoolVal(True)
    
    def iterate_generator(self):
        """Override to add theory-specific differences to logos theory models.
        
        This method extends the base iterator's generator to merge logos-specific
        differences (verification, falsification, parthood) with the generic 
        differences calculated by the base iterator.
        
        Yields:
            Model structures with both generic and theory-specific differences
        """
        for model in super().iterate_generator():
            # Calculate theory-specific differences if we have a previous model
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_logos_differences(
                    model, self.model_structures[-2]
                )
                
                # Transform logos structure to match display expectations
                if theory_diffs.get('verify') or theory_diffs.get('falsify'):
                    atomic_changes = {}
                    
                    # Transform verify structure
                    if theory_diffs.get('verify'):
                        atomic_changes['verify'] = {}
                        for letter_str, state_changes in theory_diffs['verify'].items():
                            # Extract clean letter name (A, B, C) from "Proposition_A" or "A" formats
                            letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                            # Handle case where letter_str might be "Proposition A" with space
                            letter_name = letter_name.replace('Proposition ', '')
                            atomic_changes['verify'][letter_name] = state_changes
                    
                    # Transform falsify structure
                    if theory_diffs.get('falsify'):
                        atomic_changes['falsify'] = {}
                        for letter_str, state_changes in theory_diffs['falsify'].items():
                            # Extract clean letter name (A, B, C) from "Proposition_A" or "A" formats
                            letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                            # Handle case where letter_str might be "Proposition A" with space
                            letter_name = letter_name.replace('Proposition ', '')
                            atomic_changes['falsify'][letter_name] = state_changes
                    
                    theory_diffs['atomic_changes'] = atomic_changes
                
                # Merge theory-specific differences with existing generic ones
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs
            
            yield model


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


def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example that yields models incrementally.
    
    This function provides a generator interface for finding multiple models,
    yielding each model as it's discovered rather than returning them all at once.
    
    Args:
        example: A BuildExample instance with logos theory.
        max_iterations: Maximum number of models to find.
        
    Yields:
        ModelStructure: Each distinct model as it's found.
    """
    if max_iterations is not None:
        # Update the iterate setting
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator
    iterator = LogosModelIterator(example)
    
    # Store the iterator on the example for access to debug messages
    example._iterator = iterator
    
    # Use the generator interface
    yield from iterator.iterate_generator()


# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator