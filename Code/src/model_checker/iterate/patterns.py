"""Utilities for extracting and comparing structural patterns from Z3 models."""

import z3
from typing import Dict, Any, List, Optional


class StructuralPattern:
    """Represents a structural pattern extracted from a Z3 model."""
    
    def __init__(self, model_constraints, z3_model):
        """Extract pattern from a Z3 model using model constraints."""
        self.pattern = self._extract_pattern(model_constraints, z3_model)
    
    def _extract_pattern(self, model_constraints, z3_model):
        """Extract structural information from Z3 model."""
        semantics = model_constraints.semantics
        pattern = {}
        
        # Count worlds and possible states
        all_states = list(range(2**semantics.N))
        pattern['num_worlds'] = sum(
            1 for state in all_states
            if z3.is_true(z3_model.eval(semantics.is_world(state), model_completion=True))
        )
        pattern['num_possible'] = sum(
            1 for state in all_states
            if z3.is_true(z3_model.eval(semantics.possible(state), model_completion=True))
        )
        
        # Record which states are worlds
        pattern['world_states'] = [
            state for state in all_states
            if z3.is_true(z3_model.eval(semantics.is_world(state), model_completion=True))
        ]
        
        # Record verify/falsify patterns for each letter
        pattern['verify'] = {}
        pattern['falsify'] = {}
        
        for letter in model_constraints.sentence_letters:
            letter_str = str(letter)
            pattern['verify'][letter_str] = [
                state for state in all_states
                if z3.is_true(z3_model.eval(semantics.verify(state, letter), model_completion=True))
            ]
            pattern['falsify'][letter_str] = [
                state for state in all_states
                if z3.is_true(z3_model.eval(semantics.falsify(state, letter), model_completion=True))
            ]
        
        return pattern
    
    def to_difference_constraint(self, semantics, sentence_letters):
        """Create Z3 constraint that excludes this exact pattern."""
        constraints = []
        all_states = list(range(2**semantics.N))
        
        # At least one world must be different
        world_differences = []
        for state in all_states:
            if state in self.pattern['world_states']:
                # This state is a world in our pattern, so require it not to be
                world_differences.append(z3.Not(semantics.is_world(state)))
            else:
                # This state is not a world in our pattern, so require it to be
                world_differences.append(semantics.is_world(state))
        
        # Or at least one verify/falsify must be different
        verify_differences = []
        for letter in sentence_letters:
            letter_str = str(letter)
            for state in all_states:
                if state in self.pattern['verify'].get(letter_str, []):
                    verify_differences.append(z3.Not(semantics.verify(state, letter)))
                if state in self.pattern['falsify'].get(letter_str, []):
                    verify_differences.append(z3.Not(semantics.falsify(state, letter)))
        
        # Require at least one difference
        return z3.Or(world_differences + verify_differences)


def create_structural_difference_constraint(model_constraints, previous_patterns):
    """Create constraint requiring difference from all previous patterns."""
    if not previous_patterns:
        return z3.BoolVal(True)
    
    # Must be different from ALL previous patterns
    difference_constraints = []
    for pattern in previous_patterns:
        diff_constraint = pattern.to_difference_constraint(
            model_constraints.semantics,
            model_constraints.sentence_letters
        )
        difference_constraints.append(diff_constraint)
    
    return z3.And(*difference_constraints)