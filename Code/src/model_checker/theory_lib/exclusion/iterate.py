"""Exclusion theory specific model iteration implementation."""

import z3
import logging
from model_checker.theory_lib.logos.iterate import LogosModelIterator
from model_checker.utils import bitvec_to_substates

logger = logging.getLogger(__name__)


class ExclusionModelIterator(LogosModelIterator):
    """Model iterator for exclusion theory with witness-aware semantics.
    
    This class extends LogosModelIterator to add exclusion-specific
    handling of witness structures and exclusion relations.
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences including witness-specific changes."""
        # Don't call parent - we'll do our own difference calculation
        differences = {
            "verifications": {},
            "witnesses": {},
            "exclusions": {}
        }
        
        # Calculate verification differences
        differences["verifications"] = self._calculate_verification_differences(
            new_structure, previous_structure
        )
        
        # Add witness-specific differences
        differences["witnesses"] = self._calculate_witness_differences(
            new_structure, previous_structure
        )
        
        # Add exclusion relation differences
        differences["exclusions"] = self._calculate_exclusion_differences(
            new_structure, previous_structure
        )
        
        return differences
    
    def _calculate_verification_differences(self, new_structure, previous_structure):
        """Calculate differences in verification between models."""
        verification_diffs = {}
        
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        semantics = new_structure.semantics
        
        # Check each state/letter combination
        for state in new_structure.all_states:
            for letter in new_structure.sentence_letters:
                if hasattr(letter, 'sentence_letter') and letter.sentence_letter is not None:
                    atom = letter.sentence_letter
                else:
                    continue
                
                try:
                    old_verify = previous_model.eval(semantics.verify(state, atom), model_completion=True)
                    new_verify = new_model.eval(semantics.verify(state, atom), model_completion=True)
                    
                    if bool(old_verify) != bool(new_verify):
                        state_str = bitvec_to_substates(state, new_structure.N)
                        atom_str = letter.proposition if hasattr(letter, 'proposition') else str(atom)
                        key = f"{state_str} verifies {atom_str}"
                        
                        verification_diffs[key] = {
                            "old": bool(old_verify),
                            "new": bool(new_verify)
                        }
                except z3.Z3Exception:
                    pass
        
        return verification_diffs
    
    def _calculate_witness_differences(self, new_structure, previous_structure):
        """Calculate differences in witness assignments between models.
        
        For exclusion theory, witness predicates are registered in the witness registry
        and accessed through the model's witness_predicates attribute.
        """
        witness_diffs = {
            "changed_witnesses": {},
            "witness_counts": {
                "old": 0,
                "new": 0
            }
        }
        
        # Access witness predicates from both models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Check if both models have witness predicates
        new_witnesses = getattr(new_model, 'witness_predicates', {}) if hasattr(new_model, 'witness_predicates') else {}
        old_witnesses = getattr(previous_model, 'witness_predicates', {}) if hasattr(previous_model, 'witness_predicates') else {}
        
        # If no witness predicates available, check the semantics registry
        if not new_witnesses and not old_witnesses and hasattr(new_structure, 'semantics'):
            semantics = new_structure.semantics
            if hasattr(semantics, 'witness_registry'):
                # Get all registered witness predicates
                all_predicates = semantics.witness_registry.get_all_predicates()
                
                # Check differences in witness function mappings
                for pred_name, pred_func in all_predicates.items():
                    if pred_name.endswith('_h') or pred_name.endswith('_y'):
                        base_name = pred_name[:-2]  # Remove _h or _y suffix
                        func_type = pred_name[-1]   # h or y
                        
                        if base_name not in witness_diffs["changed_witnesses"]:
                            witness_diffs["changed_witnesses"][base_name] = {
                                "h_changes": {},
                                "y_changes": {}
                            }
                        
                        # Compare function mappings for all states
                        for state in new_structure.all_states:
                            try:
                                # Evaluate witness function in both models
                                state_bv = int(state)
                                
                                old_result = previous_model.eval(pred_func(state_bv), model_completion=True)
                                new_result = new_model.eval(pred_func(state_bv), model_completion=True)
                                
                                if old_result != new_result:
                                    state_str = bitvec_to_substates(state_bv, new_structure.N)
                                    witness_diffs["changed_witnesses"][base_name][f"{func_type}_changes"][state_str] = {
                                        "old": int(old_result.as_long()) if hasattr(old_result, 'as_long') else str(old_result),
                                        "new": int(new_result.as_long()) if hasattr(new_result, 'as_long') else str(new_result)
                                    }
                                    
                            except Exception:
                                # Skip if evaluation fails
                                pass
        
        # Count total witness predicates
        witness_diffs["witness_counts"]["old"] = len(old_witnesses)
        witness_diffs["witness_counts"]["new"] = len(new_witnesses)
        
        return witness_diffs
    
    def _calculate_exclusion_differences(self, new_structure, previous_structure):
        """Calculate differences in exclusion relations."""
        exclusion_diffs = {}
        
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        semantics = new_structure.semantics
        
        # Check exclusion changes between states
        for s1 in new_structure.all_states:
            for s2 in new_structure.all_states:
                if s1 == s2:
                    continue
                
                try:
                    # Check if exclusion relation changed
                    old_excludes = previous_model.eval(
                        semantics.excludes(s1, s2), 
                        model_completion=True
                    )
                    new_excludes = new_model.eval(
                        semantics.excludes(s1, s2), 
                        model_completion=True
                    )
                    
                    if bool(old_excludes) != bool(new_excludes):
                        s1_str = bitvec_to_substates(s1, new_structure.N)
                        s2_str = bitvec_to_substates(s2, new_structure.N)
                        key = f"{s1_str} excludes {s2_str}"
                        
                        exclusion_diffs[key] = {
                            "old": bool(old_excludes),
                            "new": bool(new_excludes)
                        }
                        
                except z3.Z3Exception:
                    pass
        
        return exclusion_diffs
    
    
    
    def _create_witness_constraints(self, previous_models):
        """Create constraints to ensure witness diversity.
        
        For exclusion theory, we focus on witness predicates that are
        registered in the witness registry, not generic witness functions.
        """
        # For now, return empty list since witness predicates are handled
        # differently in exclusion theory through the witness registry
        return []
    
    def _create_letter_value_constraints(self, prev_model, semantics):
        """Create constraints on verify values differing (no falsify in exclusion)."""
        constraints = []
        
        # Get sentence letters from syntax
        syntax = self.build_example.example_syntax
        if not hasattr(syntax, 'sentence_letters'):
            return constraints
        
        for letter_obj in syntax.sentence_letters:
            if hasattr(letter_obj, 'sentence_letter'):
                atom = letter_obj.sentence_letter
                
                # Check each state - only verify, no falsify
                for state in range(2**semantics.N):
                    # Get previous values
                    prev_verify = prev_model.eval(
                        semantics.verify(state, atom), 
                        model_completion=True
                    )
                    
                    # Create constraints for differences
                    constraints.append(
                        semantics.verify(state, atom) != prev_verify
                    )
        
        return constraints

    def iterate_generator(self):
        """Override to add theory-specific differences to exclusion theory models.
        
        This method extends the base iterator's generator to merge exclusion-specific
        differences (verification changes, witness changes, exclusion relations) with
        the generic differences calculated by the base iterator.
        
        Yields:
            Model structures with both generic and theory-specific differences
        """
        for model in super().iterate_generator():
            # Calculate theory-specific differences if we have a previous model
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_differences(
                    model, self.model_structures[-2]
                )
                # Merge theory-specific differences with existing generic ones
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs
            
            yield model


def iterate_example(example, max_iterations=None):
    """Iterate an exclusion theory example to find multiple models."""
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator and run
    iterator = ExclusionModelIterator(example)
    models = iterator.iterate()
    
    # Store iterator for debug message access
    example._iterator = iterator
    
    return models


def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example that yields models incrementally.
    
    This function provides a generator interface for finding multiple models,
    yielding each model as it's discovered rather than returning them all at once.
    This enables proper progress tracking and iteration reports.
    
    Args:
        example: A BuildExample instance with exclusion theory.
        max_iterations: Maximum number of models to find.
        
    Yields:
        Model structures as they are discovered.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator - use ExclusionModelIterator for theory-specific logic
    iterator = ExclusionModelIterator(example)
    
    # Store the iterator on the example for access to debug messages
    example._iterator = iterator
    
    # Use the generator interface
    yield from iterator.iterate_generator()

# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator