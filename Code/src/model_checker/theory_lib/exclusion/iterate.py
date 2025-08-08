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
        
        # For now, return empty witness differences since witness predicates
        # in exclusion theory are handled through the witness registry system
        # and not directly accessible via semantics.witness()
        
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