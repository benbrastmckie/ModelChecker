"""
SK-Enhanced Exclusion Semantics

This module provides an exclusion semantics class that properly implements
recursive reduction to verifier existence conditions, following the modular
design principle.
"""

import z3
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics
from model_checker.utils import Exists


class SKExclusionSemantics(ExclusionSemantics):
    """
    Exclusion semantics with correct recursive reduction.
    
    This class overrides the base true_at method to ensure proper
    recursive semantics while maintaining modularity.
    """
    
    def true_at(self, sentence, eval_point):
        """
        Evaluate truth at a point with correct recursive reduction.
        
        Following the modular design principle, this method only distinguishes
        between atomic sentences and complex sentences, delegating to operators
        for complex cases.
        """
        if sentence.sentence_letter is not None:
            # Atomic case: reduce to verifier existence
            # exists v. verify(v, A) AND v part_of eval_world
            v = z3.BitVec(f"v_atom_{id(sentence)}", self.N)
            return Exists([v], z3.And(
                self.verify(v, sentence.sentence_letter),
                self.is_part_of(v, eval_point["world"])
            ))
        else:
            # Complex case: delegate to operator's true_at method
            # This maintains modularity - we don't check operator types
            return sentence.operator.true_at(*sentence.arguments, eval_point)
    
    def extended_verify(self, state, sentence, eval_point):
        """
        Extended verification with proper modularity.
        
        This method delegates to operator-specific extended_verify methods
        for complex sentences.
        """
        if sentence.sentence_letter is not None:
            # Atomic case
            return self.verify(state, sentence.sentence_letter)
        else:
            # Complex case: delegate to operator's extended_verify
            return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
    
    def _reset_global_state(self):
        """Reset any global state to ensure clean execution."""
        super()._reset_global_state()
        # Reset any SK-specific caches if needed
        if hasattr(self, '_sk_function_cache'):
            self._sk_function_cache = {}