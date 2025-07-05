"""
Truth Cache for Incremental Exclusion Theory

This module provides the TruthCache class that maintains partial truth evaluations
during incremental solving. It tracks formula dependencies, caches verifier sets,
and supports incremental updates as witness information becomes available.

Phase 2 implementation with full dependency tracking and incremental evaluation.
"""

import z3
from typing import Dict, Set, List, Optional, Any, Tuple
import time


class TruthCache:
    """
    Maintains partial truth evaluations during incremental solving.
    
    This cache tracks:
    - Formula verifiers computed incrementally
    - Truth values as they become available
    - Dependencies between formulas
    - Invalidation based on witness updates
    """
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.verifier_cache = {}       # sentence -> set of verifying states
        self.truth_cache = {}          # (sentence, eval_point) -> truth value
        self.dependency_graph = {}     # sentence -> set of dependent sentences
        self.evaluation_order = []     # track order for debugging
        self.cache_hits = 0
        self.cache_misses = 0
        self.invalidation_count = 0
        
    def get_verifiers(self, sentence, witness_store):
        """
        Get verifiers for a sentence, computing incrementally if needed.
        
        This is the main entry point for operator implementations to get
        verifier sets during incremental evaluation.
        """
        # Check cache first
        if sentence in self.verifier_cache:
            self.cache_hits += 1
            return self.verifier_cache[sentence]
        
        self.cache_misses += 1
        
        # Compute verifiers
        verifiers = self.compute_verifiers(sentence, witness_store)
        
        # Cache result
        self.verifier_cache[sentence] = verifiers
        self.evaluation_order.append((time.time(), sentence, len(verifiers)))
        
        return verifiers
    
    def compute_verifiers(self, sentence, witness_store):
        """
        Compute verifiers for a sentence using current witness information.
        
        This method delegates to the appropriate computation based on
        sentence type (atomic vs complex).
        """
        if sentence.sentence_letter is not None:
            # Atomic sentence - compute from proposition
            return self.compute_atomic_verifiers(sentence)
        else:
            # Complex sentence - delegate to operator
            if hasattr(sentence.operator, 'compute_verifiers'):
                return sentence.operator.compute_verifiers(
                    *sentence.arguments, witness_store, self
                )
            else:
                # Fallback for operators without incremental support
                return set()
    
    def compute_atomic_verifiers(self, sentence):
        """
        Compute verifiers for atomic sentences.
        
        For atomic propositions, we need to find which states verify
        the proposition based on the semantic model.
        """
        verifiers = set()
        
        # Get the proposition object
        if hasattr(sentence, 'proposition') and sentence.proposition is not None:
            # Use the proposition's find_proposition method
            prop_verifiers = sentence.proposition.find_proposition()
            if prop_verifiers is not None:
                verifiers = set(prop_verifiers)
        else:
            # Fallback: check all states
            for state in self.semantics.all_states:
                # Create a temporary evaluation point
                temp_eval = {'world': state}
                if self.evaluate_atomic_at_state(sentence, temp_eval):
                    verifiers.add(state)
        
        return verifiers
    
    def evaluate_atomic_at_state(self, sentence, eval_point):
        """
        Evaluate an atomic sentence at a specific state.
        
        This uses the semantic model to determine if the state
        verifies the atomic proposition.
        """
        try:
            # Use semantics.true_at for atomic evaluation
            constraint = self.semantics.true_at(sentence, eval_point)
            
            # If we have a Z3 model, evaluate the constraint
            if hasattr(self.semantics, 'z3_model') and self.semantics.z3_model is not None:
                return z3.is_true(self.semantics.z3_model.evaluate(constraint))
            else:
                # Without a model, we can't evaluate
                return False
        except:
            return False
    
    def get_truth_value(self, sentence, eval_point, witness_store):
        """
        Get the truth value of a sentence at an evaluation point.
        
        Uses cached values when available, otherwise computes incrementally.
        """
        cache_key = (id(sentence), id(eval_point))
        
        # Check cache
        if cache_key in self.truth_cache:
            self.cache_hits += 1
            return self.truth_cache[cache_key]
        
        self.cache_misses += 1
        
        # Compute truth value
        truth_value = self.evaluate_incrementally(sentence, eval_point, witness_store)
        
        # Cache result
        self.truth_cache[cache_key] = truth_value
        
        return truth_value
    
    def evaluate_incrementally(self, sentence, eval_point, witness_store):
        """
        Evaluate truth incrementally using current witness information.
        
        This method checks if we have sufficient witnesses and then
        delegates to the appropriate evaluation method.
        """
        # Check if we have sufficient witnesses
        if not self.has_sufficient_witnesses(sentence, witness_store):
            # Return None to indicate incomplete evaluation
            return None
        
        if sentence.sentence_letter is not None:
            # Atomic sentence
            verifiers = self.get_verifiers(sentence, witness_store)
            eval_world = eval_point['world']
            
            # Check if eval_world is in verifiers
            for v in verifiers:
                if self.semantics.is_part_of(v, eval_world):
                    return True
            return False
        else:
            # Complex sentence - delegate to operator
            if hasattr(sentence.operator, 'evaluate_with_witnesses'):
                return sentence.operator.evaluate_with_witnesses(
                    *sentence.arguments, eval_point, witness_store, self
                )
            else:
                # Fallback to standard evaluation
                return None
    
    def has_sufficient_witnesses(self, sentence, witness_store):
        """
        Check if we have sufficient witness information for evaluation.
        
        Recursively checks the sentence tree to ensure all required
        witnesses are available.
        """
        if sentence.sentence_letter is not None:
            # Atomic sentences don't need witnesses
            return True
        elif hasattr(sentence.operator, 'has_sufficient_witnesses'):
            # Delegate to operator
            return sentence.operator.has_sufficient_witnesses(
                *sentence.arguments, witness_store
            )
        else:
            # Conservative default
            return False
    
    def register_dependency(self, parent_sentence, child_sentence):
        """
        Register that parent_sentence depends on child_sentence.
        
        This is used to track invalidation dependencies.
        """
        if parent_sentence not in self.dependency_graph:
            self.dependency_graph[parent_sentence] = set()
        self.dependency_graph[parent_sentence].add(child_sentence)
    
    def invalidate_dependent_truths(self, sentence):
        """
        Invalidate cached values when dependencies change.
        
        This recursively invalidates all sentences that depend on
        the given sentence.
        """
        # Remove from verifier cache
        if sentence in self.verifier_cache:
            del self.verifier_cache[sentence]
            self.invalidation_count += 1
        
        # Remove from truth cache
        keys_to_remove = [key for key in self.truth_cache if key[0] == id(sentence)]
        for key in keys_to_remove:
            del self.truth_cache[key]
        
        # Recursively invalidate dependents
        if sentence in self.dependency_graph:
            for dependent in self.dependency_graph[sentence]:
                self.invalidate_dependent_truths(dependent)
    
    def invalidate_all(self):
        """
        Clear all cached values.
        
        Used when witness information changes significantly.
        """
        self.verifier_cache.clear()
        self.truth_cache.clear()
        self.evaluation_order.clear()
        self.invalidation_count += 1
    
    def get_statistics(self) -> Dict[str, Any]:
        """
        Get cache performance statistics.
        """
        total_requests = self.cache_hits + self.cache_misses
        hit_rate = self.cache_hits / total_requests if total_requests > 0 else 0
        
        return {
            'cache_hits': self.cache_hits,
            'cache_misses': self.cache_misses,
            'hit_rate': hit_rate,
            'verifier_cache_size': len(self.verifier_cache),
            'truth_cache_size': len(self.truth_cache),
            'invalidation_count': self.invalidation_count,
            'evaluation_order_length': len(self.evaluation_order)
        }
    
    def get_evaluation_trace(self, limit: int = 10) -> List[Tuple]:
        """
        Get recent evaluation history for debugging.
        """
        return self.evaluation_order[-limit:] if self.evaluation_order else []