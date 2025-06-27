#!/usr/bin/env python3
"""
Trace constraint generation to see when true_at is called.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

# Monkey patch true_at to trace calls
original_true_at = ExclusionSemantics.true_at
call_count = 0

def traced_true_at(self, sentence, eval_point):
    global call_count
    call_count += 1
    print(f"\n[TRACE {call_count}] true_at called:")
    print(f"  Sentence: {sentence}")
    print(f"  Is atomic: {sentence.sentence_letter is not None}")
    if sentence.sentence_letter is not None:
        print(f"  Atomic letter: {sentence.sentence_letter}")
        print(f"  Cache before: {list(self.atom_skolem_cache.keys())}")
    
    result = original_true_at(self, sentence, eval_point)
    
    if sentence.sentence_letter is not None:
        print(f"  Cache after: {list(self.atom_skolem_cache.keys())}")
    
    return result

def trace_generation():
    """Trace constraint generation."""
    print("TRACING CONSTRAINT GENERATION")
    print("="*60)
    
    # Patch true_at
    ExclusionSemantics.true_at = traced_true_at
    
    try:
        premises, conclusions, settings = TN_ENTAIL_example
        
        # Create semantics
        semantics = ExclusionSemantics(settings)
        
        # SK2 operators
        sk2_operators = create_operator_collection("SK2")
        
        # Create syntax
        syntax = Syntax(premises, conclusions, sk2_operators)
        
        print("\nCreating constraints...")
        print("-"*40)
        
        # Create constraints - this should call true_at
        constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
        
        print(f"\n\nTotal true_at calls during constraint generation: {call_count}")
        print(f"Final cache state: {list(semantics.atom_skolem_cache.keys())}")
        print(f"Final counter: {semantics.atom_skolem_counter}")
        
    finally:
        # Restore original
        ExclusionSemantics.true_at = original_true_at

if __name__ == "__main__":
    trace_generation()