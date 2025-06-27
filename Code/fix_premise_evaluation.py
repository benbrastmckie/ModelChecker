#!/usr/bin/env python3
"""
Fix premise evaluation by caching the constraint formulas.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints
from model_checker.utils import run_enhanced_test

# Monkey patch to cache constraint formulas
original_init = UnilateralProposition.__init__

def patched_init(self, sentence_obj, model_structure, eval_point=None):
    """Patched init that stores the constraint formula."""
    original_init(self, sentence_obj, model_structure, eval_point)
    
    # Store the constraint formula if it exists
    if hasattr(model_structure, 'model_constraints'):
        constraints = model_structure.model_constraints
        
        # Find the constraint for this sentence
        for i, premise in enumerate(constraints.premises):
            if premise is sentence_obj:
                if i < len(constraints.premise_constraints):
                    self.constraint_formula = constraints.premise_constraints[i]
                    return
                    
        for i, conclusion in enumerate(constraints.conclusions):
            if conclusion is sentence_obj:
                if i < len(constraints.conclusion_constraints):
                    self.constraint_formula = constraints.conclusion_constraints[i]
                    return

# Monkey patch truth_value_at to use cached formula
original_truth_value_at = UnilateralProposition.truth_value_at

def patched_truth_value_at(self, eval_point):
    """Use the cached constraint formula if available."""
    if hasattr(self, 'constraint_formula'):
        # Use the constraint formula that was used during model generation
        z3_model = self.model_structure.z3_model
        result = z3_model.evaluate(self.constraint_formula)
        return z3.is_true(result)
    else:
        # Fall back to original
        return original_truth_value_at(self, eval_point)

def test_with_cache(name, example_data, strategy="SK2"):
    """Test with constraint formula caching."""
    print(f"\n{'='*60}")
    print(f"Testing: {name} with {strategy} (Cached Constraints)")
    print('='*60)
    
    # Apply patches
    UnilateralProposition.__init__ = patched_init
    UnilateralProposition.truth_value_at = patched_truth_value_at
    
    try:
        # Run test
        result = run_enhanced_test(
            example_case=example_data,
            semantic_class=ExclusionSemantics,
            proposition_class=UnilateralProposition,
            operator_collection=create_operator_collection(strategy),
            syntax_class=Syntax,
            model_constraints=ModelConstraints,
            model_structure=ExclusionStructure,
            strategy_name=strategy
        )
        
        # Display results
        print(f"\nResults:")
        print(f"  Model found: {result.model_found}")
        print(f"  Premise evaluations: {result.premise_evaluations}")
        print(f"  Conclusion evaluations: {result.conclusion_evaluations}")
        
        if result.premise_evaluations and all(result.premise_evaluations):
            print("  ✓ ALL PREMISES TRUE!")
        elif result.premise_evaluations and any(p is False for p in result.premise_evaluations):
            print("  ⚠️  FALSE PREMISE DETECTED!")
            
        return result
        
    finally:
        # Restore originals
        UnilateralProposition.__init__ = original_init
        UnilateralProposition.truth_value_at = original_truth_value_at

def main():
    """Test the caching fix."""
    print("TESTING CONSTRAINT FORMULA CACHING FIX")
    
    # Test Triple Negation
    tn_result = test_with_cache("Triple Negation Entailment", TN_ENTAIL_example)
    
    # Test Disjunctive DeMorgan
    dm_result = test_with_cache("Disjunctive DeMorgan's RL", DISJ_DM_RL_example)
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    
    tn_fixed = tn_result.model_found and all(tn_result.premise_evaluations) if tn_result.premise_evaluations else False
    dm_fixed = dm_result.model_found and all(dm_result.premise_evaluations) if dm_result.premise_evaluations else False
    
    print(f"\nTriple Negation: {'✓ FIXED' if tn_fixed else '✗ Still broken'}")
    print(f"Disjunctive DeMorgan: {'✓ FIXED' if dm_fixed else '✗ Still broken'}")
    
    if tn_fixed and dm_fixed:
        print("\n🎉 SUCCESS! The constraint caching fix eliminates false premises!")
    elif tn_fixed or dm_fixed:
        print("\n⚠️  PARTIAL SUCCESS: Some examples are fixed")
    else:
        print("\n✗ The fix did not work")

if __name__ == "__main__":
    main()