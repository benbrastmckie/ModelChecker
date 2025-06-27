#!/usr/bin/env python3
"""
Simple direct test of SK2 to understand the false premise issue.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.builder import BuildExample

def test_sk2():
    """Test SK2 directly using BuildExample."""
    print("DIRECT SK2 TEST")
    print("="*60)
    
    # Get the triple negation example
    premises, conclusions, settings = TN_ENTAIL_example
    
    print(f"Testing: {premises} ⊢ {conclusions}")
    print(f"Settings: N={settings['N']}")
    
    # Test with SK2
    print("\n1. Testing with SK2 Strategy:")
    print("-"*40)
    
    from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
    from model_checker.theory_lib.exclusion.operators import create_operator_collection
    from model_checker import Syntax
    
    sk2_operators = create_operator_collection("SK2")
    
    example = BuildExample(
        premises=premises,
        conclusions=conclusions,
        settings=settings,
        semantic_class=ExclusionSemantics,
        proposition_class=UnilateralProposition,
        model_structure=ExclusionStructure,
        operator_collection=sk2_operators,
        syntax_class=Syntax,
        verbose=True
    )
    
    result = example.check_debugger()
    
    print(f"\nModel found: {result['z3_model'] is not None}")
    print(f"Z3 status: {result['z3_model_status']}")
    
    if result['z3_model']:
        # Evaluate premises
        model = result['model_structure']
        semantics = result['semantics']
        
        print("\nEvaluating premise at main world:")
        if result['syntax'].premises[0].proposition:
            eval_point = {"world": semantics.main_world}
            premise_val = result['syntax'].premises[0].proposition.truth_value_at(eval_point)
            print(f"  Premise value: {premise_val}")
            
            if not premise_val:
                print("\n⚠️  FALSE PREMISE DETECTED!")
                print("\nInvestigating why premise is false...")
                
                # Get the formula structure
                premise_prop = result['syntax'].premises[0].proposition
                print(f"  Premise type: {type(premise_prop).__name__}")
                print(f"  Premise operator: {premise_prop.sentence_letter.operator if hasattr(premise_prop.sentence_letter, 'operator') else 'N/A'}")
    
    # Compare with MS
    print("\n2. Testing with MS Strategy (for comparison):")
    print("-"*40)
    
    ms_operators = create_operator_collection("MS")
    
    ms_example = BuildExample(
        premises=premises,
        conclusions=conclusions,
        settings=settings,
        semantic_class=ExclusionSemantics,
        proposition_class=UnilateralProposition,
        model_structure=ExclusionStructure,
        operator_collection=ms_operators,
        syntax_class=Syntax,
        verbose=False
    )
    
    ms_result = ms_example.check_debugger()
    
    if ms_result['z3_model'] and ms_result['syntax'].premises[0].proposition:
        eval_point = {"world": ms_result['semantics'].main_world}
        ms_premise_val = ms_result['syntax'].premises[0].proposition.truth_value_at(eval_point)
        print(f"  MS premise value: {ms_premise_val}")
    
    print("\n" + "="*60)
    print("ANALYSIS")
    print("="*60)
    
    print("\nThe issue appears to be that even with Skolemization,")
    print("the evaluation still depends on finding witnesses.")
    print("\nPossible root causes:")
    print("1. The truth_value_at method still tries to find witnesses")
    print("2. The Skolem functions aren't being used during evaluation")
    print("3. The constraint generation and evaluation are disconnected")

if __name__ == "__main__":
    test_sk2()