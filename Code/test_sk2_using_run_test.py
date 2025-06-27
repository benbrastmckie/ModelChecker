#!/usr/bin/env python3
"""
Test SK2 using the run_test utility function.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints
from model_checker.utils import run_test

def test_with_analysis(name, example_data, strategy):
    """Test an example and analyze the result."""
    print(f"\n{'='*60}")
    print(f"Testing: {name} with {strategy}")
    print('='*60)
    
    # Get components
    operator_collection = create_operator_collection(strategy)
    
    # Run test
    result = run_test(
        example_case=example_data,
        semantic_class=ExclusionSemantics,
        proposition_class=UnilateralProposition,
        operator_collection=operator_collection,
        syntax_class=Syntax,
        model_constraints=ModelConstraints,
        model_structure=ExclusionStructure
    )
    
    print(f"Result: {result}")
    
    # For more detailed analysis, we need to run the test manually
    premises, conclusions, settings = example_data
    syntax = Syntax(premises, conclusions, operator_collection)
    semantics = ExclusionSemantics(settings)
    
    # Create model constraints
    constraints = ModelConstraints(
        settings,
        syntax,
        semantics,
        UnilateralProposition,
    )
    
    # Create model structure
    structure = ExclusionStructure(
        constraints, 
        settings,
    )
    
    if structure.z3_model:
        print("\nModel found - checking premise evaluation:")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        # Evaluate
        eval_point = {"world": semantics.main_world}
        
        for i, premise in enumerate(syntax.premises):
            if premise.proposition:
                val = premise.proposition.truth_value_at(eval_point)
                print(f"  Premise {i}: {val}")
                if not val:
                    print("    ⚠️  FALSE PREMISE!")
                    
                    # Debug the evaluation
                    print(f"    Main world: {semantics.main_world}")
                    print(f"    Checking exclusion evaluation...")
                    
                    # The issue might be in how truth_value_at works
                    # Let's check if it's using the constraints or trying to find witnesses
        
        for i, conclusion in enumerate(syntax.conclusions):
            if conclusion.proposition:
                val = conclusion.proposition.truth_value_at(eval_point)
                print(f"  Conclusion {i}: {val}")
    
    return result

def main():
    """Test SK2 on problematic examples."""
    print("SK2 ANALYSIS WITH RUN_TEST")
    print("Testing Triple Skolemization implementation")
    
    # Test Triple Negation
    tn_sk2 = test_with_analysis("Triple Negation Entailment", TN_ENTAIL_example, "SK2")
    tn_ms = test_with_analysis("Triple Negation Entailment", TN_ENTAIL_example, "MS")
    
    # Test Disjunctive DeMorgan
    dm_sk2 = test_with_analysis("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "SK2")
    dm_ms = test_with_analysis("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "MS")
    
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Triple Negation - MS: {tn_ms}, SK2: {tn_sk2}")
    print(f"Disjunctive DeMorgan - MS: {dm_ms}, SK2: {dm_sk2}")
    
    print("\nThe key insight: Even with Skolemization in constraint generation,")
    print("the truth_value_at method still tries to find witnesses dynamically.")
    print("This is the disconnect between constraint solving and evaluation.")

if __name__ == "__main__":
    main()