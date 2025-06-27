#!/usr/bin/env python3
"""
Test the SK2 (True Skolemization) strategy on problematic examples.
"""

import sys
sys.path.insert(0, 'src')

import json
import time
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection

# Test examples that have false premise issues
test_examples = {
    "Triple Negation Entailment": {
        "premises": ['\\exclude \\exclude \\exclude A'],
        "conclusions": ['\\exclude A'],
        "expected_issue": "false premise with other strategies"
    },
    "Disjunctive DeMorgan's RL": {
        "premises": ['(\\exclude A \\uniwedge \\exclude B)'],
        "conclusions": ['\\exclude (A \\univee B)'],
        "expected_issue": "false premise with other strategies"
    },
    "Simple Exclusion": {
        "premises": ['\\exclude A'],
        "conclusions": ['A'],
        "expected_issue": "should work fine"
    },
    "Double Negation Elimination": {
        "premises": ['\\exclude \\exclude A'],
        "conclusions": ['A'],
        "expected_issue": "should find countermodel"
    },
}

def test_strategy(strategy_name, examples):
    """Test a strategy on the given examples."""
    print(f"\n{'='*70}")
    print(f"TESTING STRATEGY: {strategy_name}")
    print(f"{'='*70}\n")
    
    # Create operator collection with the specified strategy
    operators = create_operator_collection(strategy_name)
    
    results = {}
    
    for example_name, example_data in examples.items():
        print(f"\nTesting: {example_name}")
        print(f"  Premises: {example_data['premises']}")
        print(f"  Conclusions: {example_data['conclusions']}")
        
        try:
            # Settings
            settings = {
                'N': 3,
                'possible': False,
                'contingent': False,
                'non_empty': False,
                'non_null': False,
                'disjoint': False,
                'fusion_closure': False,
                'max_time': 10,
                'expectation': False,
            }
            
            # Create components
            syntax = Syntax(example_data['premises'], example_data['conclusions'], operators)
            semantics = ExclusionSemantics(settings)
            
            # Create model constraints
            model_constraints = ModelConstraints(
                settings,
                syntax,
                semantics,
                UnilateralProposition
            )
            
            # Time the solving
            start_time = time.time()
            
            # Create model structure - this will solve and build the model
            model_structure = ExclusionStructure(model_constraints, settings)
            
            solve_time = time.time() - start_time
            
            # Check if we found a countermodel
            if not model_structure.z3_model_status:
                print(f"  Result: NO COUNTERMODEL (Theorem)")
                results[example_name] = {
                    "countermodel_found": False,
                    "solve_time": solve_time,
                    "false_premise": False
                }
                continue
                
            print(f"  Result: COUNTERMODEL FOUND (time: {solve_time:.3f}s)")
            
            # Check for false premises
            z3_model = model_structure.z3_model
            main_point = model_structure.main_point
            false_premise_found = False
            
            # Test each premise
            for i, premise_sent in enumerate(model_structure.premises):
                # Get the proposition
                premise_sent.update_proposition(model_structure)
                premise_prop = premise_sent.proposition
                
                if premise_prop:
                    truth_val = premise_prop.truth_value_at(main_point)
                    if not truth_val:
                        print(f"  WARNING: False premise detected for premise {i}")
                        false_premise_found = True
                
            if not false_premise_found:
                print(f"  SUCCESS: All premises evaluate to true!")
            
            # Count h functions in model
            h_functions = []
            for decl in z3_model.decls():
                if 'h_sk2_' in str(decl) or 'y_sk2_' in str(decl):
                    h_functions.append(str(decl))
            
            print(f"  Skolem functions found: {len(h_functions)}")
            if len(h_functions) > 0:
                print(f"    Functions: {', '.join(h_functions[:5])}{'...' if len(h_functions) > 5 else ''}")
            
            results[example_name] = {
                "countermodel_found": True,
                "solve_time": solve_time,
                "false_premise": false_premise_found,
                "skolem_functions": len(h_functions)
            }
            
        except Exception as e:
            print(f"  ERROR: {e}")
            results[example_name] = {
                "countermodel_found": False,
                "solve_time": 0,
                "false_premise": False,
                "error": str(e)
            }
    
    return results

def main():
    """Test SK2 strategy and compare with MS (current default)."""
    
    # Test SK2 strategy
    sk2_results = test_strategy("SK2", test_examples)
    
    # Test MS strategy for comparison
    ms_results = test_strategy("MS", test_examples)
    
    # Compare results
    print(f"\n{'='*70}")
    print("COMPARISON SUMMARY")
    print(f"{'='*70}\n")
    
    print(f"{'Example':<30} {'SK2 Result':<20} {'MS Result':<20}")
    print("-" * 70)
    
    for example_name in test_examples:
        sk2 = sk2_results.get(example_name, {})
        ms = ms_results.get(example_name, {})
        
        sk2_status = "No model" if not sk2.get("countermodel_found") else \
                     ("FALSE PREMISE" if sk2.get("false_premise") else "Valid model")
        ms_status = "No model" if not ms.get("countermodel_found") else \
                    ("FALSE PREMISE" if ms.get("false_premise") else "Valid model")
        
        print(f"{example_name:<30} {sk2_status:<20} {ms_status:<20}")
    
    # Save results
    results_data = {
        "SK2": sk2_results,
        "MS": ms_results,
        "test_examples": test_examples
    }
    
    with open("sk2_test_results.json", "w") as f:
        json.dump(results_data, f, indent=2)
    
    print(f"\nResults saved to sk2_test_results.json")

if __name__ == "__main__":
    main()