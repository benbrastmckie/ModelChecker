"""
Simple baseline test runner for Phase 1

This script runs baseline tests on exclusion examples to identify
false premises and true conclusions.
"""

import time
import json
from datetime import datetime

from model_checker import model, syntactic
from model_checker.theory_lib.exclusion import (
    semantic,
    operators as exclusion_operators,
    examples
)


def test_example(name, example_data):
    """Test a single example for false premises and true conclusions."""
    premises, conclusions, settings = example_data
    
    # Use the operator collection from the module
    operator_collection = exclusion_operators.exclusion_operators
    
    # Create syntax with premises, conclusions, and operator collection
    syntax = syntactic.Syntax(premises, conclusions, operator_collection)
    
    # Create semantics with proper settings
    merged_settings = dict(settings)
    semantics = semantic.ExclusionSemantics(merged_settings)
    
    # Create constraints
    constraints = model.ModelConstraints(
        merged_settings, 
        syntax, 
        semantics, 
        semantic.UnilateralProposition
    )
    
    # Create model structure which handles solving
    model_structure = semantic.ExclusionStructure(constraints, merged_settings)
    
    # Check if model was found
    if model_structure.z3_model_status:
        
        # Interpret sentences to create propositions
        model_structure.interpret(syntax.premises + syntax.conclusions)
            
        # Check for false premises and true conclusions
        false_premises = []
        true_conclusions = []
        
        main_point = semantics.main_point
        
        # Check premises (should all be true)
        for premise in syntax.premises:
            if hasattr(premise, 'proposition') and premise.proposition:
                truth_value = premise.proposition.truth_value_at(main_point)
                if not truth_value:
                    false_premises.append(str(premise))
                    
        # Check conclusions (should all be false)  
        for conclusion in syntax.conclusions:
            if hasattr(conclusion, 'proposition') and conclusion.proposition:
                truth_value = conclusion.proposition.truth_value_at(main_point)
                if truth_value:
                    true_conclusions.append(str(conclusion))
                    
        return {
            'model_found': True,
            'false_premises': false_premises,
            'true_conclusions': true_conclusions,
            'valid': len(false_premises) == 0 and len(true_conclusions) == 0
        }
    else:
        return {
            'model_found': False,
            'valid': True  # No model is a valid result
        }


def main():
    """Run baseline tests on all examples."""
    print("="*60)
    print("BASELINE TESTING FOR EXCLUSION SEMANTICS")
    print("="*60)
    
    results = {
        'timestamp': datetime.now().isoformat(),
        'examples': {},
        'summary': {
            'total': 0,
            'model_found': 0,
            'no_model': 0,
            'valid': 0,
            'invalid': 0,
            'false_premise_count': 0,
            'true_conclusion_count': 0,
            'errors': 0
        }
    }
    
    # Get all examples
    example_range = examples.all_example_range
    
    print(f"\nTesting {len(example_range)} examples...\n")
    
    for name, example_data in example_range.items():
        print(f"Testing {name}...", end=' ')
        start_time = time.time()
        
        try:
            result = test_example(name, example_data)
            elapsed = time.time() - start_time
            
            results['examples'][name] = {
                **result,
                'time': elapsed,
                'error': None
            }
            
            results['summary']['total'] += 1
            
            if result['model_found']:
                results['summary']['model_found'] += 1
                if result['valid']:
                    results['summary']['valid'] += 1
                    print(f"✓ Valid model ({elapsed:.3f}s)")
                else:
                    results['summary']['invalid'] += 1
                    results['summary']['false_premise_count'] += len(result['false_premises'])
                    results['summary']['true_conclusion_count'] += len(result['true_conclusions'])
                    print(f"✗ Invalid model - FP:{len(result['false_premises'])} TC:{len(result['true_conclusions'])} ({elapsed:.3f}s)")
            else:
                results['summary']['no_model'] += 1
                results['summary']['valid'] += 1
                print(f"✓ No model ({elapsed:.3f}s)")
                
        except Exception as e:
            elapsed = time.time() - start_time
            results['examples'][name] = {
                'model_found': False,
                'valid': False,
                'error': str(e),
                'time': elapsed
            }
            results['summary']['errors'] += 1
            results['summary']['total'] += 1
            print(f"✗ Error: {str(e)[:50]}... ({elapsed:.3f}s)")
    
    # Calculate summary statistics
    if results['summary']['total'] > 0:
        results['summary']['success_rate'] = results['summary']['valid'] / results['summary']['total']
        results['summary']['model_rate'] = results['summary']['model_found'] / results['summary']['total']
        results['summary']['average_time'] = sum(ex['time'] for ex in results['examples'].values()) / results['summary']['total']
    else:
        results['summary']['success_rate'] = 0
        results['summary']['model_rate'] = 0
        results['summary']['average_time'] = 0
    
    # Print summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Total examples: {results['summary']['total']}")
    print(f"Valid results: {results['summary']['valid']} ({results['summary']['success_rate']:.1%})")
    print(f"Invalid models: {results['summary']['invalid']}")
    print(f"  - False premises: {results['summary']['false_premise_count']}")
    print(f"  - True conclusions: {results['summary']['true_conclusion_count']}")
    print(f"Errors: {results['summary']['errors']}")
    print(f"Average time: {results['summary']['average_time']:.3f}s")
    
    # Save results
    with open('baseline_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to baseline_results.json")
    
    return results


if __name__ == "__main__":
    main()