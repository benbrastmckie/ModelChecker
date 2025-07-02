"""
Test runner for SK implementation on problematic examples

This script specifically tests the SK implementation on the 8 examples
that showed false premises in the baseline tests.
"""

import time
import json
from datetime import datetime

from model_checker import model, syntactic
from model_checker.theory_lib.exclusion import examples
from model_checker.theory_lib.exclusion import semantic
from model_checker.theory_lib.exclusion.sk_exclusion import create_sk_operators
from model_checker.theory_lib.exclusion.sk_semantic import SKExclusionSemantics


# The 8 problematic examples from baseline
PROBLEMATIC_EXAMPLES = {
    "DN_ELIM": examples.DN_ELIM_example,
    "TN_ENTAIL": examples.TN_ENTAIL_example,
    "QN_ENTAIL": examples.QN_ENTAIL_example,
    "CONJ_DM_LR": examples.CONJ_DM_LR_example,
    "CONJ_DM_RL": examples.CONJ_DM_RL_example,
    "DISJ_DM_LR": examples.DISJ_DM_LR_example,
    "DISJ_DM_RL": examples.DISJ_DM_RL_example,
    "EX_TH_17": examples.EX_TH_17_example,
}


def test_sk_example(name, example_data):
    """Test a single example with SK implementation."""
    premises, conclusions, settings = example_data
    
    # Use SK operators
    operator_collection = create_sk_operators()
    
    # Create syntax with SK operators
    syntax = syntactic.Syntax(premises, conclusions, operator_collection)
    
    # Create SK semantics
    merged_settings = dict(settings)
    semantics = SKExclusionSemantics(merged_settings)
    
    # Initialize operators with SK semantics
    for op_name, op_class in operator_collection.items():
        # Create instance with SK semantics
        op_instance = op_class(semantics)
        # Store in semantics for access
        if not hasattr(semantics, 'operators'):
            semantics.operators = {}
        semantics.operators[op_name] = op_instance
    
    # Create constraints
    constraints = model.ModelConstraints(
        merged_settings, 
        syntax, 
        semantics, 
        semantic.UnilateralProposition
    )
    
    # Create model structure
    model_structure = semantic.ExclusionStructure(constraints, merged_settings)
    
    # Check if model was found
    if model_structure.z3_model_status:
        # Interpret sentences
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
    """Run SK tests on problematic examples."""
    print("="*60)
    print("SK IMPLEMENTATION TESTING - PROBLEMATIC EXAMPLES")
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
    
    print(f"\nTesting {len(PROBLEMATIC_EXAMPLES)} problematic examples...\n")
    
    for name, example_data in PROBLEMATIC_EXAMPLES.items():
        print(f"Testing {name}...", end=' ')
        start_time = time.time()
        
        try:
            result = test_sk_example(name, example_data)
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
                    print(f"✓ Valid model - FIXED! ({elapsed:.3f}s)")
                else:
                    results['summary']['invalid'] += 1
                    results['summary']['false_premise_count'] += len(result.get('false_premises', []))
                    results['summary']['true_conclusion_count'] += len(result.get('true_conclusions', []))
                    fp_count = len(result.get('false_premises', []))
                    tc_count = len(result.get('true_conclusions', []))
                    print(f"✗ Still has issues - FP:{fp_count} TC:{tc_count} ({elapsed:.3f}s)")
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
    
    # Compare with baseline
    print("\n" + "="*60)
    print("IMPROVEMENT FROM BASELINE")
    print("="*60)
    print("Baseline: 8 examples with false premises")
    fixed_count = results['summary']['valid'] - (results['summary']['total'] - results['summary']['model_found'])
    print(f"SK Fixed: {fixed_count} examples")
    if results['summary']['invalid'] > 0:
        print(f"Still problematic: {results['summary']['invalid']} examples")
    
    # Save results
    with open('sk_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to sk_results.json")
    
    return results


if __name__ == "__main__":
    main()