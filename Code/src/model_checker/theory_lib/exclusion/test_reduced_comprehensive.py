"""
Comprehensive test of reduced semantics on all exclusion examples.

This is Phase 4 of the reduced semantics implementation, testing
the complete system on all 34 examples with focus on the 8 problematic ones.
"""

import time
import json
from datetime import datetime

from model_checker import model, syntactic
from model_checker.theory_lib.exclusion import examples
from model_checker.theory_lib.exclusion.reduced_theory import reduced_exclusion_theory
from model_checker.theory_lib.exclusion.reduced_semantic import (
    ReducedExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure
)


# The 8 problematic examples identified in baseline
PROBLEMATIC_EXAMPLES = {
    "DN_ELIM", "TN_ENTAIL", "QN_ENTAIL", "CONJ_DM_LR",
    "CONJ_DM_RL", "DISJ_DM_LR", "DISJ_DM_RL", "EX_TH_17"
}


def test_example(name, example_data):
    """Test a single example with reduced semantics."""
    premises, conclusions, settings = example_data
    
    # Get reduced theory components
    theory = reduced_exclusion_theory()
    operator_collection = theory['operators']
    
    # Create syntax
    syntax = syntactic.Syntax(premises, conclusions, operator_collection)
    
    # Create reduced semantics
    merged_settings = dict(settings)
    semantics = ReducedExclusionSemantics(merged_settings)
    
    # Create constraints
    constraints = model.ModelConstraints(
        merged_settings,
        syntax,
        semantics,
        UnilateralProposition
    )
    
    # Create model structure
    model_structure = ExclusionStructure(constraints, merged_settings)
    
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
            'valid': len(false_premises) == 0 and len(true_conclusions) == 0,
            'is_problematic': name in PROBLEMATIC_EXAMPLES
        }
    else:
        return {
            'model_found': False,
            'valid': True,  # No model means valid
            'is_problematic': name in PROBLEMATIC_EXAMPLES
        }


def load_all_examples():
    """Load all 34 examples from the examples module."""
    all_examples = {}
    
    # Get all example names
    for attr_name in dir(examples):
        if attr_name.endswith('_example') and not attr_name.startswith('_'):
            example_name = attr_name[:-8]  # Remove '_example' suffix
            example_data = getattr(examples, attr_name)
            all_examples[example_name] = example_data
    
    return all_examples


def main():
    """Run comprehensive tests on all examples."""
    print("="*60)
    print("REDUCED SEMANTICS COMPREHENSIVE TESTING")
    print("="*60)
    
    all_examples = load_all_examples()
    
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
            'errors': 0,
            'problematic_fixed': 0,
            'problematic_still_broken': 0
        }
    }
    
    print(f"\nTesting {len(all_examples)} examples...\n")
    
    # Test each example
    for name, example_data in sorted(all_examples.items()):
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
                    if result['is_problematic']:
                        results['summary']['problematic_fixed'] += 1
                        print(f"✓ FIXED! Valid model ({elapsed:.3f}s)")
                    else:
                        print(f"✓ Valid model ({elapsed:.3f}s)")
                else:
                    results['summary']['invalid'] += 1
                    results['summary']['false_premise_count'] += len(result.get('false_premises', []))
                    results['summary']['true_conclusion_count'] += len(result.get('true_conclusions', []))
                    if result['is_problematic']:
                        results['summary']['problematic_still_broken'] += 1
                    fp_count = len(result.get('false_premises', []))
                    tc_count = len(result.get('true_conclusions', []))
                    print(f"✗ Invalid - FP:{fp_count} TC:{tc_count} ({elapsed:.3f}s)")
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
                'time': elapsed,
                'is_problematic': name in PROBLEMATIC_EXAMPLES
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
    
    # Report on problematic examples
    print("\n" + "="*60)
    print("PROBLEMATIC EXAMPLES STATUS")
    print("="*60)
    print(f"Originally problematic: 8")
    print(f"Fixed by reduced semantics: {results['summary']['problematic_fixed']}")
    print(f"Still broken: {results['summary']['problematic_still_broken']}")
    
    # List which problematic examples were fixed
    if results['summary']['problematic_fixed'] > 0:
        print("\nFixed examples:")
        for name, result in results['examples'].items():
            if result.get('is_problematic') and result.get('valid') and not result.get('error'):
                print(f"  - {name}")
    
    # List which are still broken
    if results['summary']['problematic_still_broken'] > 0:
        print("\nStill broken:")
        for name, result in results['examples'].items():
            if result.get('is_problematic') and not result.get('valid'):
                fp = result.get('false_premises', [])
                tc = result.get('true_conclusions', [])
                print(f"  - {name}: FP={len(fp)} TC={len(tc)}")
                if fp:
                    print(f"      False premises: {fp}")
                if tc:
                    print(f"      True conclusions: {tc}")
    
    # Save results
    with open('reduced_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to reduced_results.json")
    
    return results


if __name__ == "__main__":
    main()