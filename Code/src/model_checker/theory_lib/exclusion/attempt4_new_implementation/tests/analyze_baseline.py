#!/usr/bin/env python3
"""
Analyze the current baseline behavior of exclusion theory with MS strategy.
Focus on identifying examples with false premises or true conclusions.
"""

import json
import time
import os
import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

# Import required modules
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionSemantics, 
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)
from model_checker.theory_lib.exclusion.examples import example_range

def check_example(name, example_data):
    """Check a single example for false premises or true conclusions."""
    try:
        # Unpack the example data
        premises = example_data[0]
        conclusions = example_data[1]
        settings = example_data[2]
        
        # Create semantics
        combined_settings = {**ExclusionSemantics.DEFAULT_EXAMPLE_SETTINGS, **settings}
        combined_settings['print_impossible'] = False
        combined_settings['print_constraints'] = False
        combined_settings['print_z3'] = False
        combined_settings['save_output'] = False
        
        semantics = ExclusionSemantics(combined_settings)
        
        # Create syntax and parse sentences
        syntax = Syntax(name, exclusion_operators)
        
        # Parse all sentences
        parsed_premises = [syntax.parse(p) for p in premises]
        parsed_conclusions = [syntax.parse(c) for c in conclusions]
        
        # Create structure and find model
        structure = ExclusionStructure(semantics)
        
        # Set premises and conclusions
        for premise in parsed_premises:
            structure.set_premise(premise)
        for conclusion in parsed_conclusions:
            structure.set_conclusion(conclusion)
            
        # Generate model
        has_model = structure.generate()
        
        if not has_model:
            return {
                'name': name,
                'has_model': False,
                'has_false_premise': False,
                'has_true_conclusion': False,
                'error': None
            }
            
        # Check premise and conclusion truth values
        has_false_premise = False
        has_true_conclusion = False
        
        # Create propositions to evaluate
        for premise in parsed_premises:
            prop = UnilateralProposition(premise, structure)
            if not prop.evaluate():
                has_false_premise = True
                break
                
        for conclusion in parsed_conclusions:
            prop = UnilateralProposition(conclusion, structure)
            if prop.evaluate():
                has_true_conclusion = True
                break
                
        return {
            'name': name,
            'has_model': True,
            'has_false_premise': has_false_premise,
            'has_true_conclusion': has_true_conclusion,
            'error': None
        }
        
    except Exception as e:
        return {
            'name': name,
            'has_model': False,
            'has_false_premise': False,
            'has_true_conclusion': False,
            'error': str(e)
        }

def main():
    """Analyze all examples for baseline behavior."""
    print("Analyzing baseline behavior with MS (Multi-Sort) strategy...")
    print(f"Total examples: {len(example_range)}")
    print()
    
    results = []
    problematic_examples = []
    
    for i, (name, settings) in enumerate(example_range.items(), 1):
        print(f"[{i}/{len(example_range)}] Checking {name}...", end='', flush=True)
        
        start_time = time.time()
        result = check_example(name, settings)
        result['execution_time'] = time.time() - start_time
        
        results.append(result)
        
        if result['has_false_premise'] or result['has_true_conclusion']:
            problematic_examples.append(name)
            print(f" ⚠️  FALSE PREMISE: {result['has_false_premise']}, TRUE CONCLUSION: {result['has_true_conclusion']}")
        elif result['error']:
            print(f" ❌ ERROR: {result['error']}")
        elif not result['has_model']:
            print(f" ✓ (no model)")
        else:
            print(f" ✓ (model found)")
    
    # Summary
    total = len(results)
    false_premise_count = sum(1 for r in results if r['has_false_premise'])
    true_conclusion_count = sum(1 for r in results if r['has_true_conclusion'])
    error_count = sum(1 for r in results if r['error'])
    no_model_count = sum(1 for r in results if not r['has_model'] and not r['error'])
    
    summary = {
        'strategy': 'MS (Multi-Sort) - Current Default',
        'total_examples': total,
        'false_premise_count': false_premise_count,
        'true_conclusion_count': true_conclusion_count,
        'error_count': error_count,
        'no_model_count': no_model_count,
        'problematic_examples': problematic_examples,
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S')
    }
    
    # Save results
    output = {
        'summary': summary,
        'detailed_results': results
    }
    
    output_file = Path(__file__).parent / 'current_ms_baseline.json'
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    # Print summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Total examples: {total}")
    print(f"Examples with no model (expected): {no_model_count}")
    print(f"Examples with false premises: {false_premise_count}")
    print(f"Examples with true conclusions: {true_conclusion_count}")
    print(f"Examples with errors: {error_count}")
    
    if problematic_examples:
        print(f"\nProblematic examples ({len(problematic_examples)}):")
        for ex in problematic_examples:
            print(f"  - {ex}")
    
    print(f"\nResults saved to: {output_file}")
    
    return false_premise_count > 0 or true_conclusion_count > 0

if __name__ == "__main__":
    has_issues = main()
    sys.exit(1 if has_issues else 0)