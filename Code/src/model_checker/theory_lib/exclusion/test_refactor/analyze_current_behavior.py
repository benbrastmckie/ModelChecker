#!/usr/bin/env python3
"""
Analyze current behavior of exclusion theory with MS (Multi-Sort) strategy.
Documents which examples have false premises or true conclusions.
"""

import json
import time
import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from model_checker.builder import BuildExample
from model_checker.theory_lib.exclusion import exclusion_operators
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics
from model_checker.theory_lib.exclusion.examples import example_range

def analyze_example(name, settings):
    """Analyze a single example and return metrics."""
    start_time = time.time()
    
    try:
        # Create example
        example = BuildExample(
            example_name=name,
            theory="exclusion",
            syntax_module_name="exclusion",
            semantics_class=ExclusionSemantics,
            proposition_class_name="UnilateralProposition",
            structure_class_name="ExclusionStructure",
            operators=exclusion_operators,
            example_settings=settings
        )
        
        # Build the example
        result = example.main()
        
        # Check for models
        models_found = result.get('models_found', 0)
        
        # Initialize metrics
        metrics = {
            'name': name,
            'models_found': models_found,
            'has_false_premise': False,
            'has_true_conclusion': False,
            'execution_time': time.time() - start_time,
            'error': None
        }
        
        # If models found, check premise/conclusion behavior
        if models_found > 0 and 'model_structures' in result:
            for model in result['model_structures']:
                # Check premises
                if hasattr(model, 'premises') and model.premises:
                    for premise in model.premises:
                        if hasattr(premise, 'evaluate') and not premise.evaluate():
                            metrics['has_false_premise'] = True
                            
                # Check conclusions  
                if hasattr(model, 'conclusions') and model.conclusions:
                    for conclusion in model.conclusions:
                        if hasattr(conclusion, 'evaluate') and conclusion.evaluate():
                            metrics['has_true_conclusion'] = True
                            
        return metrics
        
    except Exception as e:
        return {
            'name': name,
            'models_found': 0,
            'has_false_premise': False,
            'has_true_conclusion': False,
            'execution_time': time.time() - start_time,
            'error': str(e)
        }

def main():
    """Run analysis on all examples."""
    print("Analyzing current behavior with MS (Multi-Sort) strategy...")
    print(f"Total examples to analyze: {len(example_range)}")
    print()
    
    results = []
    problematic_examples = []
    
    for i, (name, settings) in enumerate(example_range.items(), 1):
        print(f"[{i}/{len(example_range)}] Analyzing {name}...", end='', flush=True)
        
        metrics = analyze_example(name, settings)
        results.append(metrics)
        
        # Check if problematic
        if metrics['has_false_premise'] or metrics['has_true_conclusion']:
            problematic_examples.append(name)
            print(f" ⚠️  FALSE PREMISE: {metrics['has_false_premise']}, TRUE CONCLUSION: {metrics['has_true_conclusion']}")
        elif metrics['error']:
            print(f" ❌ ERROR: {metrics['error']}")
        else:
            print(f" ✓ ({metrics['models_found']} models, {metrics['execution_time']:.2f}s)")
    
    # Summary statistics
    total_examples = len(results)
    false_premise_count = sum(1 for r in results if r['has_false_premise'])
    true_conclusion_count = sum(1 for r in results if r['has_true_conclusion'])
    error_count = sum(1 for r in results if r['error'])
    avg_execution_time = sum(r['execution_time'] for r in results) / total_examples
    
    summary = {
        'strategy': 'MS (Multi-Sort)',
        'total_examples': total_examples,
        'false_premise_count': false_premise_count,
        'true_conclusion_count': true_conclusion_count,
        'error_count': error_count,
        'problematic_examples': problematic_examples,
        'average_execution_time': avg_execution_time,
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S')
    }
    
    # Save results
    output = {
        'summary': summary,
        'detailed_results': results
    }
    
    with open('current_ms_baseline.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    # Print summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Total examples analyzed: {total_examples}")
    print(f"Examples with false premises: {false_premise_count}")
    print(f"Examples with true conclusions: {true_conclusion_count}")
    print(f"Examples with errors: {error_count}")
    print(f"Average execution time: {avg_execution_time:.2f}s")
    print(f"\nProblematic examples: {', '.join(problematic_examples) if problematic_examples else 'None'}")
    print(f"\nResults saved to: current_ms_baseline.json")

if __name__ == "__main__":
    main()