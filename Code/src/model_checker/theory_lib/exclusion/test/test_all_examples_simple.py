"""Simple test of all strategies on all examples - saves results to file."""

import sys
import os
import json
from io import StringIO
from contextlib import redirect_stdout

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic


def load_examples():
    """Load all examples from examples.py."""
    from model_checker.theory_lib.exclusion import examples as ex
    
    examples = []
    for name in dir(ex):
        if name.endswith('_example'):
            try:
                example = getattr(ex, name)
                if isinstance(example, list) and len(example) >= 3:
                    display_name = name.replace('_example', '')
                    examples.append((display_name, example[0], example[1], example[2]))
            except:
                continue
    return examples


def test_strategy(strategy_name, examples_subset):
    """Test one strategy on a subset of examples."""
    print(f"Testing {strategy_name}...", flush=True)
    
    results = {}
    for example_name, premises, conclusions, settings in examples_subset:
        test_settings = {
            'N': min(settings.get('N', 3), 3),
            'possible': settings.get('possible', False),
            'contingent': settings.get('contingent', False),
            'non_empty': settings.get('non_empty', False),
            'non_null': settings.get('non_null', False),
            'disjoint': settings.get('disjoint', False),
            'fusion_closure': settings.get('fusion_closure', False),
            'max_time': 0.5,  # Very short timeout
            'exclusion_strategy': strategy_name,
            'print_constraints': False,
            'print_z3': False,
        }
        
        try:
            with redirect_stdout(StringIO()):
                semantics = ExclusionSemantics(test_settings)
                operators = create_operator_collection(strategy_name)
                syntax = syntactic.Syntax(premises, conclusions, operators)
                constraints = model.ModelConstraints(test_settings, syntax, semantics, UnilateralProposition)
                structure = ExclusionStructure(constraints, test_settings)
            
            if structure.z3_model and not getattr(structure, 'timeout', False):
                structure.interpret(syntax.premises)
                structure.interpret(syntax.conclusions)
                main_point = structure.main_point
                
                fp = sum(1 for p in syntax.premises 
                        if p.proposition and not p.proposition.truth_value_at(main_point))
                tc = sum(1 for c in syntax.conclusions 
                        if c.proposition and c.proposition.truth_value_at(main_point))
                
                results[example_name] = {
                    'model': True,
                    'false_premises': fp,
                    'true_conclusions': tc,
                    'total_premises': len(premises),
                    'total_conclusions': len(conclusions)
                }
            else:
                results[example_name] = {'model': False}
        except:
            results[example_name] = {'model': False, 'error': True}
    
    return results


def main():
    """Test strategies efficiently and save results."""
    examples = load_examples()
    strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
    
    print(f"Testing {len(strategies)} strategies on {len(examples)} examples")
    print("Using very short timeouts for efficiency...")
    
    all_results = {}
    
    # Test each strategy
    for strategy in strategies:
        try:
            results = test_strategy(strategy, examples)
            all_results[strategy] = results
            
            # Quick summary
            models = sum(1 for r in results.values() if r.get('model', False))
            issues = sum(1 for r in results.values() 
                        if r.get('model', False) and 
                        (r.get('false_premises', 0) > 0 or r.get('true_conclusions', 0) > 0))
            fp_total = sum(r.get('false_premises', 0) for r in results.values())
            tc_total = sum(r.get('true_conclusions', 0) for r in results.values())
            
            print(f"  {strategy}: {models} models, {issues} with issues, {fp_total} FP, {tc_total} TC")
        except Exception as e:
            print(f"  {strategy}: ERROR - {e}")
            all_results[strategy] = {}
    
    # Save results
    output_file = 'exclusion_strategy_results.json'
    with open(output_file, 'w') as f:
        json.dump(all_results, f, indent=2)
    
    print(f"\nResults saved to {output_file}")
    
    # Quick analysis
    print(f"\n{'='*60}")
    print("QUICK ANALYSIS")
    print(f"{'='*60}")
    
    strategy_stats = {}
    for strategy, results in all_results.items():
        models = sum(1 for r in results.values() if r.get('model', False))
        fp_total = sum(r.get('false_premises', 0) for r in results.values())
        tc_total = sum(r.get('true_conclusions', 0) for r in results.values())
        total_issues = fp_total + tc_total
        
        strategy_stats[strategy] = {
            'models': models,
            'fp_total': fp_total,
            'tc_total': tc_total,
            'total_issues': total_issues
        }
    
    print(f"{'Strategy':<10} {'Models':<8} {'FP':<6} {'TC':<6} {'Total Issues'}")
    print("-"*45)
    for strategy in strategies:
        stats = strategy_stats[strategy]
        print(f"{strategy:<10} {stats['models']:<8} {stats['fp_total']:<6} "
              f"{stats['tc_total']:<6} {stats['total_issues']}")
    
    # Rankings
    by_issues = sorted(strategies, key=lambda s: strategy_stats[s]['total_issues'])
    print(f"\nBy total issues (best to worst): {', '.join(by_issues)}")
    
    return all_results


if __name__ == '__main__':
    main()