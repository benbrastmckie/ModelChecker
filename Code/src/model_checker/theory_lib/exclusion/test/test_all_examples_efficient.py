"""Efficient test of all exclusion strategies on ALL examples from examples.py.

This version uses shorter timeouts and focuses on getting comprehensive results quickly.
"""

import sys
import os
import time
from io import StringIO
from contextlib import redirect_stdout
from collections import defaultdict

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic


def load_all_examples():
    """Load all examples from the examples.py file."""
    from model_checker.theory_lib.exclusion import examples as ex
    
    example_names = [name for name in dir(ex) if name.endswith('_example')]
    
    examples = []
    for name in example_names:
        try:
            example = getattr(ex, name)
            if isinstance(example, list) and len(example) >= 3:
                premises, conclusions, settings = example[0], example[1], example[2]
                display_name = name.replace('_example', '')
                examples.append((display_name, premises, conclusions, settings))
        except Exception:
            continue
    
    return examples


def test_strategy_fast(strategy_name, premises, conclusions, original_settings, example_name):
    """Fast test with short timeout."""
    settings = {
        'N': min(original_settings.get('N', 3), 3),  # Cap at 3
        'possible': original_settings.get('possible', False),
        'contingent': original_settings.get('contingent', False), 
        'non_empty': original_settings.get('non_empty', False),
        'non_null': original_settings.get('non_null', False),
        'disjoint': original_settings.get('disjoint', False),
        'fusion_closure': original_settings.get('fusion_closure', False),
        'max_time': 1,  # Short timeout
        'expectation': None,
        'exclusion_strategy': strategy_name,
        'print_constraints': False,
        'print_z3': False,
        'print_impossible': False,
    }
    
    try:
        with redirect_stdout(StringIO()):
            semantics = ExclusionSemantics(settings)
            operators = create_operator_collection(strategy_name)
            syntax = syntactic.Syntax(premises, conclusions, operators)
            constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
            
            start_time = time.time()
            structure = ExclusionStructure(constraints, settings)
            runtime = time.time() - start_time
        
        if structure.z3_model and not getattr(structure, 'timeout', False):
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            main_point = structure.main_point
            
            false_premises = sum(1 for p in syntax.premises 
                               if p.proposition and not p.proposition.truth_value_at(main_point))
            true_conclusions = sum(1 for c in syntax.conclusions 
                                 if c.proposition and c.proposition.truth_value_at(main_point))
            
            return {
                'model_found': True,
                'false_premises': false_premises,
                'true_conclusions': true_conclusions,
                'total_premises': len(premises),
                'total_conclusions': len(conclusions),
                'runtime': runtime,
                'timeout': False
            }
        else:
            return {
                'model_found': False,
                'false_premises': 0,
                'true_conclusions': 0,
                'total_premises': len(premises),
                'total_conclusions': len(conclusions),
                'runtime': runtime,
                'timeout': getattr(structure, 'timeout', False)
            }
    except Exception:
        return {
            'model_found': False,
            'false_premises': 0,
            'true_conclusions': 0,
            'total_premises': len(premises),
            'total_conclusions': len(conclusions),
            'runtime': 0,
            'timeout': False,
            'error': True
        }


def main():
    """Efficient test of all strategies on all examples."""
    
    examples = load_all_examples()
    strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
    
    print("="*80)
    print("EFFICIENT COMPREHENSIVE EVALUATION")
    print("="*80)
    print(f"Testing {len(strategies)} strategies on {len(examples)} examples\n")
    
    # Store results
    all_results = {}
    strategy_stats = {}
    
    # Test each strategy
    for strategy in strategies:
        print(f"Testing {strategy}...", end=" ", flush=True)
        
        strategy_results = {}
        models_found = 0
        total_fp = 0
        total_tc = 0
        models_with_issues = 0
        total_runtime = 0
        timeouts = 0
        errors = 0
        
        for example_name, premises, conclusions, settings in examples:
            result = test_strategy_fast(strategy, premises, conclusions, settings, example_name)
            strategy_results[example_name] = result
            
            if result.get('error', False):
                errors += 1
                continue
            
            if result['timeout']:
                timeouts += 1
                continue
            
            total_runtime += result['runtime']
            
            if result['model_found']:
                models_found += 1
                total_fp += result['false_premises']
                total_tc += result['true_conclusions']
                if result['false_premises'] > 0 or result['true_conclusions'] > 0:
                    models_with_issues += 1
        
        strategy_stats[strategy] = {
            'models_found': models_found,
            'total_fp': total_fp,
            'total_tc': total_tc,
            'models_with_issues': models_with_issues,
            'avg_runtime': total_runtime / max(1, models_found),
            'timeouts': timeouts,
            'errors': errors
        }
        
        all_results[strategy] = strategy_results
        
        print(f"Models: {models_found}, Issues: {models_with_issues}, "
              f"FP: {total_fp}, TC: {total_tc}, Avg: {total_runtime / max(1, models_found):.3f}s")
    
    # Summary table
    print(f"\n{'='*80}")
    print("STRATEGY COMPARISON")
    print(f"{'='*80}")
    print(f"{'Strategy':<10} {'Models':<8} {'Issues':<8} {'FP':<6} {'TC':<6} {'Total':<7} {'AvgTime':<9} {'Timeouts':<9}")
    print("-"*70)
    
    for strategy in strategies:
        stats = strategy_stats[strategy]
        total_issues = stats['total_fp'] + stats['total_tc']
        print(f"{strategy:<10} {stats['models_found']:<8} {stats['models_with_issues']:<8} "
              f"{stats['total_fp']:<6} {stats['total_tc']:<6} {total_issues:<7} "
              f"{stats['avg_runtime']:<9.3f} {stats['timeouts']:<9}")
    
    # Find most problematic examples
    print(f"\n{'='*80}")
    print("MOST PROBLEMATIC EXAMPLES")
    print(f"{'='*80}")
    
    example_issues = defaultdict(int)
    example_strategies = defaultdict(int)
    
    for example_name, _, _, _ in examples:
        for strategy in strategies:
            if example_name in all_results[strategy]:
                result = all_results[strategy][example_name]
                if result['model_found']:
                    example_strategies[example_name] += 1
                    if result['false_premises'] > 0 or result['true_conclusions'] > 0:
                        example_issues[example_name] += result['false_premises'] + result['true_conclusions']
    
    # Sort by total issues
    sorted_examples = sorted(example_issues.items(), key=lambda x: x[1], reverse=True)
    
    print("Top 15 examples by total issues across all strategies:")
    for i, (example_name, total_issues) in enumerate(sorted_examples[:15], 1):
        strategies_with_models = example_strategies[example_name]
        print(f"  {i:2}. {example_name:<20}: {total_issues:3} issues across {strategies_with_models} strategies")
    
    # Find clean examples
    print(f"\n{'='*40}")
    print("EXAMPLES WITH NO ISSUES")
    print(f"{'='*40}")
    
    clean_examples = []
    for example_name, _, _, _ in examples:
        if example_name not in example_issues and example_strategies[example_name] > 0:
            clean_examples.append((example_name, example_strategies[example_name]))
    
    if clean_examples:
        print("Examples with no false premises or true conclusions:")
        for example_name, model_count in sorted(clean_examples, key=lambda x: x[1], reverse=True):
            print(f"  - {example_name}: {model_count} strategies found valid models")
    else:
        print("No examples are completely free of issues.")
    
    # Strategy rankings
    print(f"\n{'='*80}")
    print("STRATEGY RANKINGS")
    print(f"{'='*80}")
    
    # By total issues
    by_issues = sorted(strategies, key=lambda s: strategy_stats[s]['total_fp'] + strategy_stats[s]['total_tc'])
    print("1. By total issues (fewer is better):")
    for i, strategy in enumerate(by_issues, 1):
        stats = strategy_stats[strategy]
        total = stats['total_fp'] + stats['total_tc']
        print(f"   {i}. {strategy}: {total} total issues ({stats['total_fp']} FP + {stats['total_tc']} TC)")
    
    # By models with issues
    by_issue_models = sorted(strategies, key=lambda s: strategy_stats[s]['models_with_issues'])
    print("\n2. By models with issues (fewer is better):")
    for i, strategy in enumerate(by_issue_models, 1):
        stats = strategy_stats[strategy]
        rate = stats['models_with_issues'] / max(1, stats['models_found']) * 100
        print(f"   {i}. {strategy}: {stats['models_with_issues']}/{stats['models_found']} models with issues ({rate:.1f}%)")
    
    # By speed
    by_speed = sorted([s for s in strategies if strategy_stats[s]['models_found'] > 0], 
                     key=lambda s: strategy_stats[s]['avg_runtime'])
    print("\n3. By speed (faster is better):")
    for i, strategy in enumerate(by_speed, 1):
        stats = strategy_stats[strategy]
        print(f"   {i}. {strategy}: {stats['avg_runtime']:.3f}s average")
    
    # Final recommendations
    print(f"\n{'='*80}")
    print("RECOMMENDATIONS")
    print(f"{'='*80}")
    
    best_overall = by_issues[0]
    fastest = by_speed[0]
    fewest_bad_models = by_issue_models[0]
    
    print(f"🏆 Best overall (fewest total issues): {best_overall}")
    print(f"⚡ Fastest: {fastest}")
    print(f"🎯 Fewest models with issues: {fewest_bad_models}")
    
    # Final stats
    total_models = sum(stats['models_found'] for stats in strategy_stats.values())
    total_issues = sum(stats['total_fp'] + stats['total_tc'] for stats in strategy_stats.values())
    
    print(f"\nOverall statistics:")
    print(f"- Total models found across all strategies: {total_models}")
    print(f"- Total logical issues detected: {total_issues}")
    print(f"- Average issues per model: {total_issues / max(1, total_models):.2f}")


if __name__ == '__main__':
    main()