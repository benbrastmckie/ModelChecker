"""Comprehensive test of all exclusion strategies on ALL examples from examples.py.

This test ensures consistent model usage across strategies for fair comparison.
It loads all examples and tests each strategy with identical settings.
"""

import sys
import os
import time
import importlib.util
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
from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY, create_operator_collection
from model_checker import model, syntactic


def load_all_examples():
    """Load all examples from the examples.py file."""
    # Import the examples module
    from model_checker.theory_lib.exclusion import examples as ex
    
    # Get all example names that end with '_example'
    example_names = [name for name in dir(ex) if name.endswith('_example')]
    
    examples = []
    for name in example_names:
        try:
            example = getattr(ex, name)
            if isinstance(example, list) and len(example) >= 3:
                premises, conclusions, settings = example[0], example[1], example[2]
                # Clean name for display
                display_name = name.replace('_example', '')
                examples.append((display_name, premises, conclusions, settings))
        except Exception as e:
            print(f"Warning: Could not load example {name}: {e}")
    
    return examples


def normalize_settings(original_settings, strategy_name):
    """Normalize settings to ensure consistency across strategies."""
    # Use consistent base settings
    normalized = {
        'N': original_settings.get('N', 3),
        'possible': original_settings.get('possible', False),
        'contingent': original_settings.get('contingent', False), 
        'non_empty': original_settings.get('non_empty', False),
        'non_null': original_settings.get('non_null', False),
        'disjoint': original_settings.get('disjoint', False),
        'fusion_closure': original_settings.get('fusion_closure', False),
        'max_time': min(original_settings.get('max_time', 5), 5),  # Cap at 5 seconds
        'expectation': original_settings.get('expectation', None),
        'exclusion_strategy': strategy_name,
        'print_constraints': False,
        'print_z3': False,
        'print_impossible': False,
        'save_output': False,
        'maximize': False,
    }
    return normalized


def test_strategy_on_example(strategy_name, premises, conclusions, original_settings, example_name):
    """Test a single strategy on a single example with normalized settings."""
    settings = normalize_settings(original_settings, strategy_name)
    
    captured_output = StringIO()
    
    try:
        with redirect_stdout(captured_output):
            # Create semantics
            semantics = ExclusionSemantics(settings)
            
            # Create operator collection for this strategy
            operators = create_operator_collection(strategy_name)
            
            # Create syntax parser
            syntax = syntactic.Syntax(premises, conclusions, operators)
            
            # Create model constraints
            constraints = model.ModelConstraints(
                settings,
                syntax,
                semantics,
                UnilateralProposition
            )
            
            # Create model structure
            start_time = time.time()
            structure = ExclusionStructure(constraints, settings)
            runtime = time.time() - start_time
        
        if structure.z3_model and not getattr(structure, 'timeout', False):
            # Interpret sentences
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            
            main_point = structure.main_point
            
            # Count false premises
            false_premise_count = 0
            premise_truths = []
            for premise in syntax.premises:
                if premise.proposition:
                    truth = premise.proposition.truth_value_at(main_point)
                    premise_truths.append(truth)
                    if not truth:
                        false_premise_count += 1
            
            # Count true conclusions
            true_conclusion_count = 0
            conclusion_truths = []
            for conclusion in syntax.conclusions:
                if conclusion.proposition:
                    truth = conclusion.proposition.truth_value_at(main_point)
                    conclusion_truths.append(truth)
                    if truth:
                        true_conclusion_count += 1
            
            return {
                'model_found': True,
                'false_premise_count': false_premise_count,
                'true_conclusion_count': true_conclusion_count,
                'total_premises': len(premises),
                'total_conclusions': len(conclusions),
                'premise_truths': premise_truths,
                'conclusion_truths': conclusion_truths,
                'runtime': runtime,
                'timeout': False,
                'error': None
            }
        else:
            return {
                'model_found': False,
                'false_premise_count': 0,
                'true_conclusion_count': 0,
                'total_premises': len(premises),
                'total_conclusions': len(conclusions),
                'premise_truths': [],
                'conclusion_truths': [],
                'runtime': runtime,
                'timeout': getattr(structure, 'timeout', False),
                'error': None
            }
    except Exception as e:
        return {
            'model_found': False,
            'false_premise_count': 0,
            'true_conclusion_count': 0,
            'total_premises': len(premises),
            'total_conclusions': len(conclusions),
            'premise_truths': [],
            'conclusion_truths': [],
            'runtime': 0,
            'timeout': False,
            'error': str(e)[:100] + "..." if len(str(e)) > 100 else str(e)
        }


def main():
    """Test all strategies on all examples from examples.py."""
    
    # Load all examples
    examples = load_all_examples()
    
    # Focus on main strategies
    strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
    
    print("="*100)
    print("COMPREHENSIVE EVALUATION: ALL STRATEGIES ON ALL EXAMPLES")
    print("="*100)
    print(f"Testing {len(strategies)} strategies on {len(examples)} examples from examples.py\n")
    
    # Store all results
    all_results = {}
    strategy_summaries = {}
    
    # Test each strategy
    for strategy in strategies:
        print(f"\n{'='*50}")
        print(f"TESTING {strategy} STRATEGY")
        print(f"{'='*50}")
        
        strategy_results = {}
        total_models = 0
        total_false_premises = 0
        total_true_conclusions = 0
        total_runtime = 0
        error_count = 0
        timeout_count = 0
        models_with_issues = 0
        
        for example_name, premises, conclusions, original_settings in examples:
            result = test_strategy_on_example(strategy, premises, conclusions, original_settings, example_name)
            strategy_results[example_name] = result
            
            if result['error']:
                error_count += 1
                print(f"  ⚠ {example_name}: ERROR - {result['error']}")
                continue
            
            if result['timeout']:
                timeout_count += 1
                print(f"  ⏰ {example_name}: TIMEOUT")
                continue
            
            total_runtime += result['runtime']
            
            if result['model_found']:
                total_models += 1
                total_false_premises += result['false_premise_count']
                total_true_conclusions += result['true_conclusion_count']
                
                has_issues = result['false_premise_count'] > 0 or result['true_conclusion_count'] > 0
                if has_issues:
                    models_with_issues += 1
                
                # Print result
                issue_markers = []
                if result['false_premise_count'] > 0:
                    issue_markers.append(f"FP:{result['false_premise_count']}")
                if result['true_conclusion_count'] > 0:
                    issue_markers.append(f"TC:{result['true_conclusion_count']}")
                
                issue_str = " [" + ", ".join(issue_markers) + "]" if issue_markers else ""
                print(f"  ✓ {example_name}: Model found{issue_str} ({result['runtime']:.3f}s)")
            else:
                print(f"  - {example_name}: No model ({result['runtime']:.3f}s)")
        
        # Store strategy summary
        strategy_summaries[strategy] = {
            'total_models': total_models,
            'total_false_premises': total_false_premises,
            'total_true_conclusions': total_true_conclusions,
            'models_with_issues': models_with_issues,
            'avg_runtime': total_runtime / max(1, total_models),
            'total_runtime': total_runtime,
            'error_count': error_count,
            'timeout_count': timeout_count
        }
        
        all_results[strategy] = strategy_results
        
        print(f"\n{strategy} SUMMARY:")
        print(f"  Models found: {total_models}")
        print(f"  Models with issues: {models_with_issues}")
        print(f"  Total false premises: {total_false_premises}")
        print(f"  Total true conclusions: {total_true_conclusions}")
        print(f"  Average runtime: {total_runtime / max(1, total_models):.3f}s")
        print(f"  Errors: {error_count}, Timeouts: {timeout_count}")
    
    # Comprehensive analysis
    print(f"\n{'='*100}")
    print("COMPREHENSIVE ANALYSIS")
    print(f"{'='*100}")
    
    # Strategy comparison table
    print(f"\n{'Strategy':<10} {'Models':<8} {'Issues':<8} {'FP Total':<9} {'TC Total':<9} {'Issue%':<8} {'AvgTime':<9} {'Errors':<7}")
    print("-"*75)
    
    for strategy in strategies:
        stats = strategy_summaries[strategy]
        issue_rate = (stats['models_with_issues'] / max(1, stats['total_models'])) * 100
        print(f"{strategy:<10} {stats['total_models']:<8} {stats['models_with_issues']:<8} "
              f"{stats['total_false_premises']:<9} {stats['total_true_conclusions']:<9} "
              f"{issue_rate:<8.1f} {stats['avg_runtime']:<9.3f} {stats['error_count']:<7}")
    
    # Find examples that cause the most issues across strategies
    print(f"\n{'='*60}")
    print("MOST PROBLEMATIC EXAMPLES")
    print(f"{'='*60}")
    
    example_issue_counts = defaultdict(int)
    example_total_issues = defaultdict(int)
    
    for example_name, _, _, _ in examples:
        for strategy in strategies:
            if example_name in all_results[strategy]:
                result = all_results[strategy][example_name]
                if result['model_found'] and (result['false_premise_count'] > 0 or result['true_conclusion_count'] > 0):
                    example_issue_counts[example_name] += 1
                    example_total_issues[example_name] += result['false_premise_count'] + result['true_conclusion_count']
    
    # Sort by total issues across all strategies
    sorted_examples = sorted(example_total_issues.items(), key=lambda x: x[1], reverse=True)
    
    print("Top 10 most problematic examples (by total issues across all strategies):")
    for i, (example_name, total_issues) in enumerate(sorted_examples[:10], 1):
        strategies_affected = example_issue_counts[example_name]
        print(f"  {i:2}. {example_name}: {total_issues} total issues across {strategies_affected} strategies")
    
    # Find examples with no issues
    print(f"\n{'='*60}")
    print("EXAMPLES WITH NO ISSUES")
    print(f"{'='*60}")
    
    clean_examples = []
    for example_name, _, _, _ in examples:
        has_any_issues = False
        for strategy in strategies:
            if example_name in all_results[strategy]:
                result = all_results[strategy][example_name]
                if result['model_found'] and (result['false_premise_count'] > 0 or result['true_conclusion_count'] > 0):
                    has_any_issues = True
                    break
        
        if not has_any_issues:
            # Count how many strategies found models
            models_found = sum(1 for strategy in strategies 
                             if example_name in all_results[strategy] and 
                             all_results[strategy][example_name]['model_found'])
            clean_examples.append((example_name, models_found))
    
    if clean_examples:
        print("Examples with no false premises or true conclusions across any strategy:")
        for example_name, models_found in sorted(clean_examples, key=lambda x: x[1], reverse=True):
            print(f"  - {example_name}: {models_found} strategies found valid models")
    else:
        print("No examples are completely free of issues across all strategies.")
    
    # Strategy ranking
    print(f"\n{'='*60}")
    print("STRATEGY RANKINGS")
    print(f"{'='*60}")
    
    # By total issues
    by_issues = sorted(strategies, key=lambda s: strategy_summaries[s]['total_false_premises'] + 
                                                strategy_summaries[s]['total_true_conclusions'])
    print("By total issues (fewer is better):")
    for i, strategy in enumerate(by_issues, 1):
        stats = strategy_summaries[strategy]
        total_issues = stats['total_false_premises'] + stats['total_true_conclusions']
        print(f"  {i}. {strategy}: {total_issues} total issues")
    
    # By performance
    by_speed = sorted([s for s in strategies if strategy_summaries[s]['total_models'] > 0], 
                     key=lambda s: strategy_summaries[s]['avg_runtime'])
    print("\nBy average speed (faster is better):")
    for i, strategy in enumerate(by_speed, 1):
        stats = strategy_summaries[strategy]
        print(f"  {i}. {strategy}: {stats['avg_runtime']:.3f}s average")
    
    # Final summary statistics
    print(f"\n{'='*100}")
    print("FINAL SUMMARY")
    print(f"{'='*100}")
    
    total_examples = len(examples)
    total_tests = len(strategies) * total_examples
    total_models_found = sum(stats['total_models'] for stats in strategy_summaries.values())
    total_issues_found = sum(stats['total_false_premises'] + stats['total_true_conclusions'] 
                           for stats in strategy_summaries.values())
    
    print(f"Total examples tested: {total_examples}")
    print(f"Total strategy-example combinations: {total_tests}")
    print(f"Total models found: {total_models_found}")
    print(f"Total logical issues detected: {total_issues_found}")
    print(f"Average issues per model: {total_issues_found / max(1, total_models_found):.2f}")
    
    best_strategy = by_issues[0]
    fastest_strategy = by_speed[0]
    print(f"\nBest overall strategy (fewest issues): {best_strategy}")
    print(f"Fastest strategy: {fastest_strategy}")


if __name__ == '__main__':
    main()