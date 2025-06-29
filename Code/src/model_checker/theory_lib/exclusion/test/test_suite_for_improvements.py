"""Test suite for evaluating theory improvements.

This test suite is designed to be reused when making changes to exclusion theories
to improve false premise and true conclusion rates. It provides comprehensive
evaluation across all strategies and examples.

Usage:
    python test_suite_for_improvements.py [--strategies QA,MS,CD] [--timeout 2]
"""

import sys
import os
import time
import argparse
import json
from datetime import datetime
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
            except Exception as e:
                print(f"Warning: Could not load {name}: {e}")
    
    return examples


def test_strategy_on_example(strategy_name, premises, conclusions, original_settings, example_name, timeout=2):
    """Test a single strategy on a single example."""
    settings = {
        'N': min(original_settings.get('N', 3), 3),
        'possible': original_settings.get('possible', False),
        'contingent': original_settings.get('contingent', False),
        'non_empty': original_settings.get('non_empty', False),
        'non_null': original_settings.get('non_null', False),
        'disjoint': original_settings.get('disjoint', False),
        'fusion_closure': original_settings.get('fusion_closure', False),
        'max_time': timeout,
        'expectation': original_settings.get('expectation', None),
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
            
            # Detailed premise analysis
            premise_results = []
            false_premise_count = 0
            for i, premise in enumerate(syntax.premises):
                if premise.proposition:
                    truth = premise.proposition.truth_value_at(main_point)
                    premise_results.append({'text': premises[i], 'truth': truth})
                    if not truth:
                        false_premise_count += 1
            
            # Detailed conclusion analysis
            conclusion_results = []
            true_conclusion_count = 0
            for i, conclusion in enumerate(syntax.conclusions):
                if conclusion.proposition:
                    truth = conclusion.proposition.truth_value_at(main_point)
                    conclusion_results.append({'text': conclusions[i], 'truth': truth})
                    if truth:
                        true_conclusion_count += 1
            
            return {
                'model_found': True,
                'false_premise_count': false_premise_count,
                'true_conclusion_count': true_conclusion_count,
                'total_premises': len(premises),
                'total_conclusions': len(conclusions),
                'premise_details': premise_results,
                'conclusion_details': conclusion_results,
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
                'premise_details': [],
                'conclusion_details': [],
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
            'premise_details': [],
            'conclusion_details': [],
            'runtime': 0,
            'timeout': False,
            'error': str(e)
        }


def run_evaluation(strategies=None, timeout=2, save_results=True):
    """Run comprehensive evaluation of strategies."""
    if strategies is None:
        strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
    
    examples = load_all_examples()
    
    print("="*80)
    print("EXCLUSION THEORY EVALUATION SUITE")
    print("="*80)
    print(f"Testing {len(strategies)} strategies on {len(examples)} examples")
    print(f"Timeout: {timeout}s per example")
    print(f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    all_results = {}
    strategy_summaries = {}
    
    # Test each strategy
    for strategy in strategies:
        print(f"Testing {strategy} strategy...")
        
        strategy_results = {}
        total_models = 0
        total_false_premises = 0
        total_true_conclusions = 0
        models_with_issues = 0
        total_runtime = 0
        timeouts = 0
        errors = 0
        examples_with_fp = []
        examples_with_tc = []
        
        for example_name, premises, conclusions, original_settings in examples:
            result = test_strategy_on_example(
                strategy, premises, conclusions, original_settings, example_name, timeout
            )
            strategy_results[example_name] = result
            
            if result['error']:
                errors += 1
                continue
            
            if result['timeout']:
                timeouts += 1
                continue
            
            total_runtime += result['runtime']
            
            if result['model_found']:
                total_models += 1
                total_false_premises += result['false_premise_count']
                total_true_conclusions += result['true_conclusion_count']
                
                if result['false_premise_count'] > 0:
                    examples_with_fp.append(example_name)
                if result['true_conclusion_count'] > 0:
                    examples_with_tc.append(example_name)
                if result['false_premise_count'] > 0 or result['true_conclusion_count'] > 0:
                    models_with_issues += 1
        
        strategy_summaries[strategy] = {
            'total_models': total_models,
            'total_false_premises': total_false_premises,
            'total_true_conclusions': total_true_conclusions,
            'models_with_issues': models_with_issues,
            'avg_runtime': total_runtime / max(1, total_models),
            'total_runtime': total_runtime,
            'timeouts': timeouts,
            'errors': errors,
            'examples_with_fp': examples_with_fp,
            'examples_with_tc': examples_with_tc
        }
        
        all_results[strategy] = strategy_results
        
        # Print strategy summary
        issue_rate = (models_with_issues / max(1, total_models)) * 100
        print(f"  Models: {total_models}, Issues: {models_with_issues} ({issue_rate:.1f}%)")
        print(f"  FP: {total_false_premises}, TC: {total_true_conclusions}, "
              f"Runtime: {total_runtime / max(1, total_models):.3f}s avg")
    
    # Analysis and comparison
    print(f"\n{'='*80}")
    print("STRATEGY COMPARISON")
    print(f"{'='*80}")
    
    print(f"{'Strategy':<10} {'Models':<8} {'Issues':<8} {'FP':<6} {'TC':<6} {'Total':<7} {'Rate%':<7} {'Time':<7}")
    print("-"*65)
    
    for strategy in strategies:
        stats = strategy_summaries[strategy]
        total_issues = stats['total_false_premises'] + stats['total_true_conclusions']
        issue_rate = (stats['models_with_issues'] / max(1, stats['total_models'])) * 100
        
        print(f"{strategy:<10} {stats['total_models']:<8} {stats['models_with_issues']:<8} "
              f"{stats['total_false_premises']:<6} {stats['total_true_conclusions']:<6} "
              f"{total_issues:<7} {issue_rate:<7.1f} {stats['avg_runtime']:<7.3f}")
    
    # Rankings
    print(f"\n{'='*50}")
    print("RANKINGS")
    print(f"{'='*50}")
    
    # By total issues
    by_issues = sorted(strategies, key=lambda s: 
                      strategy_summaries[s]['total_false_premises'] + 
                      strategy_summaries[s]['total_true_conclusions'])
    print("By total issues (fewer is better):")
    for i, strategy in enumerate(by_issues, 1):
        stats = strategy_summaries[strategy]
        total = stats['total_false_premises'] + stats['total_true_conclusions']
        print(f"  {i}. {strategy}: {total} total issues")
    
    # By performance
    strategies_with_models = [s for s in strategies if strategy_summaries[s]['total_models'] > 0]
    by_speed = sorted(strategies_with_models, key=lambda s: strategy_summaries[s]['avg_runtime'])
    print("\nBy speed (faster is better):")
    for i, strategy in enumerate(by_speed, 1):
        stats = strategy_summaries[strategy]
        print(f"  {i}. {strategy}: {stats['avg_runtime']:.3f}s average")
    
    # Save results
    if save_results:
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f'exclusion_evaluation_{timestamp}.json'
        
        results_data = {
            'timestamp': datetime.now().isoformat(),
            'strategies_tested': strategies,
            'timeout_used': timeout,
            'total_examples': len(examples),
            'strategy_summaries': strategy_summaries,
            'detailed_results': all_results
        }
        
        with open(filename, 'w') as f:
            json.dump(results_data, f, indent=2)
        
        print(f"\nResults saved to: {filename}")
    
    return {
        'strategies': strategies,
        'summaries': strategy_summaries,
        'results': all_results,
        'examples': examples
    }


def compare_results(baseline_file, current_results):
    """Compare current results with a baseline to show improvements."""
    try:
        with open(baseline_file, 'r') as f:
            baseline = json.load(f)
        
        print(f"\n{'='*80}")
        print("IMPROVEMENT COMPARISON")
        print(f"{'='*80}")
        print(f"Baseline: {baseline.get('timestamp', 'Unknown')}")
        print(f"Current:  {datetime.now().isoformat()}")
        print()
        
        print(f"{'Strategy':<10} {'Baseline':<15} {'Current':<15} {'Change':<15} {'Status'}")
        print("-"*70)
        
        for strategy in current_results['summaries']:
            if strategy in baseline['strategy_summaries']:
                baseline_issues = (baseline['strategy_summaries'][strategy]['total_false_premises'] + 
                                 baseline['strategy_summaries'][strategy]['total_true_conclusions'])
                current_issues = (current_results['summaries'][strategy]['total_false_premises'] + 
                                current_results['summaries'][strategy]['total_true_conclusions'])
                
                change = current_issues - baseline_issues
                status = "IMPROVED" if change < 0 else "WORSE" if change > 0 else "SAME"
                change_str = f"{change:+d}" if change != 0 else "0"
                
                print(f"{strategy:<10} {baseline_issues:<15} {current_issues:<15} "
                      f"{change_str:<15} {status}")
        
    except FileNotFoundError:
        print(f"Baseline file {baseline_file} not found. Skipping comparison.")
    except Exception as e:
        print(f"Error comparing results: {e}")


def main():
    """Main function with command-line interface."""
    parser = argparse.ArgumentParser(description='Exclusion theory evaluation suite')
    parser.add_argument('--strategies', type=str, 
                       help='Comma-separated list of strategies (default: all)')
    parser.add_argument('--timeout', type=int, default=2,
                       help='Timeout per example in seconds (default: 2)')
    parser.add_argument('--baseline', type=str,
                       help='Baseline results file for comparison')
    parser.add_argument('--no-save', action='store_true',
                       help='Do not save results to file')
    
    args = parser.parse_args()
    
    strategies = None
    if args.strategies:
        strategies = [s.strip() for s in args.strategies.split(',')]
    
    results = run_evaluation(
        strategies=strategies,
        timeout=args.timeout,
        save_results=not args.no_save
    )
    
    if args.baseline:
        compare_results(args.baseline, results)
    
    return results


if __name__ == '__main__':
    main()