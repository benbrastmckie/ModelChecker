"""Baseline comparison tool for tracking improvements to exclusion theories.

This tool helps track changes in false premise/true conclusion rates
when making improvements to the exclusion theory implementation.
"""

import sys
import os
import json
import argparse
from datetime import datetime

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))


def load_results(filename):
    """Load results from a JSON file."""
    with open(filename, 'r') as f:
        return json.load(f)


def compare_two_results(baseline_file, current_file):
    """Compare two result files."""
    baseline = load_results(baseline_file)
    current = load_results(current_file)
    
    print("="*80)
    print("DETAILED COMPARISON REPORT")
    print("="*80)
    print(f"Baseline: {baseline.get('timestamp', 'Unknown')} ({baseline_file})")
    print(f"Current:  {current.get('timestamp', 'Unknown')} ({current_file})")
    print()
    
    # Overall comparison
    print("OVERALL STRATEGY COMPARISON")
    print("-"*50)
    print(f"{'Strategy':<10} {'Baseline Issues':<15} {'Current Issues':<15} {'Change':<10} {'%Change':<10}")
    print("-"*60)
    
    total_baseline_issues = 0
    total_current_issues = 0
    improvements = 0
    
    for strategy in baseline['strategy_summaries']:
        if strategy in current['strategy_summaries']:
            baseline_issues = (baseline['strategy_summaries'][strategy]['total_false_premises'] + 
                             baseline['strategy_summaries'][strategy]['total_true_conclusions'])
            current_issues = (current['strategy_summaries'][strategy]['total_false_premises'] + 
                            current['strategy_summaries'][strategy]['total_true_conclusions'])
            
            change = current_issues - baseline_issues
            pct_change = (change / max(1, baseline_issues)) * 100
            
            total_baseline_issues += baseline_issues
            total_current_issues += current_issues
            
            if change < 0:
                improvements += 1
            
            print(f"{strategy:<10} {baseline_issues:<15} {current_issues:<15} "
                  f"{change:+d}:<10} {pct_change:+.1f}%")
    
    print("-"*60)
    total_change = total_current_issues - total_baseline_issues
    total_pct = (total_change / max(1, total_baseline_issues)) * 100
    print(f"{'TOTAL':<10} {total_baseline_issues:<15} {total_current_issues:<15} "
          f"{total_change:+d}:<10} {total_pct:+.1f}%")
    
    print(f"\nStrategies improved: {improvements}/{len(baseline['strategy_summaries'])}")
    
    # Performance comparison
    print(f"\n{'='*60}")
    print("PERFORMANCE COMPARISON")
    print("-"*40)
    print(f"{'Strategy':<10} {'Baseline Time':<15} {'Current Time':<15} {'Change':<10}")
    print("-"*50)
    
    for strategy in baseline['strategy_summaries']:
        if strategy in current['strategy_summaries']:
            baseline_time = baseline['strategy_summaries'][strategy]['avg_runtime']
            current_time = current['strategy_summaries'][strategy]['avg_runtime']
            change = current_time - baseline_time
            
            print(f"{strategy:<10} {baseline_time:<15.3f} {current_time:<15.3f} {change:+.3f}")
    
    # Example-specific analysis
    print(f"\n{'='*60}")
    print("EXAMPLES WITH BIGGEST CHANGES")
    print("-"*40)
    
    example_changes = {}
    baseline_results = baseline.get('detailed_results', {})
    current_results = current.get('detailed_results', {})
    
    for strategy in baseline_results:
        if strategy in current_results:
            for example in baseline_results[strategy]:
                if example in current_results[strategy]:
                    baseline_ex = baseline_results[strategy][example]
                    current_ex = current_results[strategy][example]
                    
                    if baseline_ex.get('model_found', False) and current_ex.get('model_found', False):
                        baseline_issues = (baseline_ex.get('false_premise_count', 0) + 
                                         baseline_ex.get('true_conclusion_count', 0))
                        current_issues = (current_ex.get('false_premise_count', 0) + 
                                        current_ex.get('true_conclusion_count', 0))
                        
                        change = current_issues - baseline_issues
                        if example not in example_changes:
                            example_changes[example] = []
                        example_changes[example].append((strategy, change))
    
    # Show examples with most improvement/regression
    example_totals = {}
    for example, changes in example_changes.items():
        total_change = sum(change for _, change in changes)
        example_totals[example] = total_change
    
    # Most improved
    most_improved = sorted(example_totals.items(), key=lambda x: x[1])[:5]
    if most_improved and most_improved[0][1] < 0:
        print("Most improved examples:")
        for example, change in most_improved:
            if change < 0:
                print(f"  {example}: {change} total issue reduction")
    
    # Most regressed
    most_regressed = sorted(example_totals.items(), key=lambda x: x[1], reverse=True)[:5]
    if most_regressed and most_regressed[0][1] > 0:
        print("\nMost regressed examples:")
        for example, change in most_regressed:
            if change > 0:
                print(f"  {example}: +{change} total issue increase")


def create_baseline(results_file, baseline_name=None):
    """Create a baseline from current results."""
    if baseline_name is None:
        baseline_name = f"baseline_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    
    # Simply copy the results file to create baseline
    import shutil
    shutil.copy2(results_file, baseline_name)
    
    print(f"Baseline created: {baseline_name}")
    return baseline_name


def main():
    """Main function."""
    parser = argparse.ArgumentParser(description='Compare exclusion theory evaluation results')
    parser.add_argument('baseline', help='Baseline results file')
    parser.add_argument('current', help='Current results file')
    parser.add_argument('--create-baseline', help='Create baseline from current results')
    
    args = parser.parse_args()
    
    if args.create_baseline:
        create_baseline(args.current, args.create_baseline)
    else:
        compare_two_results(args.baseline, args.current)


if __name__ == '__main__':
    main()