#!/usr/bin/env python3
"""
Quick script to analyze strategy results and generate comparison data.
"""

import json
import glob
import os

def analyze_strategy_results():
    """Analyze all available strategy result files."""
    
    strategy_files = glob.glob("strategy_results_*.json")
    
    if not strategy_files:
        print("No strategy result files found.")
        return
    
    print("=== STRATEGY COMPARISON ANALYSIS ===")
    print(f"{'Strategy':<8} {'Success':<8} {'Invalid':<8} {'Avg Time':<10} {'Reliability':<12}")
    print("-" * 58)
    
    strategy_data = {}
    
    for file_path in strategy_files:
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            
            strategy_name = data['strategy']
            summary = data['summary']
            
            success_rate = summary['success_rate']
            invalid_rate = summary['invalid_rate']
            avg_time = summary['avg_solving_time']
            reliability = (1 - invalid_rate) if success_rate > 0 else 0
            
            strategy_data[strategy_name] = {
                'success_rate': success_rate,
                'invalid_rate': invalid_rate,
                'avg_time': avg_time,
                'reliability': reliability,
                'successful_models': summary['successful_models'],
                'invalid_countermodels': summary['invalid_countermodels']
            }
            
            print(f"{strategy_name:<8} {success_rate:<8.1%} {invalid_rate:<8.1%} {avg_time:<10.3f} {reliability:<12.1%}")
            
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
    
    # Find best performing strategies
    if strategy_data:
        best_reliability = max(data['reliability'] for data in strategy_data.values() if data['success_rate'] > 0)
        best_strategies = [name for name, data in strategy_data.items() 
                          if data['success_rate'] > 0 and data['reliability'] == best_reliability]
        
        print(f"\nBest reliability strategies: {', '.join(best_strategies)} ({best_reliability:.1%} valid countermodels)")
        
        # Additional analysis
        print(f"\n=== DETAILED ANALYSIS ===")
        for strategy_name, data in sorted(strategy_data.items()):
            print(f"\n{strategy_name}:")
            print(f"  Models found: {data['successful_models']}/32 ({data['success_rate']:.1%})")
            print(f"  Invalid models: {data['invalid_countermodels']} ({data['invalid_rate']:.1%})")
            print(f"  Valid models: {data['successful_models'] - data['invalid_countermodels']}")
            print(f"  Average time: {data['avg_time']:.3f}s")
            print(f"  Reliability: {data['reliability']:.1%}")
    
    return strategy_data

if __name__ == "__main__":
    strategy_data = analyze_strategy_results()