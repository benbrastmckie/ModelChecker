#!/usr/bin/env python3
"""
Simple test of SK2 strategy on the Triple Negation example.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.builder import BuildModule
from model_checker.theory_lib import exclusion

def test_example_with_strategy(strategy_name, example_name, example_data):
    """Test a single example with a specific strategy."""
    print(f"\n{'='*60}")
    print(f"Testing {example_name} with {strategy_name} strategy")
    print(f"{'='*60}")
    
    # Create a module with custom settings
    module = exclusion
    
    # Override the default strategy
    from model_checker.theory_lib.exclusion import operators
    original_default = operators.DEFAULT_STRATEGY
    operators.DEFAULT_STRATEGY = strategy_name
    
    try:
        # Create build module
        build_module = BuildModule(module)
        
        # Set up the example
        build_module.example_range = {example_name: example_data}
        
        # Build examples
        results = build_module.build_examples()
        
        if results:
            print(f"\nResults processed successfully")
        
    finally:
        # Restore original default
        operators.DEFAULT_STRATEGY = original_default

def main():
    """Test SK2 on key problematic examples."""
    
    # Triple Negation Entailment
    tn_example = [
        ['\\exclude \\exclude \\exclude A'],  # premises
        ['\\exclude A'],                       # conclusions
        {'N': 3, 'max_time': 10}              # settings
    ]
    
    # Test with SK2
    test_example_with_strategy("SK2", "Triple Negation Entailment", tn_example)
    
    # Test with MS for comparison
    test_example_with_strategy("MS", "Triple Negation Entailment", tn_example)
    
    # Disjunctive DeMorgan's RL
    dm_example = [
        ['(\\exclude A \\uniwedge \\exclude B)'],
        ['\\exclude (A \\univee B)'],
        {'N': 3, 'max_time': 10}
    ]
    
    test_example_with_strategy("SK2", "Disjunctive DeMorgan's RL", dm_example)
    test_example_with_strategy("MS", "Disjunctive DeMorgan's RL", dm_example)

if __name__ == "__main__":
    main()