"""Test timeout hypothesis for QA strategy on Triple Negation."""

import sys
import time
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic


def test_with_timeout(strategy_name, timeout):
    """Test Triple Negation with specific timeout."""
    premises = ["\\exclude \\exclude \\exclude A"]
    conclusions = ["\\exclude A"]
    
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': timeout,
        'expectation': False,
        'exclusion_strategy': strategy_name,
        'print_constraints': False,
        'print_z3': False,
    }
    
    start_time = time.time()
    
    try:
        semantics = ExclusionSemantics(settings)
        operators = create_operator_collection(strategy_name)
        syntax = syntactic.Syntax(premises, conclusions, operators)
        constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
        structure = ExclusionStructure(constraints, settings)
        
        runtime = time.time() - start_time
        
        return {
            'model_found': structure.z3_model is not None,
            'timeout': getattr(structure, 'timeout', False),
            'runtime': runtime
        }
    except Exception as e:
        runtime = time.time() - start_time
        return {
            'model_found': False,
            'timeout': True,
            'runtime': runtime,
            'error': str(e)
        }


def main():
    """Test timeout hypothesis."""
    print("TESTING TIMEOUT HYPOTHESIS: QA vs Other Strategies")
    print("="*60)
    
    strategies = ["QA", "QI2", "MS"]
    timeouts = [0.5, 1.0, 2.0, 5.0]
    
    print(f"{'Strategy':<10} {'Timeout':<8} {'Model':<8} {'Timeout?':<9} {'Runtime':<10}")
    print("-"*55)
    
    for strategy in strategies:
        for timeout in timeouts:
            result = test_with_timeout(strategy, timeout)
            
            model_status = "YES" if result['model_found'] else "NO"
            timeout_status = "YES" if result['timeout'] else "NO"
            
            print(f"{strategy:<10} {timeout:<8.1f} {model_status:<8} {timeout_status:<9} {result['runtime']:<10.3f}")
    
    print(f"\n{'='*60}")
    print("ANALYSIS")
    print(f"{'='*60}")
    
    # Test specifically with 1s timeout (like detailed_analysis.py)
    print("Testing with 1-second timeout (same as detailed_analysis.py):")
    
    for strategy in strategies:
        result = test_with_timeout(strategy, 1.0)
        status = "FOUND MODEL" if result['model_found'] else "NO MODEL"
        timeout_info = "(TIMEOUT)" if result['timeout'] else "(SOLVED)"
        print(f"  {strategy}: {status} {timeout_info} in {result['runtime']:.3f}s")
    
    print("\nConclusion:")
    print("If QA shows 'NO MODEL (TIMEOUT)' while others show 'FOUND MODEL (SOLVED)',")
    print("then QA simply needs more time to solve this particular example.")


if __name__ == '__main__':
    main()