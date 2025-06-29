"""Quick test for evaluating specific strategies on key examples.

This is useful for rapid iteration when making theory improvements.
"""

import sys
import os
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


def quick_test(strategies=None, examples=None):
    """Quick test of key examples on specified strategies."""
    
    if strategies is None:
        strategies = ["QA", "CD", "MS"]  # Most important ones
    
    if examples is None:
        # Key problematic examples
        examples = [
            (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
            (["\\exclude \\exclude \\exclude A"], ["\\exclude A"], "Triple Negation"),
            (["(\\exclude A \\univee \\exclude B)"], ["\\exclude (A \\uniwedge B)"], "Conjunctive DeMorgan's RL"),
            (["A"], ["\\exclude \\exclude A"], "Double Negation Introduction"),
            (["\\exclude A"], ["A"], "Exclusion Contradiction"),
        ]
    
    print("="*60)
    print("QUICK STRATEGY TEST")
    print("="*60)
    print(f"Testing {len(strategies)} strategies on {len(examples)} key examples\n")
    
    results = {}
    
    for strategy in strategies:
        print(f"Testing {strategy}:")
        strategy_results = {}
        total_fp = 0
        total_tc = 0
        models_found = 0
        
        for premises, conclusions, example_name in examples:
            settings = {
                'N': 3,
                'possible': False,
                'contingent': False,
                'non_empty': False,
                'non_null': False,
                'disjoint': False,
                'fusion_closure': False,
                'max_time': 1,
                'exclusion_strategy': strategy,
                'print_constraints': False,
                'print_z3': False,
            }
            
            try:
                with redirect_stdout(StringIO()):
                    semantics = ExclusionSemantics(settings)
                    operators = create_operator_collection(strategy)
                    syntax = syntactic.Syntax(premises, conclusions, operators)
                    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
                    structure = ExclusionStructure(constraints, settings)
                
                if structure.z3_model:
                    structure.interpret(syntax.premises)
                    structure.interpret(syntax.conclusions)
                    main_point = structure.main_point
                    
                    models_found += 1
                    fp = sum(1 for p in syntax.premises 
                            if p.proposition and not p.proposition.truth_value_at(main_point))
                    tc = sum(1 for c in syntax.conclusions 
                            if c.proposition and c.proposition.truth_value_at(main_point))
                    
                    total_fp += fp
                    total_tc += tc
                    
                    issues = []
                    if fp > 0:
                        issues.append(f"FP:{fp}")
                    if tc > 0:
                        issues.append(f"TC:{tc}")
                    
                    issue_str = " [" + ", ".join(issues) + "]" if issues else ""
                    print(f"  ✓ {example_name}: Model{issue_str}")
                    
                    strategy_results[example_name] = {'fp': fp, 'tc': tc, 'model': True}
                else:
                    print(f"  - {example_name}: No model")
                    strategy_results[example_name] = {'fp': 0, 'tc': 0, 'model': False}
            
            except Exception as e:
                print(f"  ⚠ {example_name}: Error - {str(e)[:50]}...")
                strategy_results[example_name] = {'fp': 0, 'tc': 0, 'model': False, 'error': True}
        
        total_issues = total_fp + total_tc
        print(f"  Summary: {models_found} models, {total_issues} total issues ({total_fp} FP + {total_tc} TC)\n")
        
        results[strategy] = {
            'models_found': models_found,
            'total_fp': total_fp,
            'total_tc': total_tc,
            'total_issues': total_issues,
            'examples': strategy_results
        }
    
    # Quick comparison
    print("="*60)
    print("QUICK COMPARISON")
    print("="*60)
    print(f"{'Strategy':<10} {'Models':<8} {'FP':<6} {'TC':<6} {'Total':<7}")
    print("-"*40)
    
    for strategy in strategies:
        stats = results[strategy]
        print(f"{strategy:<10} {stats['models_found']:<8} {stats['total_fp']:<6} "
              f"{stats['total_tc']:<6} {stats['total_issues']:<7}")
    
    # Best performer
    best_strategy = min(strategies, key=lambda s: results[s]['total_issues'])
    print(f"\nBest performer: {best_strategy} ({results[best_strategy]['total_issues']} total issues)")
    
    return results


if __name__ == '__main__':
    quick_test()