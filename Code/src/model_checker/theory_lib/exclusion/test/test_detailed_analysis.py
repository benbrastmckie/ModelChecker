"""Detailed analysis of which specific examples cause false premises/true conclusions."""

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


def test_strategy_detailed(strategy_name, premises, conclusions, example_name):
    """Test strategy and return detailed breakdown."""
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 1,
        'expectation': False,
        'exclusion_strategy': strategy_name,
        'print_constraints': False,
        'print_z3': False,
    }
    
    try:
        with redirect_stdout(StringIO()):
            semantics = ExclusionSemantics(settings)
            operators = create_operator_collection(strategy_name)
            syntax = syntactic.Syntax(premises, conclusions, operators)
            constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
            structure = ExclusionStructure(constraints, settings)
        
        if structure.z3_model:
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            main_point = structure.main_point
            
            premise_results = []
            for i, premise in enumerate(syntax.premises):
                if premise.proposition:
                    truth = premise.proposition.truth_value_at(main_point)
                    premise_results.append((premises[i], truth))
            
            conclusion_results = []
            for i, conclusion in enumerate(syntax.conclusions):
                if conclusion.proposition:
                    truth = conclusion.proposition.truth_value_at(main_point)
                    conclusion_results.append((conclusions[i], truth))
            
            return {
                'model_found': True,
                'premise_results': premise_results,
                'conclusion_results': conclusion_results
            }
        else:
            return {'model_found': False}
    except:
        return {'model_found': False, 'error': True}


def main():
    """Detailed analysis of false premises and true conclusions by example."""
    
    test_cases = [
        (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
        (["\\exclude \\exclude \\exclude A"], ["\\exclude A"], "Triple Negation"), 
        (["(\\exclude A \\univee \\exclude B)"], ["\\exclude (A \\uniwedge B)"], "Conjunctive DeMorgan's RL"),
        (["A"], ["\\exclude \\exclude A"], "Double Negation Introduction"),
        (["\\exclude (A \\uniwedge B)"], ["(\\exclude A \\univee \\exclude B)"], "Conjunctive DeMorgan's LR"),
        (["\\exclude A"], ["A"], "Exclusion Contradiction"),
    ]
    
    strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
    
    print("="*100)
    print("DETAILED FALSE PREMISE AND TRUE CONCLUSION ANALYSIS")
    print("="*100)
    
    # Create detailed matrix
    results_matrix = {}
    
    for strategy in strategies:
        results_matrix[strategy] = {}
        for premises, conclusions, example_name in test_cases:
            result = test_strategy_detailed(strategy, premises, conclusions, example_name)
            results_matrix[strategy][example_name] = result
    
    # Print example-by-example analysis
    for premises, conclusions, example_name in test_cases:
        print(f"\n{'='*60}")
        print(f"EXAMPLE: {example_name}")
        print(f"{'='*60}")
        print(f"Premise: {premises[0]}")
        print(f"Conclusion: {conclusions[0]}")
        print()
        
        print(f"{'Strategy':<10} {'Model':<8} {'Premise Truth':<15} {'Conclusion Truth':<17} {'Issues'}")
        print("-"*70)
        
        for strategy in strategies:
            result = results_matrix[strategy][example_name]
            
            if not result['model_found']:
                print(f"{strategy:<10} {'No':<8} {'-':<15} {'-':<17} {'None'}")
                continue
            
            premise_truth = result['premise_results'][0][1] if result['premise_results'] else None
            conclusion_truth = result['conclusion_results'][0][1] if result['conclusion_results'] else None
            
            issues = []
            if premise_truth is False:
                issues.append("FALSE PREMISE")
            if conclusion_truth is True:
                issues.append("TRUE CONCLUSION")
            
            issue_str = ", ".join(issues) if issues else "None"
            
            print(f"{strategy:<10} {'Yes':<8} {str(premise_truth):<15} {str(conclusion_truth):<17} {issue_str}")
    
    # Summary by strategy
    print(f"\n{'='*100}")
    print("STRATEGY SUMMARY")
    print(f"{'='*100}")
    
    strategy_stats = {}
    for strategy in strategies:
        fp_count = 0
        tc_count = 0
        model_count = 0
        fp_examples = []
        tc_examples = []
        
        for premises, conclusions, example_name in test_cases:
            result = results_matrix[strategy][example_name]
            if result['model_found']:
                model_count += 1
                
                if result['premise_results']:
                    premise_truth = result['premise_results'][0][1]
                    if premise_truth is False:
                        fp_count += 1
                        fp_examples.append(example_name)
                
                if result['conclusion_results']:
                    conclusion_truth = result['conclusion_results'][0][1] 
                    if conclusion_truth is True:
                        tc_count += 1
                        tc_examples.append(example_name)
        
        strategy_stats[strategy] = {
            'models': model_count,
            'false_premises': fp_count,
            'true_conclusions': tc_count,
            'fp_examples': fp_examples,
            'tc_examples': tc_examples
        }
    
    print(f"{'Strategy':<10} {'Models':<8} {'False Premises':<15} {'True Conclusions':<17} {'Total Issues'}")
    print("-"*65)
    
    for strategy in strategies:
        stats = strategy_stats[strategy]
        total_issues = stats['false_premises'] + stats['true_conclusions']
        print(f"{strategy:<10} {stats['models']:<8} {stats['false_premises']:<15} "
              f"{stats['true_conclusions']:<17} {total_issues}")
    
    # Most problematic examples
    print(f"\n{'='*100}")
    print("MOST PROBLEMATIC EXAMPLES")
    print(f"{'='*100}")
    
    example_issues = {}
    for premises, conclusions, example_name in test_cases:
        total_issues = 0
        for strategy in strategies:
            result = results_matrix[strategy][example_name]
            if result['model_found']:
                if result['premise_results'] and result['premise_results'][0][1] is False:
                    total_issues += 1
                if result['conclusion_results'] and result['conclusion_results'][0][1] is True:
                    total_issues += 1
        example_issues[example_name] = total_issues
    
    sorted_examples = sorted(example_issues.items(), key=lambda x: x[1], reverse=True)
    
    print("Examples ranked by number of strategies that have issues with them:")
    for example_name, issue_count in sorted_examples:
        print(f"  {example_name}: {issue_count} strategy issues")
    
    # Best strategies
    print(f"\n{'='*100}")
    print("STRATEGY RANKING")
    print(f"{'='*100}")
    
    # Sort by total issues
    sorted_strategies = sorted(strategies, 
                              key=lambda s: strategy_stats[s]['false_premises'] + 
                                           strategy_stats[s]['true_conclusions'])
    
    print("Strategies ranked by total issues (best to worst):")
    for i, strategy in enumerate(sorted_strategies, 1):
        stats = strategy_stats[strategy]
        total_issues = stats['false_premises'] + stats['true_conclusions']
        print(f"  {i}. {strategy}: {total_issues} total issues "
              f"({stats['false_premises']} FP, {stats['true_conclusions']} TC) "
              f"in {stats['models']} models")


if __name__ == '__main__':
    main()