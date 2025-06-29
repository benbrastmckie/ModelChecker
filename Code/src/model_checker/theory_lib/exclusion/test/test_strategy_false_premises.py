"""Test different exclusion strategies for false premise issues.

This test runs problematic examples with different strategies to see
which ones produce countermodels with false premises.
"""

import unittest
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY, create_operator_collection
from model_checker import model, syntactic
import z3


class TestStrategyFalsePremises(unittest.TestCase):
    """Test different strategies for false premise issues."""
    
    def check_example_with_strategy(self, premise_str, conclusion_str, strategy_name, example_name):
        """Check if a strategy produces false premises for an example."""
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
            'expectation': False,
            'print_impossible': False,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'maximize': False,
        }
        
        # Create semantics with the specific strategy
        settings['exclusion_strategy'] = strategy_name
        semantics = ExclusionSemantics(settings)
        
        # Create operator collection for this strategy
        operators = create_operator_collection(strategy_name)
        
        # Create syntax parser
        syntax = syntactic.Syntax([premise_str], [conclusion_str], operators)
        
        # Create model constraints
        constraints = model.ModelConstraints(
            settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        # Create model structure
        structure = ExclusionStructure(constraints, settings)
        
        result = {
            'model_found': structure.z3_model is not None,
            'false_premise': False,
            'true_conclusion': False,
            'premise_verifiers': None,
            'conclusion_verifiers': None
        }
        
        if structure.z3_model:
            # Interpret sentences to create propositions
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            
            # Model was instantiated, so propositions exist
            premise = syntax.premises[0]
            conclusion = syntax.conclusions[0]
            main_point = structure.main_point
            
            # Debug: print when we find a model
            if strategy_name == "MS" and example_name == "Disjunctive DeMorgan's RL":
                print(f"\n    DEBUG: Found model for {example_name} with {strategy_name}")
            
            premise_prop = premise.proposition
            conclusion_prop = conclusion.proposition
            
            if premise_prop and conclusion_prop:
                premise_truth = premise_prop.truth_value_at(main_point)
                conclusion_truth = conclusion_prop.truth_value_at(main_point)
                
                result['premise_verifiers'] = premise_prop.verifiers
                result['conclusion_verifiers'] = conclusion_prop.verifiers
                result['false_premise'] = not premise_truth
                result['true_conclusion'] = conclusion_truth
                
                # Debug output for first example
                if example_name == "Disjunctive DeMorgan's RL" and strategy_name == "MS":
                    print(f"\n    DEBUG {example_name} with {strategy_name}:")
                    print(f"    Premise: {premise_str}")
                    print(f"    Premise verifiers: {premise_prop.verifiers}")
                    print(f"    Premise truth: {premise_truth}")
                    print(f"    Main world: {main_point['world']}")
                
        return result
    
    def test_all_strategies_on_problematic_examples(self):
        """Test all strategies on examples known to cause false premises."""
        
        # Examples that revealed false premise issues
        test_cases = [
            ("(\\exclude A \\uniwedge \\exclude B)", "\\exclude (A \\univee B)", "Disjunctive DeMorgan's RL"),
            ("\\exclude \\exclude \\exclude A", "\\exclude A", "Triple Negation"),
            ("(\\exclude A \\univee \\exclude B)", "\\exclude (A \\uniwedge B)", "Conjunctive DeMorgan's RL"),
        ]
        
        # Test each strategy
        strategies = ["QA", "QI2", "SK", "CD", "MS", "UF"]
        
        print("\n" + "="*80)
        print("Testing Exclusion Strategies for False Premises")
        print("="*80)
        
        results_summary = {}
        
        for strategy in strategies:
            print(f"\n--- Testing {strategy} Strategy ---")
            strategy_results = []
            
            for premise_str, conclusion_str, example_name in test_cases:
                result = self.check_example_with_strategy(
                    premise_str, conclusion_str, strategy, example_name
                )
                
                strategy_results.append((example_name, result))
                
                if result['model_found']:
                    status = []
                    if result['false_premise']:
                        status.append("FALSE PREMISE")
                    if result['true_conclusion']:
                        status.append("TRUE CONCLUSION")
                    
                    if status:
                        print(f"  {example_name}: ❌ {', '.join(status)}")
                        print(f"    Premise verifiers: {len(result['premise_verifiers']) if result['premise_verifiers'] else 'None'}")
                    else:
                        print(f"  {example_name}: ✓ Valid countermodel")
                else:
                    print(f"  {example_name}: No countermodel (correct - this is a valid inference)")
            
            # Count issues
            false_premises = sum(1 for _, r in strategy_results if r['false_premise'])
            true_conclusions = sum(1 for _, r in strategy_results if r['true_conclusion'])
            models_found = sum(1 for _, r in strategy_results if r['model_found'])
            
            results_summary[strategy] = {
                'models_found': models_found,
                'false_premises': false_premises,
                'true_conclusions': true_conclusions
            }
        
        # Print summary
        print("\n" + "="*80)
        print("SUMMARY")
        print("="*80)
        print(f"{'Strategy':<10} {'Models Found':<15} {'False Premises':<15} {'True Conclusions':<15}")
        print("-"*55)
        
        for strategy, stats in results_summary.items():
            print(f"{strategy:<10} {stats['models_found']:<15} {stats['false_premises']:<15} {stats['true_conclusions']:<15}")
        
        # Identify good strategies
        print("\nRecommended strategies (no false premises or true conclusions):")
        good_strategies = [s for s, stats in results_summary.items() 
                          if stats['false_premises'] == 0 and stats['true_conclusions'] == 0]
        if good_strategies:
            print("  " + ", ".join(good_strategies))
        else:
            print("  None - all strategies have issues!")


if __name__ == '__main__':
    # Run with minimal unittest output to see our custom output
    unittest.main(verbosity=0)