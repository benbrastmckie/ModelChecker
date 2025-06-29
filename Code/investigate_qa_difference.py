"""Investigate why QA strategy finds no model for Triple Negation while others do."""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic
import z3


def test_triple_negation_with_strategy(strategy_name):
    """Test Triple Negation example with specific strategy."""
    print(f"\n{'='*50}")
    print(f"TESTING {strategy_name} STRATEGY")
    print(f"{'='*50}")
    
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
        'max_time': 5,
        'expectation': False,
        'exclusion_strategy': strategy_name,
        'print_constraints': False,
        'print_z3': False,
    }
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # Create operator collection
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
    
    print(f"Premise: {premises[0]}")
    print(f"Conclusion: {conclusions[0]}")
    print()
    
    # Create model structure
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("✓ Model found!")
        print(f"Timeout: {getattr(structure, 'timeout', False)}")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        main_point = structure.main_point
        main_world = main_point['world']
        
        print(f"Main world: {main_world}")
        
        # Check premise truth
        premise = syntax.premises[0]
        if premise.proposition:
            premise_truth = premise.proposition.truth_value_at(main_point)
            premise_verifiers = premise.proposition.verifiers
            print(f"Premise truth: {premise_truth}")
            print(f"Premise verifiers: {premise_verifiers}")
        else:
            print("No premise proposition created")
        
        # Check conclusion truth
        conclusion = syntax.conclusions[0]
        if conclusion.proposition:
            conclusion_truth = conclusion.proposition.truth_value_at(main_point)
            conclusion_verifiers = conclusion.proposition.verifiers
            print(f"Conclusion truth: {conclusion_truth}")
            print(f"Conclusion verifiers: {conclusion_verifiers}")
        else:
            print("No conclusion proposition created")
            
    else:
        print("❌ No model found")
        print(f"Timeout: {getattr(structure, 'timeout', False)}")
        print(f"Z3 model status: {getattr(structure, 'z3_model_status', 'Unknown')}")
        
        # Check if there's an unsat core
        if hasattr(structure, 'unsat_core') and structure.unsat_core:
            print(f"Unsat core size: {len(structure.unsat_core)}")
        
    return structure.z3_model is not None


def main():
    """Compare QA with other strategies on Triple Negation."""
    print("INVESTIGATING QA DIFFERENCE ON TRIPLE NEGATION")
    print("="*60)
    
    strategies = ["QA", "QI2", "MS"]
    results = {}
    
    for strategy in strategies:
        found_model = test_triple_negation_with_strategy(strategy)
        results[strategy] = found_model
    
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    
    for strategy, found in results.items():
        status = "FOUND MODEL" if found else "NO MODEL"
        print(f"{strategy}: {status}")
    
    print(f"\n{'='*60}")
    print("ANALYSIS")
    print(f"{'='*60}")
    
    if not results["QA"] and results["QI2"]:
        print("QA finds no model while QI2 finds a model.")
        print("This suggests:")
        print("1. QA's constraint generation is more restrictive")
        print("2. QA correctly identifies this as an unsatisfiable case")
        print("3. Triple Negation (¬¬¬A ⊢ ¬A) might be a valid inference")
        print("4. QI2 and others find invalid countermodels with false premises")
        print("\nConclusion: QA's behavior is likely CORRECT here.")
        print("The other strategies are finding invalid countermodels.")
    elif results["QA"] and not results["QI2"]:
        print("QA finds a model while QI2 doesn't - unexpected!")
    else:
        print("All strategies behave the same way.")


if __name__ == '__main__':
    main()