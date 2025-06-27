#!/usr/bin/env python3
"""
Test a different approach: modify evaluation to not create new Skolem functions.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

def test_evaluation_approach():
    """Test by checking what happens if we evaluate differently."""
    print("TESTING ALTERNATIVE EVALUATION APPROACH")
    print("="*60)
    
    premises, conclusions, settings = TN_ENTAIL_example
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    # Create constraints
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    # Create structure
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("Model found!")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        
        # Get the premise
        premise = syntax.premises[0]
        
        if premise.proposition:
            eval_point = {"world": semantics.main_world}
            
            # Standard evaluation
            standard_result = premise.proposition.truth_value_at(eval_point)
            print(f"\nStandard evaluation: {standard_result}")
            
            # Now let's try a different approach
            # Instead of evaluating the formula with new Skolem functions,
            # let's check if the premise constraint is satisfied
            
            print("\nAlternative approach - check constraint satisfaction:")
            
            # The premise constraint should already be in the model
            premise_constraint = constraints.premise_constraints[0]
            constraint_result = structure.z3_model.evaluate(premise_constraint)
            print(f"Premise constraint satisfied: {z3.is_true(constraint_result)}")
            
            # This should be True because the model was found by satisfying this constraint!
            
            # The issue is that truth_value_at creates a DIFFERENT formula than the constraint
            
            print("\nAnalyzing the formulas:")
            print("-"*40)
            
            # Get the constraint formula
            constraint_str = str(premise_constraint)
            print(f"Constraint formula length: {len(constraint_str)}")
            print(f"Contains f_atom: {'f_atom' in constraint_str}")
            
            # Get the evaluation formula
            eval_formula = semantics.true_at(premise, eval_point)
            eval_str = str(eval_formula)
            print(f"\nEvaluation formula length: {len(eval_str)}")
            print(f"Contains f_atom: {'f_atom' in eval_str}")
            
            # They should be the same, but they're not!
            print(f"\nFormulas are identical: {constraint_str == eval_str}")
            
            # The root issue: premise_behavior creates one formula,
            # but truth_value_at creates a different one

if __name__ == "__main__":
    test_evaluation_approach()