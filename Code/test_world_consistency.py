#!/usr/bin/env python3
"""
Test if the main_world value is consistent between constraint and evaluation.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

def test_world_consistency():
    """Check if main_world is consistent."""
    print("TESTING WORLD CONSISTENCY")
    print("="*60)
    
    premises, conclusions, settings = TN_ENTAIL_example
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    print(f"Initial main_world: {semantics.main_world}")
    print(f"Initial main_point: {semantics.main_point}")
    
    # SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    # Create constraints
    print("\nDuring constraint generation:")
    print(f"  main_world used: {semantics.main_world}")
    
    # Trace premise_behavior
    premise = syntax.premises[0]
    premise_formula = semantics.premise_behavior(premise)
    print(f"  Premise formula created")
    
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    # Create structure
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("\nAfter model generation:")
        
        # Get the actual main_world value from the model
        main_world_val = structure.z3_model.eval(semantics.main_world)
        print(f"  main_world value in model: {main_world_val}")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        
        # During evaluation
        print("\nDuring evaluation:")
        premise_sent = syntax.premises[0]
        
        if premise_sent.proposition:
            # Check what eval_point is used
            prop = premise_sent.proposition
            print(f"  Proposition eval_point: {prop.eval_point}")
            
            # The eval_point for evaluation
            eval_point_for_eval = {"world": semantics.main_world}
            print(f"  Evaluation eval_point: {eval_point_for_eval}")
            
            # Are they the same Z3 object?
            print(f"  Same Z3 object: {eval_point_for_eval['world'] is semantics.main_world}")
            
            # Check if the values match
            eval_world_val = structure.z3_model.eval(eval_point_for_eval['world'])
            print(f"  Eval world value: {eval_world_val}")
            print(f"  Values match: {main_world_val == eval_world_val}")

if __name__ == "__main__":
    test_world_consistency()