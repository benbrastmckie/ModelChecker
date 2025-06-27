#!/usr/bin/env python3
"""
Debug why SK2's true_at method isn't fixing the false premise issue.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import ModelConstraints

def debug_triple_negation():
    """Debug the triple negation example step by step."""
    print("DEBUGGING SK2 TRUE_AT")
    print("="*60)
    
    # Settings for triple negation
    premises = ['\\exclude \\exclude \\exclude A']
    conclusions = ['\\exclude A']
    settings = {
        'N': 3,
        'contingent': ['A'],
        'possible': [],
        'necessary': [],
        'disjoint_set': [],
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'fusion_closure': False,
        'print_constraints': False,
        'expectation': 'CEX',
        'max_time': 5
    }
    
    # Create SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax and semantics
    syntax = Syntax(premises, conclusions, sk2_operators)
    semantics = ExclusionSemantics(settings)
    
    # Create constraints and structure
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    structure = ExclusionStructure(constraints, settings)
    
    print(f"Model found: {structure.z3_model is not None}")
    print(f"Z3 status: {structure.z3_model_status}")
    
    if structure.z3_model:
        # Interpret sentences
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        # Get the premise
        premise_sent = syntax.premises[0]
        
        # Debug the operator chain
        print("\nDEBUGGING OPERATOR CHAIN:")
        print("-"*40)
        
        # The premise is \\exclude \\exclude \\exclude A
        # Let's trace through each level
        
        # Level 1: A (atomic)
        A = syntax.sentence_letters[0]
        print(f"A (atomic): {A.name}")
        
        # Level 2: \\exclude A
        # This should be an argument of the next level
        if premise_sent.operator:
            outer_op = premise_sent.operator
            print(f"Outermost operator: {type(outer_op).__name__}")
            
            # Check if it's using SK2
            if hasattr(outer_op, 'true_at'):
                print(f"Has true_at method: Yes")
                
                # Try to evaluate manually
                eval_point = {"world": semantics.main_world}
                
                # Get the formula that would be used
                print("\nTesting formula generation:")
                try:
                    # The outermost exclusion's argument is \\exclude \\exclude A
                    inner_arg = premise_sent.arguments[0]
                    print(f"Inner argument: {inner_arg.name}")
                    
                    # Generate the true_at formula
                    true_formula = outer_op.true_at(inner_arg, eval_point)
                    print(f"True_at formula type: {type(true_formula)}")
                    print(f"Contains 'h_sk2_true': {'h_sk2_true' in str(true_formula)}")
                    print(f"Contains existential: {z3.is_exists(true_formula)}")
                    
                except Exception as e:
                    print(f"Error generating formula: {e}")
        
        # Now check the actual evaluation
        print("\nACTUAL EVALUATION:")
        print("-"*40)
        
        if premise_sent.proposition:
            eval_point = {"world": semantics.main_world}
            
            # Check what method is actually called
            print("Tracing truth_value_at call...")
            
            # Get the proposition
            prop = premise_sent.proposition
            print(f"Proposition type: {type(prop).__name__}")
            
            # Check the sentence structure
            print(f"Sentence operator: {prop.sentence.operator.name if prop.sentence.operator else 'None'}")
            print(f"Sentence has true_at: {hasattr(prop.sentence.operator, 'true_at') if prop.sentence.operator else False}")
            
            # Manual evaluation
            formula = semantics.true_at(prop.sentence, eval_point)
            result = structure.z3_model.evaluate(formula)
            print(f"Manual evaluation result: {z3.is_true(result)}")
            
            # Check if the formula contains our Skolem functions
            formula_str = str(formula)
            print(f"\nFormula analysis:")
            print(f"  Contains 'h_sk2_true': {'h_sk2_true' in formula_str}")
            print(f"  Contains 'h_sk2_': {'h_sk2_' in formula_str}")
            print(f"  Contains 'Exists': {'Exists' in formula_str}")
            print(f"  Formula length: {len(formula_str)}")

if __name__ == "__main__":
    debug_triple_negation()