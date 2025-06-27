#!/usr/bin/env python3
"""
Debug SK2 constraint generation to understand why it still has false premises.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition
from model_checker.theory_lib.exclusion.operators import (
    ExclusionOperatorMultiSort,
    ExclusionOperatorSkolemized2,
    create_operator_collection
)
from model_checker import ModelConstraints
from model_checker.builder import BuildExample

def analyze_sk2_behavior():
    """Analyze SK2's actual behavior in constraint generation."""
    print("SK2 CONSTRAINT ANALYSIS")
    print("="*60)
    
    # Simple test: ∼∼∼A ⊢ ∼A
    premises = ['\\exclude \\exclude \\exclude A']
    conclusions = ['\\exclude A']
    settings = {
        'N': 3, 
        'contingent': ['A'], 
        'possible': [],
        'necessary': [],
        'disjoint_set': [],
        'print_constraints': False,
        'expectation': 'CEX', 
        'max_time': 5
    }
    
    # Test with SK2
    print("\n1. Testing SK2 Strategy:")
    print("-"*40)
    
    # Create operator collection
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # Create model constraints
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    # Examine the constraint structure
    print(f"Number of premises: {len(syntax.premises)}")
    print(f"Number of conclusions: {len(syntax.conclusions)}")
    print(f"Number of sentence letters: {len(syntax.sentence_letters)}")
    
    # Get the exclusion operator
    exclude_op = sk2_operators.registry.get('\\exclude')
    print(f"\nExclusion operator type: {type(exclude_op).__name__}")
    
    # Test the extended_verify method directly
    state = z3.BitVec("test_state", 3)
    eval_point = {"world": z3.BitVecVal(0, 3)}
    
    # Get the innermost A
    A = syntax.sentence_letters[0]
    
    # Build up the triple negation manually
    print("\nBuilding formula step by step:")
    
    # First exclusion: ∼A
    print("Step 1: Creating ∼A")
    neg_A_formula = exclude_op.extended_verify(state, A, eval_point)
    print(f"  Formula contains 'Exists': {'Exists' in str(neg_A_formula)}")
    print(f"  Formula contains 'h_sk2': {'h_sk2' in str(neg_A_formula)}")
    print(f"  Formula contains 'y_sk2': {'y_sk2' in str(neg_A_formula)}")
    
    # Check if we're using the actual ForAll/Exists from utils
    print("\nChecking quantifier expansion:")
    from model_checker.utils import ForAll, Exists
    
    # Create a simple test formula
    test_x = z3.BitVec("test_x", 3)
    test_formula = ForAll(test_x, test_x == test_x)
    print(f"ForAll test formula type: {type(test_formula)}")
    print(f"ForAll expands to And: {z3.is_and(test_formula)}")
    
    # Now let's trace through the actual constraint generation
    print("\n2. Tracing Constraint Generation:")
    print("-"*40)
    
    # Use BuildExample to see the full process
    example = BuildExample(
        premises=premises,
        conclusions=conclusions,
        settings=settings,
        semantic_class=ExclusionSemantics,
        proposition_class=UnilateralProposition,
        model_structure=None,  # Will use default
        operator_collection=sk2_operators,
        syntax_class=Syntax,
        verbose=True
    )
    
    # Run with verbosity
    result = example.check_debugger()
    
    if result['z3_model']:
        print("\nModel found!")
        model = result['z3_model']
        
        # Extract values
        main_world = model.eval(z3.BitVec('main_world', 3))
        print(f"Main world: {main_world}")
        
        # Check premise evaluation
        if result['syntax'].premises[0].proposition:
            premise_value = result['syntax'].premises[0].proposition.truth_value_at(eval_point)
            print(f"Premise evaluation: {premise_value}")
            
            # If false, try to understand why
            if not premise_value:
                print("\nFALSE PREMISE DETECTED - Investigating...")
                
                # Look for function witnesses
                for decl in model.decls():
                    if 'h_sk2' in str(decl) or 'y_sk2' in str(decl):
                        print(f"  Found function: {decl}")
                        # Try to get function interpretation
                        func_interp = model[decl]
                        print(f"    Interpretation: {func_interp}")

if __name__ == "__main__":
    analyze_sk2_behavior()