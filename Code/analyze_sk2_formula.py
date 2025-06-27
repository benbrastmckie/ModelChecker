#!/usr/bin/env python3
"""
Analyze the actual SK2 formula structure to understand why it still evaluates to false.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection, ExclusionOperatorSkolemized2
from model_checker import ModelConstraints

def analyze_formula_structure():
    """Analyze the SK2 formula in detail."""
    print("SK2 FORMULA STRUCTURE ANALYSIS")
    print("="*60)
    
    # Simple test: \\exclude A
    premises = ['\\exclude A']
    conclusions = []
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
    
    # Create operators and semantics
    sk2_operators = create_operator_collection("SK2")
    semantics = ExclusionSemantics(settings)
    
    # Get the exclusion operator
    exclude_op = sk2_operators['\\exclude']
    print(f"Exclusion operator type: {type(exclude_op).__name__}")
    
    # Create a simple test
    syntax = Syntax(['A'], [], sk2_operators)
    A = syntax.sentence_letters[0]
    
    # Test true_at directly
    eval_point = {"world": z3.BitVecVal(0, 3)}
    
    print("\n1. Testing true_at method:")
    print("-"*40)
    
    # Create an instance of the operator
    op_instance = ExclusionOperatorSkolemized2(semantics)
    
    # Generate the true_at formula
    true_formula = op_instance.true_at(A, eval_point)
    
    print(f"Formula type: {type(true_formula)}")
    
    # Check for quantifiers
    def count_quantifiers(expr, depth=0):
        """Recursively count quantifiers in a Z3 expression."""
        indent = "  " * depth
        if z3.is_quantifier(expr):
            if expr.is_forall():
                print(f"{indent}ForAll at depth {depth}")
                count_quantifiers(expr.body(), depth + 1)
                return 1 + count_quantifiers(expr.body(), 0)
            elif expr.is_exists():
                print(f"{indent}EXISTS at depth {depth}")
                count_quantifiers(expr.body(), depth + 1)
                return 1 + count_quantifiers(expr.body(), 0)
        elif z3.is_and(expr) or z3.is_or(expr) or z3.is_implies(expr):
            total = 0
            for child in expr.children():
                total += count_quantifiers(child, depth)
            return total
        return 0
    
    print("\nQuantifier analysis:")
    num_quantifiers = count_quantifiers(true_formula)
    print(f"Total quantifiers: {num_quantifiers}")
    
    # Check the formula string
    formula_str = str(true_formula)
    print(f"\nFormula contains:")
    print(f"  - 'h_sk2_true': {'h_sk2_true' in formula_str}")
    print(f"  - 'y_sk2_true': {'y_sk2_true' in formula_str}")
    print(f"  - 'Or(': {'Or(' in formula_str}")
    print(f"  - Length: {len(formula_str)}")
    
    # Now test with a real model
    print("\n2. Testing with actual model:")
    print("-"*40)
    
    # Create constraints and structure
    syntax_full = Syntax(premises, conclusions, sk2_operators)
    constraints = ModelConstraints(settings, syntax_full, semantics, UnilateralProposition)
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("Model found!")
        
        # Interpret and evaluate
        structure.interpret(syntax_full.premises)
        premise = syntax_full.premises[0]
        
        if premise.proposition:
            # Evaluate
            eval_result = premise.proposition.truth_value_at(eval_point)
            print(f"Premise evaluates to: {eval_result}")
            
            # Check what's in the model
            print("\nModel contents:")
            for decl in structure.z3_model.decls():
                if 'sk2' in str(decl):
                    print(f"  Found: {decl}")
            
            # Try to understand why it's false
            print("\nDiagnosing false evaluation:")
            
            # The issue might be that Z3 can't find witnesses even with Skolem functions
            # Let's check if any state verifies \\exclude A
            all_states = semantics.all_states
            verifying_states = []
            
            for state in all_states:
                # Check if state verifies \\exclude A
                verify_formula = op_instance.extended_verify(state, A, eval_point)
                if z3.is_true(structure.z3_model.evaluate(verify_formula)):
                    verifying_states.append(state)
            
            print(f"States that verify \\exclude A: {len(verifying_states)}")
            
            # Check if any of these are part of the main world
            main_world = structure.z3_model.eval(z3.BitVec('main_world', 3))
            print(f"Main world: {main_world}")
            
            for v_state in verifying_states:
                is_part = semantics.is_part_of(v_state, main_world)
                part_result = structure.z3_model.evaluate(is_part)
                if z3.is_true(part_result):
                    print(f"  State {v_state} is part of main world")

if __name__ == "__main__":
    analyze_formula_structure()