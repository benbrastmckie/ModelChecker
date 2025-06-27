#!/usr/bin/env python3
"""
Check if SK2 truly eliminates existential quantifiers.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics
from model_checker.theory_lib.exclusion.operators import (
    ExclusionOperatorMultiSort,
    ExclusionOperatorSkolemized2,
    create_operator_collection
)

def analyze_formula_quantifiers(formula, name):
    """Analyze quantifiers in a formula."""
    print(f"\nAnalyzing {name}:")
    print("-" * 40)
    
    # Convert to string
    formula_str = str(formula)
    
    # Look for quantifier patterns
    import re
    
    # Find all Exists patterns
    exists_pattern = r'Exists\('
    exists_matches = re.findall(exists_pattern, formula_str)
    
    # Find all ForAll patterns
    forall_pattern = r'ForAll\('
    forall_matches = re.findall(forall_pattern, formula_str)
    
    print(f"Formula contains:")
    print(f"  - {len(exists_matches)} Exists quantifiers")
    print(f"  - {len(forall_matches)} ForAll quantifiers")
    
    # Look for function names
    h_patterns = re.findall(r'h_\w+_\d+', formula_str)
    y_patterns = re.findall(r'y_\w+_\d+', formula_str)
    
    print(f"  - {len(set(h_patterns))} unique h functions")
    print(f"  - {len(set(y_patterns))} unique y functions")
    
    # Print first few characters to see structure
    print(f"\nFirst 200 chars of formula:")
    print(formula_str[:200] + "...")
    
    return len(exists_matches), len(forall_matches)

def test_strategies():
    """Test both strategies and analyze their formulas."""
    print("="*60)
    print("EXISTENTIAL QUANTIFIER ANALYSIS")
    print("="*60)
    
    # Settings
    settings = {'N': 3}
    semantics = ExclusionSemantics(settings)
    
    # Create test sentence
    syntax = Syntax(['A'], [], create_operator_collection('MS'))
    arg_sent = syntax.sentence_letters[0]
    
    # Test state
    state = z3.BitVec("test_state", 3)
    eval_point = {"world": z3.BitVecVal(0, 3)}
    
    # Test MS strategy
    ms_op = ExclusionOperatorMultiSort(semantics)
    ms_formula = ms_op.extended_verify(state, arg_sent, eval_point)
    ms_exists, ms_forall = analyze_formula_quantifiers(ms_formula, "MS Strategy")
    
    # Test SK2 strategy
    sk2_op = ExclusionOperatorSkolemized2(semantics)
    sk2_formula = sk2_op.extended_verify(state, arg_sent, eval_point)
    sk2_exists, sk2_forall = analyze_formula_quantifiers(sk2_formula, "SK2 Strategy")
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"\nMS Strategy:")
    print(f"  - Existential quantifiers: {ms_exists}")
    print(f"  - Universal quantifiers: {ms_forall}")
    
    print(f"\nSK2 Strategy:")
    print(f"  - Existential quantifiers: {sk2_exists}")
    print(f"  - Universal quantifiers: {sk2_forall}")
    
    if sk2_exists == 0 and sk2_forall > 0:
        print("\n✓ SUCCESS: SK2 uses only universal quantifiers!")
        print("This should solve the false premise issue.")
    else:
        print("\n✗ WARNING: SK2 may still have quantifier issues.")
    
    # Now let's check the actual Z3 expression structure
    print("\n" + "="*60)
    print("Z3 EXPRESSION STRUCTURE")
    print("="*60)
    
    def check_z3_expr(expr, depth=0):
        """Recursively check Z3 expression for quantifiers."""
        indent = "  " * depth
        if z3.is_quantifier(expr):
            if expr.is_forall():
                print(f"{indent}ForAll found at depth {depth}")
            elif expr.is_exists():
                print(f"{indent}EXISTS found at depth {depth} !!!")
            # Check body
            check_z3_expr(expr.body(), depth + 1)
        elif z3.is_and(expr) or z3.is_or(expr) or z3.is_implies(expr):
            for child in expr.children():
                check_z3_expr(child, depth)
    
    print("\nMS formula structure:")
    check_z3_expr(ms_formula)
    
    print("\nSK2 formula structure:")
    check_z3_expr(sk2_formula)

if __name__ == "__main__":
    test_strategies()