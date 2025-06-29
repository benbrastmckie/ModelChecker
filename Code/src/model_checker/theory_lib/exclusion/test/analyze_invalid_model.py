"""Analyze why invalid models satisfy premise/conclusion constraints."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic
import z3


def analyze_constraint_generation(strategy, premises, conclusions, example_name):
    """Analyze how premise/conclusion constraints are generated and why they fail."""
    
    print(f"\n{'='*80}")
    print(f"ANALYZING: {example_name} with {strategy} strategy")
    print(f"{'='*80}")
    
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
        'exclusion_strategy': strategy,
        'print_constraints': False,
        'print_z3': False,
    }
    
    # Create components
    semantics = ExclusionSemantics(settings)
    operators = create_operator_collection(strategy)
    syntax = syntactic.Syntax(premises, conclusions, operators)
    
    print("\n1. CONSTRAINT GENERATION MECHANISM:")
    print(f"use_formula_registry: {semantics.use_formula_registry}")
    print(f"premise_behavior type: {type(semantics.premise_behavior)}")
    print(f"conclusion_behavior type: {type(semantics.conclusion_behavior)}")
    
    # Create model constraints
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    print("\n2. PREMISE/CONCLUSION CONSTRAINTS:")
    print(f"Number of premise constraints: {len(constraints.premise_constraints)}")
    print(f"Number of conclusion constraints: {len(constraints.conclusion_constraints)}")
    
    # Solve the model
    structure = ExclusionStructure(constraints, settings)
    
    if not structure.z3_model:
        print("\n3. NO MODEL FOUND")
        return None
        
    print("\n3. MODEL FOUND - ANALYZING VALIDITY")
    
    # Interpret to create propositions
    structure.interpret(syntax.premises)
    structure.interpret(syntax.conclusions)
    
    main_point = structure.main_point
    main_world = main_point['world']
    
    print(f"\nMain evaluation point: world={main_world}")
    
    # Analyze each premise
    print("\n4. PREMISE ANALYSIS:")
    for i, premise in enumerate(syntax.premises):
        print(f"\nPremise {i}: {premises[i]}")
        
        if premise.proposition:
            prop = premise.proposition
            verifiers = prop.verifiers
            truth = prop.truth_value_at(main_point)
            
            print(f"  Verifiers: {verifiers}")
            print(f"  Truth value: {truth}")
            
            if not truth:
                print("  ⚠️  FALSE PREMISE DETECTED!")
                
                # Analyze why the constraint was satisfied
                print("\n  CONSTRAINT SATISFACTION ANALYSIS:")
                
                # The premise_behavior constraint should have required this to be true
                # Let's trace what happened
                print(f"  Expected constraint: true_at({premises[i]}, main_point)")
                
                # Check if verifiers are empty
                if not verifiers:
                    print("  ⚠️  EMPTY VERIFIERS - this is likely the issue")
                    print("  Empty verifiers lead to false truth value")
                    print("  But how did the true_at constraint get satisfied?")
                    
                # Try to understand the constraint
                # The constraint would have been generated during ModelConstraints.__init__
                # as semantics.premise_behavior(premise) which calls true_at(premise, main_point)
                
    # Analyze each conclusion
    print("\n5. CONCLUSION ANALYSIS:")
    for i, conclusion in enumerate(syntax.conclusions):
        print(f"\nConclusion {i}: {conclusions[i]}")
        
        if conclusion.proposition:
            prop = conclusion.proposition
            verifiers = prop.verifiers
            truth = prop.truth_value_at(main_point)
            
            print(f"  Verifiers: {verifiers}")
            print(f"  Truth value: {truth}")
            
            if truth:
                print("  ⚠️  TRUE CONCLUSION DETECTED!")
                
                print("\n  CONSTRAINT SATISFACTION ANALYSIS:")
                print(f"  Expected constraint: false_at({conclusions[i]}, main_point)")
                
                if verifiers:
                    print(f"  Non-empty verifiers: {verifiers}")
                    print("  This should have been constrained to be false")
                    
    # Extract Z3 model details
    print("\n6. Z3 MODEL DETAILS:")
    z3_model = structure.z3_model
    
    # Look for exclusion function assignments
    print("\nExclusion function sample values:")
    for decl in z3_model.decls():
        if 'exclusion' in str(decl).lower():
            print(f"  {decl}: {z3_model[decl]}")
            
    return {
        'model_found': True,
        'has_false_premise': any(not p.proposition.truth_value_at(main_point) 
                                for p in syntax.premises if p.proposition),
        'has_true_conclusion': any(c.proposition.truth_value_at(main_point) 
                                  for c in syntax.conclusions if c.proposition)
    }


def main():
    """Analyze problematic examples."""
    
    # Test cases known to have issues
    test_cases = [
        (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
        (["\\exclude \\exclude \\exclude A"], ["\\exclude A"], "Triple Negation"),
        (["\\exclude A"], ["A"], "Exclusion Contradiction"),
    ]
    
    print("INVESTIGATING CONSTRAINT SATISFACTION FOR INVALID MODELS")
    
    for premises, conclusions, name in test_cases:
        result = analyze_constraint_generation("QA", premises, conclusions, name)
        if result and (result['has_false_premise'] or result['has_true_conclusion']):
            print(f"\n⚠️  CONFIRMED INVALID MODEL for {name}")


if __name__ == '__main__':
    main()