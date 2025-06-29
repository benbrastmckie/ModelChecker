"""Trace premise/conclusion behavior constraint generation."""

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


def trace_premise_conclusion_constraints(strategy, premises, conclusions, example_name):
    """Extract exact premise/conclusion behavior constraints."""
    
    print(f"\n{'='*60}")
    print(f"TRACING CONSTRAINTS: {example_name}")
    print(f"Strategy: {strategy}")
    print(f"{'='*60}")
    
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
    
    # Create model constraints - this is where premise/conclusion behavior is set up
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    # Access the Z3 solver to examine constraints
    solver = constraints.solver
    
    print("\n1. MAIN POINT CONSTRAINT:")
    # The main point is typically constrained to be possible
    print(f"Main point: {constraints.main_point}")
    
    print("\n2. PREMISE BEHAVIOR CONSTRAINTS:")
    print("Expected: All premises must be TRUE at main point")
    
    # Look for premise-related constraints
    all_constraints = solver.assertions()
    premise_constraints = []
    
    for i, premise in enumerate(syntax.premises):
        print(f"\nPremise {i}: {premises[i]}")
        # During constraint generation, premises should be constrained to be true
        # This happens in premise_behavior method
        
    print("\n3. CONCLUSION BEHAVIOR CONSTRAINTS:")
    print("Expected: All conclusions must be FALSE at main point")
    
    for i, conclusion in enumerate(syntax.conclusions):
        print(f"\nConclusion {i}: {conclusions[i]}")
        # During constraint generation, conclusions should be constrained to be false
        # This happens in conclusion_behavior method
        
    print("\n4. CONSTRAINT COUNT:")
    print(f"Total constraints generated: {len(all_constraints)}")
    
    # Try to identify specific premise/conclusion constraints
    print("\n5. SEARCHING FOR TRUTH CONSTRAINTS:")
    
    # Look for constraints that reference truth values
    truth_constraints = []
    for constraint in all_constraints:
        constraint_str = str(constraint)
        if "true" in constraint_str.lower() or "false" in constraint_str.lower():
            truth_constraints.append(constraint)
    
    print(f"Found {len(truth_constraints)} potential truth-related constraints")
    
    # Now actually solve and check if we get an invalid model
    print("\n6. SOLVING:")
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("Model found!")
        
        # Interpret to create propositions
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        # Check validity
        main_point = structure.main_point
        
        print("\n7. MODEL VALIDITY CHECK:")
        
        invalid = False
        for i, premise in enumerate(syntax.premises):
            if premise.proposition:
                truth = premise.proposition.truth_value_at(main_point)
                print(f"Premise {i} truth: {truth}")
                if not truth:
                    print("  ⚠️  FALSE PREMISE FOUND!")
                    invalid = True
                    
        for i, conclusion in enumerate(syntax.conclusions):
            if conclusion.proposition:
                truth = conclusion.proposition.truth_value_at(main_point)
                print(f"Conclusion {i} truth: {truth}")
                if truth:
                    print("  ⚠️  TRUE CONCLUSION FOUND!")
                    invalid = True
                    
        if invalid:
            print("\n⚠️  INVALID MODEL DETECTED")
            print("This model violates premise/conclusion constraints!")
            
            # Examine verifiers
            print("\n8. VERIFIER ANALYSIS:")
            for i, premise in enumerate(syntax.premises):
                if premise.proposition:
                    verifiers = premise.proposition.verifiers
                    print(f"Premise {i} verifiers: {verifiers}")
                    if not verifiers:
                        print("  ⚠️  EMPTY VERIFIERS!")
                        
            for i, conclusion in enumerate(syntax.conclusions):
                if conclusion.proposition:
                    verifiers = conclusion.proposition.verifiers
                    print(f"Conclusion {i} verifiers: {verifiers}")
                    if not verifiers:
                        print("  ⚠️  EMPTY VERIFIERS!")
                        
    else:
        print("No model found")
        
    return {
        'model_found': structure.z3_model is not None,
        'constraint_count': len(all_constraints),
        'truth_constraint_count': len(truth_constraints)
    }


def main():
    """Test constraint tracing on a problematic example."""
    
    # Test with Disjunctive DeMorgan's RL - known to have false premise
    test_cases = [
        (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
        (["\\exclude \\exclude \\exclude A"], ["\\exclude A"], "Triple Negation"),
    ]
    
    for premises, conclusions, name in test_cases:
        trace_premise_conclusion_constraints("QA", premises, conclusions, name)


if __name__ == '__main__':
    main()