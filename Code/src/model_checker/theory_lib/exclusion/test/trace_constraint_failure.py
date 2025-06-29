"""Trace exactly why premise/conclusion constraints fail."""

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


def trace_constraint_failure(strategy, premises, conclusions, example_name):
    """Trace the exact constraint generation and why it allows invalid models."""
    
    print(f"\n{'='*80}")
    print(f"TRACING CONSTRAINT FAILURE: {example_name} ({strategy})")
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
    
    print("\n1. UNDERSTANDING THE CONSTRAINT GENERATION")
    print(f"Main point: {semantics.main_point}")
    
    # Now let's trace what happens when constraints are generated
    print("\n2. PREMISE CONSTRAINT GENERATION:")
    for i, premise in enumerate(syntax.premises):
        print(f"\nPremise {i}: {premises[i]}")
        print(f"Sentence object: {premise}")
        
        # The constraint is: semantics.premise_behavior(premise)
        # which is: semantics.true_at_cached(premise, semantics.main_point)
        
        # Let's manually call this to see what constraint is generated
        constraint = semantics.premise_behavior(premise)
        print(f"Generated constraint: {constraint}")
        print(f"Constraint type: {type(constraint)}")
        
        # Simplify to see it better
        simplified = z3.simplify(constraint)
        print(f"Simplified: {simplified}")
        
    print("\n3. CONCLUSION CONSTRAINT GENERATION:")
    for i, conclusion in enumerate(syntax.conclusions):
        print(f"\nConclusion {i}: {conclusions[i]}")
        
        constraint = semantics.conclusion_behavior(conclusion)
        print(f"Generated constraint: {constraint}")
        print(f"Simplified: {z3.simplify(constraint)}")
        
    # Now create the full model
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    structure = ExclusionStructure(constraints, settings)
    
    if not structure.z3_model:
        print("\n4. NO MODEL FOUND - constraints are unsatisfiable")
        return
        
    print("\n4. MODEL FOUND - checking constraint satisfaction")
    
    z3_model = structure.z3_model
    
    # Check how the constraints evaluate in the model
    print("\n5. CONSTRAINT EVALUATION IN MODEL:")
    
    for i, premise in enumerate(syntax.premises):
        constraint = semantics.premise_behavior(premise)
        evaluation = z3_model.evaluate(constraint)
        print(f"\nPremise {i} constraint evaluates to: {evaluation}")
        
        if z3.is_true(evaluation):
            print("✓ Constraint is satisfied (expects premise to be TRUE)")
        else:
            print("✗ Constraint is NOT satisfied")
            
    for i, conclusion in enumerate(syntax.conclusions):
        constraint = semantics.conclusion_behavior(conclusion)
        evaluation = z3_model.evaluate(constraint)
        print(f"\nConclusion {i} constraint evaluates to: {evaluation}")
        
        if z3.is_true(evaluation):
            print("✓ Constraint is satisfied (expects conclusion to be FALSE)")
        else:
            print("✗ Constraint is NOT satisfied")
            
    # Now check actual truth values
    print("\n6. ACTUAL TRUTH VALUES AFTER INTERPRETATION:")
    
    structure.interpret(syntax.premises)
    structure.interpret(syntax.conclusions)
    main_point = structure.main_point
    
    for i, premise in enumerate(syntax.premises):
        if premise.proposition:
            truth = premise.proposition.truth_value_at(main_point)
            verifiers = premise.proposition.verifiers
            print(f"\nPremise {i} actual truth: {truth}")
            print(f"Verifiers: {verifiers}")
            
            if not truth:
                print("⚠️  MISMATCH: Constraint satisfied but premise is FALSE!")
                
    for i, conclusion in enumerate(syntax.conclusions):
        if conclusion.proposition:
            truth = conclusion.proposition.truth_value_at(main_point)
            verifiers = conclusion.proposition.verifiers
            print(f"\nConclusion {i} actual truth: {truth}")
            print(f"Verifiers: {verifiers}")
            
            if truth:
                print("⚠️  MISMATCH: Constraint satisfied but conclusion is TRUE!")
                
    # The key question: why does the constraint evaluation differ from actual truth?
    print("\n7. DIAGNOSIS:")
    print("The constraints are generated BEFORE propositions are created.")
    print("The constraints use formula registry or direct formula generation.")
    print("The actual truth evaluation happens AFTER model solving with different logic.")
    print("This disconnect allows constraints to be satisfied while truth values violate expectations.")


def main():
    """Analyze key problematic examples."""
    
    test_cases = [
        (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
        (["\\exclude A"], ["A"], "Exclusion Contradiction"),
    ]
    
    for premises, conclusions, name in test_cases:
        trace_constraint_failure("QA", premises, conclusions, name)


if __name__ == '__main__':
    main()