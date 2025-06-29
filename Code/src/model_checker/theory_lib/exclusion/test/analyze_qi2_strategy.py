"""Analyze QI2 strategy constraint generation."""

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


def analyze_qi2_constraints():
    """Analyze how QI2 handles the same problematic cases."""
    
    print("ANALYZING QI2 STRATEGY CONSTRAINTS")
    print("="*60)
    
    test_cases = [
        (["\\exclude A"], ["A"], "Exclusion Contradiction"),
        (["(\\exclude A \\uniwedge \\exclude B)"], ["\\exclude (A \\univee B)"], "Disjunctive DeMorgan's RL"),
    ]
    
    for premises, conclusions, name in test_cases:
        print(f"\n{'='*60}")
        print(f"EXAMPLE: {name}")
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
            'exclusion_strategy': 'QI2',  # Using QI2 strategy
            'print_constraints': False,
            'print_z3': False,
        }
        
        # Create components
        semantics = ExclusionSemantics(settings)
        operators = create_operator_collection('QI2')
        syntax = syntactic.Syntax(premises, conclusions, operators)
        
        print(f"\nPremise: {premises[0]}")
        print(f"Conclusion: {conclusions[0]}")
        
        # Create model constraints
        constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
        
        print("\n1. CONSTRAINT GENERATION:")
        if constraints.premise_constraints:
            pc = constraints.premise_constraints[0]
            print(f"Premise constraint type: {type(pc)}")
            print(f"Premise constraint (first 200 chars): {str(pc)[:200]}...")
            
        if constraints.conclusion_constraints:
            cc = constraints.conclusion_constraints[0]
            print(f"Conclusion constraint type: {type(cc)}")
            print(f"Conclusion constraint (first 200 chars): {str(cc)[:200]}...")
            
        # Solve
        structure = ExclusionStructure(constraints, settings)
        
        if structure.z3_model:
            print("\n2. MODEL FOUND")
            z3_model = structure.z3_model
            
            # Check constraint satisfaction
            if constraints.premise_constraints:
                eval_result = z3_model.evaluate(constraints.premise_constraints[0])
                print(f"Premise constraint satisfied: {z3.is_true(eval_result)}")
                
            if constraints.conclusion_constraints:
                eval_result = z3_model.evaluate(constraints.conclusion_constraints[0])
                print(f"Conclusion constraint satisfied: {z3.is_true(eval_result)}")
                
            # Interpret and check truth
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            
            main_point = structure.main_point
            
            print("\n3. TRUTH VALUES:")
            invalid = False
            
            for i, premise in enumerate(syntax.premises):
                if premise.proposition:
                    truth = premise.proposition.truth_value_at(main_point)
                    verifiers = premise.proposition.verifiers
                    print(f"Premise truth: {truth}, verifiers: {verifiers}")
                    if not truth:
                        print("  ⚠️  FALSE PREMISE!")
                        invalid = True
                        
            for i, conclusion in enumerate(syntax.conclusions):
                if conclusion.proposition:
                    truth = conclusion.proposition.truth_value_at(main_point)
                    verifiers = conclusion.proposition.verifiers
                    print(f"Conclusion truth: {truth}, verifiers: {verifiers}")
                    if truth:
                        print("  ⚠️  TRUE CONCLUSION!")
                        invalid = True
                        
            if invalid:
                print("\n4. INVALID MODEL DETECTED")
                print("QI2 also suffers from the same constraint/truth disconnect!")
                
        else:
            print("\n2. NO MODEL FOUND")
            
    print("\n" + "="*60)
    print("QI2 ANALYSIS SUMMARY:")
    print("QI2 uses a different exclusion function implementation but has the same fundamental issue:")
    print("- Constraints can be satisfied with models that assign empty verifiers")
    print("- Truth evaluation requires non-empty verifiers for truth")
    print("- This disconnect allows invalid models")


def main():
    analyze_qi2_constraints()


if __name__ == '__main__':
    main()