#!/usr/bin/env python3
"""
Investigate false premise issue in exclusion theory by examining constraint generation.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition
from model_checker.theory_lib.exclusion.operators import exclusion_operators, ExclusionOperatorMultiSort

def investigate_triple_negation():
    """Deep dive into Triple Negation Entailment constraints."""
    print("="*70)
    print("INVESTIGATING: Triple Negation Entailment")
    print("\\exclude \\exclude \\exclude A ⊨ \\exclude A")
    print("="*70)
    
    # Settings
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 10,
    }
    
    # Create syntax and semantics
    premises = ['\\exclude \\exclude \\exclude A']
    conclusions = ['\\exclude A']
    syntax = Syntax(premises, conclusions, exclusion_operators)
    semantics = ExclusionSemantics(settings)
    
    # Get the premise sentence object
    premise_sent = syntax.premises[0]
    print(f"\nPremise sentence: {premise_sent}")
    print(f"Sentence type: {type(premise_sent)}")
    
    # Create evaluation point
    eval_point = {"world": z3.BitVecVal(2, 3)}  # World b (010)
    print(f"\nEvaluation point: {eval_point}")
    
    # Generate the formula for the premise
    print("\n=== FORMULA GENERATION ===")
    formula = semantics.true_at(premise_sent, eval_point)
    print(f"Formula type: {type(formula)}")
    print(f"Formula string length: {len(str(formula))}")
    
    # Count quantifiers
    formula_str = str(formula)
    exists_count = formula_str.count('Exists')
    forall_count = formula_str.count('ForAll')
    print(f"\nQuantifier counts:")
    print(f"  Exists: {exists_count}")
    print(f"  ForAll: {forall_count}")
    
    # Look at the exclusion operator being used
    print("\n=== EXCLUSION OPERATOR ANALYSIS ===")
    print(f"Current default strategy: MS (Multi-Sort)")
    print(f"Operator class: {ExclusionOperatorMultiSort}")
    
    # Analyze the nested structure
    print("\n=== NESTED STRUCTURE ===")
    print("The formula \\exclude \\exclude \\exclude A has 3 nested exclusions:")
    print("1. Inner: \\exclude A")
    print("2. Middle: \\exclude (\\exclude A)")
    print("3. Outer: \\exclude (\\exclude \\exclude A)")
    print("\nEach exclusion introduces existential quantifiers for:")
    print("- The exclusion function h")
    print("- The witness y that gets excluded")
    
    # Create model constraints to test solving
    print("\n=== CONSTRAINT SOLVING ===")
    model_constraints = ModelConstraints(
        settings,
        syntax,
        semantics,
        UnilateralProposition
    )
    
    # Create a simple solver to test
    solver = z3.Solver()
    
    # Add premise constraint
    premise_constraint = model_constraints.premise_constraints[0]
    solver.add(premise_constraint)
    
    # Add conclusion negation
    conclusion_constraint = model_constraints.conclusion_constraints[0]
    solver.add(z3.Not(conclusion_constraint))
    
    print("Checking satisfiability...")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        print("\nCOUNTERMODEL FOUND")
        model = solver.model()
        
        # Look for h functions
        print("\n=== FUNCTION ANALYSIS ===")
        h_functions = []
        for decl in model.decls():
            if 'h_ms_' in str(decl):
                h_functions.append(decl)
                print(f"Found: {decl}")
        
        print(f"\nTotal h functions: {len(h_functions)}")
        
        # Try to evaluate the premise
        print("\n=== PREMISE EVALUATION TEST ===")
        premise_eval = model.evaluate(premise_constraint)
        print(f"Premise constraint evaluates to: {premise_eval}")
        print(f"z3.is_true(premise_eval): {z3.is_true(premise_eval)}")
        
        # The issue
        print("\n=== THE CORE ISSUE ===")
        print("During constraint solving:")
        print("  Z3 proves: ∃h1,h2,h3. P(h1,h2,h3) where P encodes the nested exclusions")
        print("  This means: 'there exist functions h1,h2,h3 that make the premise true'")
        print("\nDuring evaluation:")
        print("  Z3 evaluates: P(?,?,?) with no specific h1,h2,h3 available")
        print("  Result: The formula evaluates to false")
        print("\nThis is because Z3's existential quantifier satisfaction doesn't")
        print("preserve the witness functions in the final model.")

def propose_solutions():
    """Propose concrete solutions to the false premise issue."""
    print("\n\n" + "="*70)
    print("PROPOSED SOLUTIONS")
    print("="*70)
    
    print("\n1. SKOLEMIZATION APPROACH")
    print("   Replace ∃h.P(h) with P(f_skolem)")
    print("   - Create named Skolem functions upfront")
    print("   - No existential quantifiers")
    print("   - Functions are explicit in the model")
    
    print("\n2. GLOBAL FUNCTION APPROACH")
    print("   Define a single global exclusion function")
    print("   - exclusion_func: State × Proposition → State")
    print("   - No per-instance quantification")
    print("   - Reuse the same function everywhere")
    
    print("\n3. WITNESS CACHING")
    print("   Cache function witnesses during solving")
    print("   - Intercept Z3's internal witness generation")
    print("   - Store witnesses for reuse during evaluation")
    print("   - Requires Z3 API extensions")
    
    print("\n4. REFORMULATE EXCLUSION SEMANTICS")
    print("   Avoid existential quantifiers entirely")
    print("   - Use a different semantic formulation")
    print("   - Trade expressiveness for computability")
    
    print("\n5. TWO-PHASE VERIFICATION")
    print("   Separate constraint satisfaction from evaluation")
    print("   - Phase 1: Find that a model exists")
    print("   - Phase 2: Construct explicit witnesses")
    print("   - More complex but preserves semantics")

if __name__ == "__main__":
    investigate_triple_negation()
    propose_solutions()