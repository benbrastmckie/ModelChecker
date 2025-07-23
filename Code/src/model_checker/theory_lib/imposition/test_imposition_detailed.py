#!/usr/bin/env python3
"""
Detailed test script for IM_TH_8 that shows the countermodel
"""

import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from model_checker.utils import get_theory
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints, ModelDefaults
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics
import z3

def test_im_th_8_detailed():
    """Test the IM_TH_8 example with detailed output"""
    print("Testing IM_TH_8: ¬A ⊭ (A ⊐ B)")
    print("This should find a countermodel where ¬A is true but (A ⊐ B) is false")
    print("=" * 70)
    
    # Get the imposition theory
    theory = get_theory("imposition")
    
    # Extract components
    semantics_class = theory["semantics"]
    proposition_class = theory["proposition"]
    operators = theory["operators"]
    model_structure_class = theory.get("model", ModelDefaults)
    
    # Define the example
    premises = ['\\neg A']
    conclusions = ['(A \\imposition B)']
    settings = {
        'N': 3,
        'contingent': False,
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'max_time': 60000,  # Increase timeout for detailed analysis
        'expectation': False,
    }
    
    # Create syntax and semantics
    example_syntax = Syntax(premises, conclusions, operators)
    semantics = semantics_class(settings)
    
    # Create model constraints
    constraints = ModelConstraints(
        example_syntax.language_syntax,
        semantics,
        proposition_class,
        model_structure_class
    )
    
    # Create model structure
    model_structure = model_structure_class(constraints)
    
    # Set up Z3 solver
    solver = z3.Solver()
    solver.set("timeout", settings['max_time'])
    
    # Add constraints
    solver.add(model_structure.modal_setup)
    solver.add(model_structure.modal_axioms)
    solver.add(model_structure.modal_validity_constraints)
    
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print()
    
    # Check satisfiability
    result = solver.check()
    
    if result == z3.sat:
        print("Countermodel found!")
        print("-" * 70)
        
        # Get the model
        z3_model = solver.model()
        
        # Extract states
        states = []
        for i in range(2**settings['N']):
            if z3_model.eval(model_structure.state_bitvectors[i]) == z3.BitVecVal(i, settings['N']):
                states.append(f"S{i}")
        
        print(f"States in model: {states}")
        
        # Extract actual state
        actual_val = z3_model.eval(model_structure.actual_world_variable)
        actual_state = f"S{actual_val}"
        print(f"Actual state: {actual_state}")
        
        # Extract proposition assignments
        print("\nProposition assignments:")
        for prop_name in ['A', 'B']:
            if prop_name in model_structure.named_propositions:
                prop = model_structure.named_propositions[prop_name]
                true_states = []
                for i, state in enumerate(states):
                    state_idx = int(state[1:])
                    if z3_model.eval(prop.proposition_object[state_idx]):
                        true_states.append(state)
                print(f"  {prop_name} is true at: {true_states if true_states else 'nowhere'}")
        
        # Evaluate formulas at actual state
        print(f"\nEvaluation at actual state {actual_state}:")
        
        # Check ¬A
        actual_idx = int(actual_state[1:])
        A_prop = model_structure.named_propositions['A']
        A_at_actual = z3_model.eval(A_prop.proposition_object[actual_idx])
        print(f"  A at {actual_state}: {A_at_actual}")
        print(f"  ¬A at {actual_state}: {not A_at_actual}")
        
        # The imposition (A ⊐ B) evaluation is complex, but we know it's false
        # since this is a countermodel
        print(f"  (A ⊐ B) at {actual_state}: False (since this is a countermodel)")
        
        print("\nCountermodel explanation:")
        print("  - The premise ¬A is true (A is false at the actual state)")
        print("  - The conclusion (A ⊐ B) is false")
        print("  - Therefore, ¬A ⊭ (A ⊐ B)")
        
    elif result == z3.unsat:
        print("No countermodel found - the entailment holds!")
        print("This would mean: ¬A ⊨ (A ⊐ B)")
    else:
        print("Z3 solver returned unknown (possibly timeout)")
    
    print("\n" + "=" * 70)
    return result == z3.sat

if __name__ == "__main__":
    # Run the test
    found_countermodel = test_im_th_8_detailed()
    
    # Exit with appropriate code
    if found_countermodel:
        print("\nResult: COUNTERMODEL FOUND - Entailment does not hold")
        sys.exit(0)
    else:
        print("\nResult: NO COUNTERMODEL - Entailment holds")
        sys.exit(1)