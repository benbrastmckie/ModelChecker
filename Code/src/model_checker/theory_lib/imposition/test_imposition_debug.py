#!/usr/bin/env python3
"""
Debug script to test IM_TH_8 example directly
"""

import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from model_checker.theory_lib.imposition.semantic import ImpositionSemantics
from model_checker.theory_lib.imposition.operators import imposition_operators
from model_checker.builder import ModelBuilder
from model_checker.settings import Settings

def test_im_th_8():
    """Test the IM_TH_8 example: ¬A ⊭ (A ⊐ B)"""
    print("Testing IM_TH_8: ¬A ⊭ (A ⊐ B)")
    print("=" * 50)
    
    # Create settings
    settings = Settings(
        max_time=60000,
        max_propositions=2,
        max_states=10,
        max_relations=10,
        verbosity=2  # Higher verbosity for debugging
    )
    
    # Create semantics and operators
    semantics = ImpositionSemantics(settings)
    operators = imposition_operators
    
    # Create model builder
    builder = ModelBuilder(settings, semantics, operators)
    
    # Define premises and conclusions
    premises = ['\\neg A']
    conclusions = ['(A \\imposition B)']
    
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print()
    
    # Check if there's a countermodel
    print("Searching for countermodel...")
    result = builder.check_entailment(premises, conclusions)
    
    if result is None:
        print("\nNo countermodel found - the entailment holds!")
        print("This means: ¬A ⊨ (A ⊐ B)")
    else:
        print("\nCountermodel found - the entailment does not hold!")
        print("This means: ¬A ⊭ (A ⊐ B)")
        
        # Extract model info
        model_dict = result['model']
        assignments = result['assignments']
        
        print("\nModel details:")
        print(f"States: {model_dict.get('states', [])}")
        print(f"Actual state: {model_dict.get('actual_state')}")
        print(f"Propositions: {model_dict.get('propositions', [])}")
        
        print("\nAssignments:")
        for prop, states in assignments.items():
            print(f"  {prop} is true at states: {states}")
        
        print("\nEvaluation at actual state:")
        actual = model_dict.get('actual_state')
        print(f"  ¬A at state {actual}: ", end="")
        if 'A' in assignments and actual not in assignments['A']:
            print("True (A is false)")
        else:
            print("False (A is true)")
            
        print(f"  (A ⊐ B) at state {actual}: ", end="")
        # The imposition operator would need to be evaluated here
        # For now, just note that we found a countermodel
        print("False (since this is a countermodel)")
    
    print("\n" + "=" * 50)
    return result

if __name__ == "__main__":
    # Run the test
    result = test_im_th_8()
    
    # Exit with appropriate code
    if result is None:
        print("\nTest result: ENTAILMENT HOLDS (no countermodel)")
        sys.exit(0)
    else:
        print("\nTest result: ENTAILMENT FAILS (countermodel found)")
        sys.exit(1)