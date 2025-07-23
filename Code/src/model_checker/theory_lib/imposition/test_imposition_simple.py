#!/usr/bin/env python3
"""
Simple test script for IM_TH_8 example using the correct API
"""

import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from model_checker.utils import get_theory, run_test
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints, ModelDefaults

def test_im_th_8():
    """Test the IM_TH_8 example: ¬A ⊭ (A ⊐ B)"""
    print("Testing IM_TH_8: ¬A ⊭ (A ⊐ B)")
    print("=" * 50)
    
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
        'max_time': 1,
        'expectation': False,
    }
    
    example_case = [premises, conclusions, settings]
    
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print()
    
    # Run the test
    print("Running model checker...")
    result = run_test(
        example_case,
        semantics_class,
        proposition_class,
        operators,
        Syntax,
        ModelConstraints,
        model_structure_class
    )
    
    if result:
        print("\nTest passed - the entailment holds!")
        print("This means: ¬A ⊨ (A ⊐ B)")
    else:
        print("\nTest failed - the entailment does not hold!")
        print("This means: ¬A ⊭ (A ⊐ B)")
        print("A countermodel was found.")
    
    print("\n" + "=" * 50)
    return result

if __name__ == "__main__":
    # Run the test
    result = test_im_th_8()
    
    # Exit with appropriate code
    if result:
        print("\nTest result: ENTAILMENT HOLDS")
        sys.exit(0)
    else:
        print("\nTest result: ENTAILMENT FAILS (countermodel found)")
        sys.exit(1)