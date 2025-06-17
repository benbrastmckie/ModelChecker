#!/usr/bin/env python3
"""Debug script to identify CF_TH_4 discrepancy between default and logos theories."""

import sys
import os

# Add the src directory to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from model_checker import BuildExample

def test_cf_th4():
    """Test CF_TH_4 example in both theories."""
    
    # Define the example
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N': 4,
        'contingent': False,
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'max_time': 1,
        'iterate': 1,
        'expectation': False,
    }
    
    print("=" * 60)
    print("Testing CF_TH_4: ((A ∨ B) □→ C) ⊢ ((A ∧ B) □→ C)")
    print("=" * 60)
    
    # Test with default theory
    print("\n1. DEFAULT THEORY:")
    print("-" * 40)
    
    try:
        from model_checker.theory_lib.default.semantic import Semantics, Proposition, ModelStructure
        from model_checker.theory_lib.default.operators import default_operators
        
        default_theory = {
            "semantics": Semantics,
            "proposition": Proposition,
            "model": ModelStructure,
            "operators": default_operators,
        }
        
        result = BuildExample(
            premises=premises,
            conclusions=conclusions,
            settings=settings,
            semantic_theory=default_theory,
            example_name="CF_TH_4_default"
        )
        
        model_status = result['model_status']
        print(f"Result: {'No countermodel (Valid)' if model_status else 'Countermodel found (Invalid)'}")
        
    except Exception as e:
        print(f"Error in default theory: {e}")
    
    # Test with logos theory
    print("\n2. LOGOS THEORY:")
    print("-" * 40)
    
    try:
        from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
        from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
        
        # Create operator registry for counterfactual theory
        counterfactual_registry = LogosOperatorRegistry()
        counterfactual_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
        
        logos_theory = {
            "semantics": LogosSemantics,
            "proposition": LogosProposition,
            "model": LogosModelStructure,
            "operators": counterfactual_registry.get_operators(),
        }
        
        result = BuildExample(
            premises=premises,
            conclusions=conclusions,
            settings=settings,
            semantic_theory=logos_theory,
            example_name="CF_TH_4_logos"
        )
        
        model_status = result['model_status']
        print(f"Result: {'No countermodel (Valid)' if model_status else 'Countermodel found (Invalid)'}")
        
        # If countermodel found, show details
        if not model_status:
            model_structure = result['model_structure']
            if model_structure and hasattr(model_structure, 'main_world'):
                print(f"\nCountermodel details:")
                print(f"Main world: {model_structure.main_world}")
                
    except Exception as e:
        print(f"Error in logos theory: {e}")

if __name__ == "__main__":
    test_cf_th4()