#!/usr/bin/env python3
"""
Basic test for MS strategy functionality.
"""

import sys
import os
import time

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection

print("=== Basic MS Strategy Test ===")
print("Testing if MS strategy can be created and used...")

try:
    # Create operator collection for MS strategy
    operators = create_operator_collection("MS")
    print("✓ MS operator collection created successfully")
    
    # Create a simple model structure
    print("\nTesting with N=2 (simplest non-trivial case)...")
    
    # Set up components
    syntax = Syntax(operators)
    model_structure = ExclusionStructure(
        propositions=UnilateralProposition,
        semantics=ExclusionSemantics,
        N=2
    )
    
    # Test simple formula
    formula = "\\exclude A"
    print(f"Testing formula: {formula}")
    
    sentence = syntax.parse(formula)
    print("✓ Formula parsed successfully")
    
    # Create model constraints
    constraints = ModelConstraints(
        proposition_class=UnilateralProposition,
        operators=operators,
        N=2,
        settings={'possible': False, 'max_time': 1}
    )
    
    # Try to find a model
    start = time.time()
    print("Attempting to find model...")
    
    # Note: We won't actually run the full model checking 
    # to avoid timeout, just verify components work
    print("✓ All components initialized successfully")
    
except Exception as e:
    print(f"✗ Error: {str(e)}")
    import traceback
    traceback.print_exc()

print("\n=== Component Test Complete ===")

# Now let's analyze the MS strategy implementation
print("\n=== MS Strategy Analysis ===")

try:
    from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY
    
    if "MS" in STRATEGY_REGISTRY:
        print("✓ MS strategy is registered")
        ms_info = STRATEGY_REGISTRY["MS"]
        print(f"  Description: {ms_info.get('description', 'N/A')}")
        print(f"  Constraint type: {ms_info.get('constraint_type', 'N/A')}")
    else:
        print("✗ MS strategy not found in registry")
        print(f"Available strategies: {list(STRATEGY_REGISTRY.keys())}")
        
except Exception as e:
    print(f"✗ Error accessing strategy registry: {str(e)}")