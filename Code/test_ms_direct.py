#!/usr/bin/env python3
"""
Direct test of MS strategy implementation.
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
from model_checker.theory_lib.exclusion.operators import create_operator_collection, STRATEGY_REGISTRY

print("=== Direct MS Strategy Test ===")
print()

# First check if MS strategy is available
print("Available strategies:", list(STRATEGY_REGISTRY.keys()))
print()

# Create MS operator collection
ms_operators = create_operator_collection("MS")
print("MS operator collection created successfully")
print()

# Test 1: Simple case with N=3
print("Test 1: N=3, formula: \\exclude A")
try:
    syntax = Syntax(ms_operators)
    model = ExclusionStructure(N=3)
    
    # Parse formula
    formula = syntax.parse("\\exclude A")
    print(f"  Formula parsed: {formula}")
    
    # Create proposition
    prop = UnilateralProposition(model, formula)
    print(f"  Proposition created")
    
    # Test settings
    settings = {
        'N': 3,
        'max_time': 2,
        'possible': False,
        'contingent': False,
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'fusion_closure': False,
    }
    
    # Create model constraints
    mc = ModelConstraints(
        settings,
        model, 
        prop,
        # No premises for this test
        premises=[],
        conclusions=["\\exclude A"],
        designated=True,
        is_conclusion=True
    )
    
    print(f"  Model constraints created")
    print(f"  Testing with MS strategy...")
    
    start = time.time()
    result = mc.check_model()
    elapsed = time.time() - start
    
    print(f"  Result: {result}")
    print(f"  Time: {elapsed:.3f}s")
    
except Exception as e:
    print(f"  Error: {type(e).__name__}: {str(e)}")
    import traceback
    traceback.print_exc()

print()

# Test 2: Double exclusion with N=3
print("Test 2: N=3, formula: \\exclude \\exclude A")
try:
    syntax = Syntax(ms_operators)
    model = ExclusionStructure(N=3)
    
    formula = syntax.parse("\\exclude \\exclude A")
    print(f"  Formula parsed: {formula}")
    
    prop = UnilateralProposition(model, formula)
    print(f"  Proposition created")
    
    settings = {
        'N': 3,
        'max_time': 2,
        'possible': False,
        'contingent': False,
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'fusion_closure': False,
    }
    
    mc = ModelConstraints(
        settings,
        model, 
        prop,
        premises=[],
        conclusions=["\\exclude \\exclude A"],
        designated=True,
        is_conclusion=True
    )
    
    print(f"  Testing with MS strategy...")
    
    start = time.time()
    result = mc.check_model()
    elapsed = time.time() - start
    
    print(f"  Result: {result}")
    print(f"  Time: {elapsed:.3f}s")
    
except Exception as e:
    print(f"  Error: {type(e).__name__}: {str(e)}")
    import traceback
    traceback.print_exc()