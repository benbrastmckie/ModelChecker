#!/usr/bin/env python3
"""Test SemanticDefaults import and functionality after refactoring."""

import sys
import os
sys.path.insert(0, 'src')

# Test imports work correctly
print("Testing imports...")
from model_checker.model import SemanticDefaults as ModelSemanticDefaults
from model_checker.models.semantic import SemanticDefaults as DirectSemanticDefaults
from model_checker.models import SemanticDefaults as PackageSemanticDefaults

# Verify all imports point to the same class
assert ModelSemanticDefaults is DirectSemanticDefaults, "Import from model.py doesn't match direct import"
assert DirectSemanticDefaults is PackageSemanticDefaults, "Package import doesn't match direct import"
print("✓ All imports point to the same class")

# Test basic functionality
print("\nTesting functionality...")
test_settings = {'N': 3}
semantics = DirectSemanticDefaults(test_settings)

# Verify attributes were set correctly
assert semantics.N == 3, "N not set correctly"
assert hasattr(semantics, 'full_state'), "full_state not created"
assert hasattr(semantics, 'null_state'), "null_state not created"
assert len(semantics.all_states) == 8, f"all_states has wrong length: {len(semantics.all_states)}"
print("✓ Attributes set correctly")

# Test fusion operation
from z3 import BitVecVal
bit1 = BitVecVal(0b101, 3)
bit2 = BitVecVal(0b011, 3)
result = semantics.fusion(bit1, bit2)
expected = BitVecVal(0b111, 3)
assert result.as_long() == expected.as_long(), f"Fusion failed: {result} != {expected}"
print("✓ Fusion operation works")

# Test part_of relation
assert semantics.is_part_of(bit1, result).sexpr() == 'true', "is_part_of failed"
print("✓ is_part_of relation works")

print("\nAll tests passed! SemanticDefaults refactoring successful.")

# Clean up
os.remove(__file__)