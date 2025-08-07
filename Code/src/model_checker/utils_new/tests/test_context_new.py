"""Tests for Z3ContextManager in new location."""

import pytest
import z3


def test_z3_context_manager_from_new_location():
    """Test that Z3ContextManager can be imported from new location."""
    from model_checker.utils_new import Z3ContextManager
    assert Z3ContextManager is not None
    

def test_new_reset_context_works():
    """Test that reset_context from new location works correctly."""
    from model_checker.utils_new import Z3ContextManager
    
    # Create a solver with some constraints
    s1 = z3.Solver()
    x = z3.Int('x')
    s1.add(x > 0)
    assert s1.check() == z3.sat
    
    # Reset context using new location
    Z3ContextManager.reset_context()
    
    # Create a new solver - should be independent
    s2 = z3.Solver()
    y = z3.Int('y')
    s2.add(y < 0)
    assert s2.check() == z3.sat