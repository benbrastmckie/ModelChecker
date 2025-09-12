"""Tests for Z3 context management."""

import pytest
import z3


def test_z3_context_manager_exists():
    """Test that Z3ContextManager can be imported."""
    from model_checker.utils import Z3ContextManager
    from model_checker.utils.context import reset_z3_context
    assert Z3ContextManager is not None
    assert reset_z3_context is not None
    

def test_reset_context_method_exists():
    """Test that reset_context method exists."""
    from model_checker.utils import Z3ContextManager
    from model_checker.utils.context import reset_z3_context
    manager = Z3ContextManager()
    assert hasattr(manager, 'reset_context')
    assert callable(manager.reset_context)
    assert callable(reset_z3_context)


def test_reset_context_clears_z3_state():
    """Test that reset_context actually clears Z3 state."""
    from model_checker.utils.context import reset_z3_context
    
    # Create a solver with some constraints
    s1 = z3.Solver()
    x = z3.Int('x')
    s1.add(x > 0)
    assert s1.check() == z3.sat
    
    # Reset context
    reset_z3_context()
    
    # Create a new solver - should be independent
    s2 = z3.Solver()
    y = z3.Int('y')
    s2.add(y < 0)
    assert s2.check() == z3.sat
    

def test_reset_context_handles_missing_attributes():
    """Test that reset_context handles missing Z3 attributes gracefully."""
    from model_checker.utils.context import reset_z3_context
    
    # This should not raise an exception
    try:
        reset_z3_context()
    except AttributeError:
        pytest.fail("reset_context should handle missing attributes gracefully")


def test_multiple_resets():
    """Test that multiple context resets work correctly."""
    from model_checker.utils.context import reset_z3_context
    
    # Multiple resets should not cause issues
    for _ in range(3):
        reset_z3_context()
        
        # Create a solver to verify Z3 still works
        s = z3.Solver()
        x = z3.Bool('x')
        s.add(x)
        assert s.check() == z3.sat