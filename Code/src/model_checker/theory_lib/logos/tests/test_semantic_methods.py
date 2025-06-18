"""
Unit tests for LogosSemantics methods.

Tests validate individual semantic methods work correctly without
running the full model checking pipeline.
"""

import pytest
import z3
from model_checker.theory_lib.logos.semantic import LogosSemantics
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


class TestLogosSemanticInstantiation:
    """Test LogosSemantics instantiation and basic functionality."""
    
    def test_semantics_creation_valid_settings(self, basic_settings):
        """Test semantics creation with complete valid settings."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        assert semantics is not None
        assert semantics.N == basic_settings['N']
        assert semantics.operator_registry is registry
        
    def test_semantics_missing_required_settings(self):
        """Test semantics fails with missing required settings."""
        with pytest.raises((KeyError, AttributeError)):
            LogosSemantics({})  # Empty settings should fail
            
    def test_semantics_invalid_settings(self):
        """Test semantics fails with invalid setting values."""
        invalid_settings = {'N': -1, 'max_time': 'invalid'}
        with pytest.raises((ValueError, TypeError)):
            LogosSemantics(invalid_settings)


class TestSemanticPrimitives:
    """Test Z3 semantic primitive creation."""
    
    def test_verify_falsify_functions(self, basic_settings):
        """Test verify and falsify function creation."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        assert semantics.verify is not None
        assert semantics.falsify is not None
        assert isinstance(semantics.verify, z3.FuncDeclRef)
        assert isinstance(semantics.falsify, z3.FuncDeclRef)
        
    def test_possible_function(self, basic_settings):
        """Test possible state function creation."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        assert semantics.possible is not None
        assert isinstance(semantics.possible, z3.FuncDeclRef)
        
    def test_main_world_creation(self, basic_settings):
        """Test main world and main point creation."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        assert semantics.main_world is not None
        assert isinstance(semantics.main_world, z3.BitVecRef)
        assert semantics.main_point is not None
        assert "world" in semantics.main_point
        assert semantics.main_point["world"] == semantics.main_world


class TestSemanticOperations:
    """Test inherited semantic operations."""
    
    def test_fusion_operation(self, basic_settings):
        """Test state fusion operations."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        # Create test bitvectors
        state1 = z3.BitVec("state1", semantics.N)
        state2 = z3.BitVec("state2", semantics.N)
        
        # Test fusion operation exists and returns bitvector
        fusion_result = semantics.fusion(state1, state2)
        assert fusion_result is not None
        assert isinstance(fusion_result, z3.BitVecRef)
        
    def test_parthood_operations(self, basic_settings):
        """Test part-hood relationship operations."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        state1 = z3.BitVec("state1", semantics.N)
        state2 = z3.BitVec("state2", semantics.N)
        
        # Test parthood operation exists and returns bool
        parthood_result = semantics.is_part_of(state1, state2)
        assert parthood_result is not None
        assert isinstance(parthood_result, z3.BoolRef)
        
    def test_compatibility_operations(self, basic_settings):
        """Test state compatibility operations."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        state1 = z3.BitVec("state1", semantics.N)
        state2 = z3.BitVec("state2", semantics.N)
        
        # Test compatibility operation exists and returns bool
        compat_result = semantics.compatible(state1, state2)
        assert compat_result is not None
        assert isinstance(compat_result, z3.BoolRef)


class TestFrameConstraints:
    """Test frame constraint generation."""
    
    def test_frame_constraints_generation(self, basic_settings):
        """Test that frame constraints are properly generated."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        assert semantics.frame_constraints is not None
        assert isinstance(semantics.frame_constraints, list)
        assert len(semantics.frame_constraints) > 0
        
    def test_frame_constraints_structure(self, basic_settings):
        """Test frame constraints have expected structure."""
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        # All frame constraints should be Z3 expressions
        for constraint in semantics.frame_constraints:
            assert isinstance(constraint, (z3.BoolRef, z3.QuantifierRef))