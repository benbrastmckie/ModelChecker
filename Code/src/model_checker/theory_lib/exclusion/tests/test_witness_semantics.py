"""
Unit tests for witness semantics implementation.

Tests the witness registry, witness predicates, and semantic model features.
"""

import pytest
import z3
from model_checker.theory_lib.exclusion.semantic import (
    WitnessRegistry,
    WitnessSemantics,
    WitnessConstraintGenerator,
    WitnessAwareModel,
    WitnessModelAdapter
)


class TestWitnessRegistry:
    """Test witness registry functionality."""
    
    def test_registry_creation(self):
        """Test witness registry can be created."""
        registry = WitnessRegistry(N=3)
        assert registry is not None
        assert hasattr(registry, 'predicates')
        assert hasattr(registry, 'register_witness_predicates')
        
    def test_register_witness_predicates(self):
        """Test registering witness predicates for a formula."""
        registry = WitnessRegistry(N=3)
        
        # Register predicates for a formula
        formula = "\\func_unineg(p)"
        registry.register_witness_predicates(formula)
        
        # Check predicates were registered
        assert f"{formula}_h" in registry.predicates
        assert f"{formula}_y" in registry.predicates
        
    def test_get_predicate_functions(self):
        """Test getting registered predicate functions."""
        registry = WitnessRegistry(N=3)
        
        formula = "\\func_unineg(q)"
        registry.register_witness_predicates(formula)
        
        # Get predicates
        h_pred = registry.predicates[f"{formula}_h"]
        y_pred = registry.predicates[f"{formula}_y"]
        
        # Test they are Z3 function declarations
        assert isinstance(h_pred, z3.FuncDeclRef)
        assert isinstance(y_pred, z3.FuncDeclRef)


class TestWitnessSemantics:
    """Test witness semantics implementation."""
    
    def test_semantics_creation(self, basic_settings):
        """Test semantics can be created with witness registry."""
        semantics = WitnessSemantics(basic_settings)
        
        assert semantics is not None
        assert hasattr(semantics, 'witness_registry')
        assert isinstance(semantics.witness_registry, WitnessRegistry)
        
    def test_semantics_has_exclusion_relation(self, basic_settings):
        """Test semantics has exclusion relation."""
        semantics = WitnessSemantics(basic_settings)
        
        assert hasattr(semantics, 'excludes')
        # excludes is a Z3 function, not directly callable
        assert semantics.excludes is not None
        
    def test_semantics_model_class(self, basic_settings):
        """Test semantics provides witness-aware model."""
        semantics = WitnessSemantics(basic_settings)
        
        # The semantics should have witness registry and constraint generator
        assert hasattr(semantics, 'witness_registry')
        assert hasattr(semantics, 'constraint_generator')


class TestWitnessConstraintGenerator:
    """Test witness constraint generation."""
    
    def test_constraint_generator_creation(self, basic_settings):
        """Test constraint generator can be created."""
        semantics = WitnessSemantics(basic_settings)
        generator = semantics.constraint_generator
        
        assert generator is not None
        assert hasattr(generator, 'semantics')
        assert generator.semantics is semantics
        
    def test_generate_witness_constraints(self, basic_settings):
        """Test generation of witness constraints."""
        semantics = WitnessSemantics(basic_settings)
        generator = semantics.constraint_generator
        
        # Test basic properties
        assert generator is not None
        assert hasattr(generator, 'generate_witness_constraints')
        assert hasattr(generator, '_witness_constraints_for_state')
        assert hasattr(generator, '_minimality_constraint')
        
        # Register witness predicates
        formula_str = "\\func_unineg(p)"
        h_pred, y_pred = semantics.witness_registry.register_witness_predicates(formula_str)
        
        # Check predicates were created
        assert h_pred is not None
        assert y_pred is not None
        assert isinstance(h_pred, z3.FuncDeclRef)
        assert isinstance(y_pred, z3.FuncDeclRef)


class TestWitnessAwareModel:
    """Test witness-aware model functionality."""
    
    def test_model_adapter_structure(self):
        """Test model adapter class structure."""
        # Just test that the class exists and has expected methods
        assert WitnessModelAdapter is not None
        assert hasattr(WitnessModelAdapter, '__init__')
        assert hasattr(WitnessModelAdapter, 'build_model')
        
    def test_witness_aware_model_creation(self, basic_settings):
        """Test creating witness-aware model."""
        # Create a simple Z3 model
        solver = z3.Solver()
        solver.add(z3.Bool('dummy') == True)
        solver.check()
        z3_model = solver.model()
        
        # Create semantics and witness predicates
        semantics = WitnessSemantics(basic_settings)
        witness_predicates = semantics.witness_registry.predicates
        
        # Create witness-aware model
        model = WitnessAwareModel(z3_model, semantics, witness_predicates)
        
        assert model is not None
        assert hasattr(model, 'has_witness_for')
        assert hasattr(model, 'get_h_witness')
        assert hasattr(model, 'get_y_witness')
        
        # Test has_witness_for returns boolean
        assert isinstance(model.has_witness_for("\\func_unineg(s)"), bool)