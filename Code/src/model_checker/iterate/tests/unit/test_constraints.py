"""Tests for the constraints module (constraint generation and management)."""

import pytest
import z3
from unittest.mock import Mock, patch, MagicMock
from model_checker.iterate.constraints import ConstraintGenerator


class TestConstraintGenerator:
    """Test cases for ConstraintGenerator functionality."""
    
    def test_initialization(self):
        """Test constraint generator initialization."""
        # Create mock build example
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = [z3.BoolVal(True)]
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        assert gen.build_example == mock_example
        assert isinstance(gen.solver, z3.Solver)
    
    def test_initialization_with_no_solver(self):
        """Test initialization when structure has no solver."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = None
        mock_example.model_structure.stored_solver = None
        mock_example.settings = {}
        
        # Should raise RuntimeError when no solver is available
        with pytest.raises(RuntimeError, match="No solver available"):
            gen = ConstraintGenerator(mock_example)
    
    def test_create_extended_constraints(self):
        """Test creation of extended constraints."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = [z3.BoolVal(True)]
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        # Mock the difference constraint creation
        with patch.object(gen, '_create_difference_constraint', return_value=z3.BoolVal(False)):
            # Create extended constraints with previous models
            prev_models = [Mock(), Mock()]
            extended = gen.create_extended_constraints(prev_models)
            
            # Should create one difference constraint per previous model
            assert len(extended) == 2  # One constraint per previous model
            assert all(z3.is_false(constraint) for constraint in extended)
    
    def test_check_satisfiability(self):
        """Test satisfiability checking."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        # Test with satisfiable constraints
        constraints = [z3.BoolVal(True)]
        result = gen.check_satisfiability(constraints)
        assert result == 'sat'
        
        # Test with unsatisfiable constraints
        constraints = [z3.BoolVal(False)]
        result = gen.check_satisfiability(constraints)
        assert result == 'unsat'
    
    def test_get_model(self):
        """Test model retrieval."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        # Add satisfiable constraint and check
        gen.solver.add(z3.BoolVal(True))
        gen.solver.check()
        
        # Get model
        model = gen.get_model()
        assert model is not None
        assert hasattr(model, 'eval')
    
    def test_create_difference_constraint_basic(self):
        """Test basic difference constraint creation."""
        # Create mock build example with semantics
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {'N': 3}
        
        # Mock semantics methods in the correct location
        mock_semantics = Mock()
        mock_semantics.is_world = Mock(side_effect=lambda s: z3.Bool(f"is_world_{s}"))
        mock_semantics.possible = Mock(side_effect=lambda s: z3.Bool(f"possible_{s}"))
        mock_semantics.all_states = [0, 1, 2, 3]
        mock_example.model_constraints.semantics = mock_semantics
        
        gen = ConstraintGenerator(mock_example)
        
        # Create mock previous models
        mock_model = Mock()
        mock_model.eval = Mock(side_effect=lambda expr, **kwargs: z3.BoolVal(True))
        
        # Create difference constraint
        constraint = gen._create_difference_constraint([mock_model])
        
        # Should create a non-trivial constraint
        assert constraint is not None
        assert not z3.is_true(constraint)  # Not just "True"
    
    def test_create_difference_constraint_empty(self):
        """Test difference constraint with no previous models."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        # No previous models should return None (no restriction)
        constraint = gen._create_difference_constraint([])
        assert constraint is None
    
    def test_create_non_isomorphic_constraint(self):
        """Test non-isomorphic constraint creation."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {'N': 2}
        
        # Mock semantics in the correct location
        mock_semantics = Mock()
        mock_semantics.all_states = [0, 1]
        mock_semantics.is_world = Mock(side_effect=lambda s: z3.Bool(f"is_world_{s}"))
        mock_example.model_constraints.semantics = mock_semantics
        
        gen = ConstraintGenerator(mock_example)
        
        # Mock Z3 model
        mock_model = Mock()
        mock_model.eval = Mock(return_value=z3.BoolVal(True))
        
        # Create constraint
        constraint = gen._create_non_isomorphic_constraint(mock_model)
        
        # Should create a constraint
        assert constraint is not None
    
    def test_create_stronger_constraint(self):
        """Test stronger constraint creation for escaping isomorphism."""
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.settings = {'N': 2}
        
        # Mock semantics in the correct location
        mock_semantics = Mock()
        mock_semantics.sentence_letters = ['P', 'Q']
        mock_semantics.all_states = [0, 1]
        mock_semantics.is_world = Mock(side_effect=lambda s: z3.Bool(f"is_world_{s}"))
        mock_semantics.verify = Mock(side_effect=lambda a, s: z3.Bool(f"verify_{a}_{s}"))
        mock_semantics.falsify = Mock(side_effect=lambda a, s: z3.Bool(f"falsify_{a}_{s}"))
        mock_example.model_constraints.semantics = mock_semantics
        
        gen = ConstraintGenerator(mock_example)
        
        # Mock isomorphic model
        mock_model = Mock()
        mock_model.eval = Mock(return_value=z3.BoolVal(False))
        
        # Create stronger constraint
        constraint = gen.create_stronger_constraint(mock_model)
        
        # Should create a constraint
        assert constraint is not None
    
    def test_preserve_original_constraints(self):
        """Test that original constraints are preserved in the solver."""
        # Create specific original constraints
        x = z3.Bool('x')
        y = z3.Bool('y')
        original_constraints = [x == True, y == False]
        
        # Create solver with original constraints
        solver = z3.Solver()
        for c in original_constraints:
            solver.add(c)
        
        mock_example = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = original_constraints
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = solver
        mock_example.settings = {}
        
        gen = ConstraintGenerator(mock_example)
        
        # Original constraints should be preserved in the persistent solver
        solver_assertions = gen.solver.assertions()
        assert len(solver_assertions) == len(original_constraints)
        for orig in original_constraints:
            assert any(str(orig) == str(assertion) for assertion in solver_assertions)