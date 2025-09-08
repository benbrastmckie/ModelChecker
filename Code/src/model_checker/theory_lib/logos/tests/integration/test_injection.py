"""Test Z3 injection for Logos theory.

Following TDD approach - written BEFORE implementing inject_z3_model_values.
Tests verify Logos-specific injection of worlds, verify, falsify relations.
"""

import unittest
from unittest.mock import Mock, MagicMock, patch
import z3
from model_checker.theory_lib.logos.semantic import LogosSemantics
from model_checker import syntactic


class TestLogosInjection(unittest.TestCase):
    """Test Logos theory Z3 injection functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 2}  # 2 atomic states for simplicity
        self.semantics = LogosSemantics(self.settings)
        
        # Create mock model constraints
        self.mock_constraints = Mock()
        self.mock_constraints.all_constraints = []
        self.mock_constraints.syntax = Mock()
        self.mock_constraints.syntax.sentence_letters = []
        self.mock_constraints.settings = {'N': 2}  # Same as self.settings
    
    def test_inject_z3_model_values_exists(self):
        """Test that inject_z3_model_values method exists."""
        self.assertTrue(hasattr(self.semantics, 'inject_z3_model_values'))
        
    def test_inject_world_constraints(self):
        """Test injection of world constraints."""
        # Create a Z3 model with specific world values
        solver = z3.Solver()
        # State 0 is not a world, state 1 is a world
        solver.add(z3.Not(self.semantics.is_world(0)))
        solver.add(self.semantics.is_world(1))
        solver.add(self.semantics.is_world(2))
        solver.add(z3.Not(self.semantics.is_world(3)))
        
        solver.check()
        z3_model = solver.model()
        
        # Inject values (pass same semantics as original)
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have 8 constraints total (4 world + 4 possible)
        self.assertEqual(len(constraints), 8)
        
        # World constraints are complex expressions with And and Implies
        # Count them by structure, not by name
        world_constraints = 0
        for c in constraints:
            c_str = str(c)
            if 'And(' in c_str and 'Implies(' in c_str:
                world_constraints += 1
        
        self.assertEqual(world_constraints, 4)
    
    def test_inject_possible_constraints(self):
        """Test injection of possible state constraints."""
        # Create a Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.possible(0))
        solver.add(z3.Not(self.semantics.possible(1)))
        solver.add(self.semantics.possible(2))
        solver.add(self.semantics.possible(3))
        
        solver.check()
        z3_model = solver.model()
        
        # Inject values (pass same semantics as original)
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have constraints for both world and possible states
        # With N=2, we have 2^2 = 4 states
        # Each state gets both a world and possible constraint
        self.assertEqual(len(constraints), 8)  # 4 world + 4 possible
        
        # Count constraints more carefully - is_world contains "possible" in its definition
        # so we need to be more specific
        world_constraints = 0
        simple_possible_constraints = 0
        
        for c in constraints:
            c_str = str(c)
            # World constraints are more complex - they have And and Implies
            if 'And(' in c_str and 'Implies(' in c_str:
                world_constraints += 1
            # Simple possible constraints are just "possible(n)" or "Not(possible(n))"
            elif c_str in ['possible(0)', 'possible(1)', 'possible(2)', 'possible(3)',
                          'Not(possible(0))', 'Not(possible(1))', 'Not(possible(2))', 'Not(possible(3))']:
                simple_possible_constraints += 1
        
        self.assertEqual(world_constraints, 4)
        self.assertEqual(simple_possible_constraints, 4)
    
    def test_inject_verify_falsify_constraints(self):
        """Test injection of verify/falsify constraints."""
        # Create mock sentence letters
        letter_a = Mock()
        letter_a.sentence_letter = z3.Const('A', syntactic.AtomSort)
        self.mock_constraints.syntax.sentence_letters = [letter_a]
        
        # Create a Z3 model with verify/falsify values
        solver = z3.Solver()
        atom_a = letter_a.sentence_letter
        
        # Set some verify values
        solver.add(self.semantics.verify(0, atom_a))
        solver.add(z3.Not(self.semantics.verify(1, atom_a)))
        solver.add(self.semantics.verify(2, atom_a))
        solver.add(z3.Not(self.semantics.verify(3, atom_a)))
        
        # Set some falsify values
        solver.add(z3.Not(self.semantics.falsify(0, atom_a)))
        solver.add(self.semantics.falsify(1, atom_a))
        solver.add(z3.Not(self.semantics.falsify(2, atom_a)))
        solver.add(self.semantics.falsify(3, atom_a))
        
        solver.check()
        z3_model = solver.model()
        
        # Inject values (pass same semantics as original)
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have verify and falsify constraints
        verify_constraints = [c for c in constraints if 'verify' in str(c)]
        falsify_constraints = [c for c in constraints if 'falsify' in str(c)]
        
        # 4 states * 1 letter = 4 verify and 4 falsify constraints
        self.assertEqual(len(verify_constraints), 4)
        self.assertEqual(len(falsify_constraints), 4)
    
    def test_uses_z3_eval_directly(self):
        """Test that it uses z3_model.eval directly for evaluation."""
        # Create minimal Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        solver.check()
        z3_model = solver.model()
        
        # Inject values (pass same semantics as original)
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Verify constraints were added (indicates evaluation worked)
        self.assertGreater(len(self.mock_constraints.all_constraints), 0)
    
    def test_no_theory_concepts_leak(self):
        """Test that no theory concepts leak into core packages."""
        # This test ensures the method is self-contained
        # The implementation should not require any imports from core packages
        import inspect
        source = inspect.getsource(self.semantics.inject_z3_model_values)
        
        # Should not import from iterate.core or other core packages
        self.assertNotIn('from model_checker.iterate.core', source)
        self.assertNotIn('from model_checker.builder', source)
        # Can import from iterate.validation which is a utility
        # self.assertIn('from model_checker.iterate.validation', source)


if __name__ == '__main__':
    unittest.main()