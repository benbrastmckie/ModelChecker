"""Tests for Z3 helper utilities."""

import pytest
import z3

from model_checker.utils.z3_helpers import ForAll, Exists


class TestForAll:
    """Test ForAll quantification function."""
    
    def test_forall_single_variable(self):
        """Test universal quantification with single variable."""
        x = z3.BitVec('x', 2)
        # ForAll x: x == 0 or x == 1 or x == 2 or x == 3
        # This should be True since we're checking all possible values
        formula = z3.Or(x == 0, x == 1, x == 2, x == 3)
        result = ForAll(x, formula)
        
        solver = z3.Solver()
        solver.add(result)
        assert solver.check() == z3.sat
    
    def test_forall_contradiction(self):
        """Test ForAll with contradictory formula."""
        x = z3.BitVec('x', 2)
        # ForAll x: x == 0 (which is false for x=1,2,3)
        formula = x == 0
        result = ForAll(x, formula)
        
        solver = z3.Solver()
        solver.add(result)
        assert solver.check() == z3.unsat
    
    def test_forall_multiple_variables(self):
        """Test ForAll with multiple variables."""
        x = z3.BitVec('x', 2)
        y = z3.BitVec('y', 2)
        # ForAll x,y: (x == y) => (x & y == x)
        # This is a tautology: if x equals y, then x AND y equals x
        formula = z3.Implies(x == y, (x & y) == x)
        result = ForAll([x, y], formula)
        
        solver = z3.Solver()
        solver.add(result)
        # This should be satisfiable since it's a tautology
        assert solver.check() == z3.sat


class TestExists:
    """Test Exists quantification function."""
    
    def test_exists_single_variable(self):
        """Test existential quantification with single variable."""
        x = z3.BitVec('x', 2)
        # Exists x: x == 2
        formula = x == 2
        result = Exists(x, formula)
        
        solver = z3.Solver()
        solver.add(result)
        assert solver.check() == z3.sat
    
    def test_exists_no_solution(self):
        """Test Exists with no solution."""
        x = z3.BitVec('x', 2)
        # Exists x: x > 3 (impossible for 2-bit value)
        formula = z3.UGT(x, 3)
        result = Exists(x, formula)
        
        solver = z3.Solver()
        solver.add(result)
        assert solver.check() == z3.unsat
    
    def test_exists_multiple_variables(self):
        """Test Exists with multiple variables."""
        x = z3.BitVec('x', 2)
        y = z3.BitVec('y', 2)
        # Exists x,y: x + y == 3
        formula = x + y == 3
        result = Exists([x, y], formula)
        
        solver = z3.Solver()
        solver.add(result)
        assert solver.check() == z3.sat


class TestMixedQuantifiers:
    """Test mixed quantifier scenarios."""
    
    def test_forall_exists_nesting(self):
        """Test ForAll and Exists interaction."""
        x = z3.BitVec('x', 2)
        
        # ForAll x: x == 0 or x == 1 or x == 2 or x == 3
        forall_result = ForAll(x, z3.Or(x == 0, x == 1, x == 2, x == 3))
        
        # Exists x: x == 1
        exists_result = Exists(x, x == 1)
        
        # Both should be satisfiable
        solver = z3.Solver()
        solver.add(z3.And(forall_result, exists_result))
        assert solver.check() == z3.sat


if __name__ == "__main__":
    pytest.main([__file__, "-v"])