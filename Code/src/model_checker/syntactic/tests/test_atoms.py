"""Tests for Z3 atom integration."""

import pytest
import z3

from model_checker.syntactic.atoms import AtomSort, AtomVal


class TestAtomSort:
    """Test the AtomSort declaration."""
    
    def test_atom_sort_exists(self):
        """Test that AtomSort is properly declared."""
        assert AtomSort is not None
        assert isinstance(AtomSort, z3.SortRef)
        
    def test_atom_sort_name(self):
        """Test that AtomSort has the correct name."""
        assert str(AtomSort) == "AtomSort"


class TestAtomVal:
    """Test the AtomVal factory function."""
    
    def test_atom_val_creation(self):
        """Test basic AtomVal creation."""
        atom0 = AtomVal(0)
        assert atom0 is not None
        assert isinstance(atom0, z3.ExprRef)
        
    def test_atom_val_sort(self):
        """Test that AtomVal creates constants of AtomSort."""
        atom = AtomVal(42)
        assert atom.sort() == AtomSort
        
    def test_atom_val_unique_names(self):
        """Test that different indices create different atoms."""
        atom0 = AtomVal(0)
        atom1 = AtomVal(1)
        atom42 = AtomVal(42)
        
        assert str(atom0) == "AtomSort!val!0"
        assert str(atom1) == "AtomSort!val!1"
        assert str(atom42) == "AtomSort!val!42"
        
    def test_atom_val_consistency(self):
        """Test that same index creates equivalent atoms."""
        atom1a = AtomVal(5)
        atom1b = AtomVal(5)
        
        # They should have the same string representation
        assert str(atom1a) == str(atom1b)
        
        # But they are different objects (Z3 creates new ones)
        assert atom1a is not atom1b
        
    def test_atom_val_in_constraints(self):
        """Test that atoms can be used in Z3 constraints."""
        atom0 = AtomVal(0)
        atom1 = AtomVal(1)
        
        # Create a simple constraint
        constraint = atom0 == atom1
        assert isinstance(constraint, z3.BoolRef)
        
        # Test in solver
        solver = z3.Solver()
        solver.add(atom0 == atom0)  # Tautology
        assert solver.check() == z3.sat
        
    def test_atom_val_negative_index(self):
        """Test that negative indices work correctly."""
        atom_neg = AtomVal(-1)
        assert str(atom_neg) == "AtomSort!val!-1"
        assert atom_neg.sort() == AtomSort