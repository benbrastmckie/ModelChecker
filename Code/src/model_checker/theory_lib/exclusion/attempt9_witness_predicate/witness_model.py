"""
Extended model structure that includes witness functions as predicates.

This module implements the core innovation of Attempt 9: making witness functions
first-class citizens of the model structure, accessible as predicates alongside
the standard verify and exclude relations.
"""

import z3
from typing import Dict, Optional, Set, Tuple, Any
from model_checker.model import ModelDefaults


class WitnessAwareModel:
    """
    Model that treats witness functions as first-class predicates.
    
    In addition to standard predicates (verify, exclude, fusion, etc.),
    this model includes witness predicates for exclusion formulas.
    """
    
    def __init__(self, z3_model, semantics, witness_predicates):
        self.z3_model = z3_model
        self.semantics = semantics
        self.witness_predicates = witness_predicates
        # Cache for evaluated predicates
        self._cache = {}
        
    def eval(self, expr):
        """Standard Z3 model evaluation."""
        return self.z3_model.eval(expr)
        
    def has_witness_for(self, formula_str: str) -> bool:
        """Check if model has witness predicates for given formula."""
        return f"{formula_str}_h" in self.witness_predicates
        
    def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
        """
        Get h(state) for the given formula.
        This is the key method that makes witnesses accessible.
        """
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None
            
        # Query the witness predicate
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(h_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
        
    def get_y_witness(self, formula_str: str, state: int) -> Optional[int]:
        """Get y(state) for the given formula."""
        y_pred = self.witness_predicates.get(f"{formula_str}_y")
        if y_pred is None:
            return None
            
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(y_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
        
    def get_all_witness_values(self, formula_str: str) -> Dict[int, Tuple[int, int]]:
        """Get all witness values for a formula."""
        witness_map = {}
        
        for state in range(2**self.semantics.N):
            h_val = self.get_h_witness(formula_str, state)
            y_val = self.get_y_witness(formula_str, state)
            if h_val is not None and y_val is not None:
                witness_map[state] = (h_val, y_val)
                
        return witness_map


class WitnessPredicateRegistry:
    """
    Registry for all witness predicates in the model.
    Tracks which formulas have associated witness functions.
    """
    
    def __init__(self, N: int):
        self.N = N
        self.predicates: Dict[str, z3.FuncDeclRef] = {}
        self.formula_mapping: Dict[str, Set[str]] = {}
        
    def register_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """
        Register witness predicates h and y for a formula.
        Returns (h_predicate, y_predicate).
        """
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"
        
        # Create Z3 functions for witness predicates
        h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
        y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
        
        self.predicates[h_name] = h_pred
        self.predicates[y_name] = y_pred
        
        self.formula_mapping[formula_str] = {h_name, y_name}
        
        return h_pred, y_pred
        
    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Get all registered witness predicates."""
        return self.predicates.copy()
        
    def clear(self):
        """Clear all registered predicates."""
        self.predicates.clear()
        self.formula_mapping.clear()