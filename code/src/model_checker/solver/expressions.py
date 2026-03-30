"""Expression construction re-exports from active backend.

This module provides formula construction functions (And, Or, BitVec, etc.)
from the currently active solver backend.

Usage:
    from model_checker.solver.expressions import And, Or, BitVec, Not

The actual implementation comes from either z3 or cvc5.pythonic
depending on the active backend.
"""

from typing import Any
from .registry import get_active_backend


def _get_backend_module():
    """Get the appropriate backend module for expression construction."""
    backend = get_active_backend()
    if backend == "z3":
        import z3
        return z3
    elif backend == "cvc5":
        try:
            import cvc5.pythonic as cvc5_pythonic
            return cvc5_pythonic
        except ImportError:
            raise ImportError(
                "cvc5 not installed. Install with: pip install cvc5"
            )
    raise ValueError(f"Unknown backend: {backend}")


# Boolean operations
def And(*args: Any) -> Any:
    """Create a conjunction (logical AND) of expressions."""
    return _get_backend_module().And(*args)


def Or(*args: Any) -> Any:
    """Create a disjunction (logical OR) of expressions."""
    return _get_backend_module().Or(*args)


def Not(expr: Any) -> Any:
    """Create a negation of an expression."""
    return _get_backend_module().Not(expr)


def Implies(a: Any, b: Any) -> Any:
    """Create an implication expression."""
    return _get_backend_module().Implies(a, b)


def Xor(*args: Any) -> Any:
    """Create an exclusive OR of expressions."""
    return _get_backend_module().Xor(*args)


def If(cond: Any, then_expr: Any, else_expr: Any) -> Any:
    """Create a conditional expression."""
    return _get_backend_module().If(cond, then_expr, else_expr)


# Boolean constants and variables
def Bool(name: str) -> Any:
    """Create a boolean variable."""
    return _get_backend_module().Bool(name)


def BoolVal(val: bool) -> Any:
    """Create a boolean constant."""
    return _get_backend_module().BoolVal(val)


def Bools(names: str) -> Any:
    """Create multiple boolean variables from space-separated names."""
    return _get_backend_module().Bools(names)


# Bitvector operations
def BitVec(name: str, size: int) -> Any:
    """Create a bitvector variable."""
    return _get_backend_module().BitVec(name, size)


def BitVecVal(val: int, size: int) -> Any:
    """Create a bitvector constant."""
    return _get_backend_module().BitVecVal(val, size)


def BitVecs(names: str, size: int) -> Any:
    """Create multiple bitvector variables from space-separated names."""
    return _get_backend_module().BitVecs(names, size)


def Concat(*args: Any) -> Any:
    """Concatenate bitvectors."""
    return _get_backend_module().Concat(*args)


def Extract(high: int, low: int, bv: Any) -> Any:
    """Extract bits [high:low] from a bitvector."""
    return _get_backend_module().Extract(high, low, bv)


def ZeroExt(n: int, bv: Any) -> Any:
    """Zero-extend a bitvector by n bits."""
    return _get_backend_module().ZeroExt(n, bv)


def SignExt(n: int, bv: Any) -> Any:
    """Sign-extend a bitvector by n bits."""
    return _get_backend_module().SignExt(n, bv)


def LShR(a: Any, b: Any) -> Any:
    """Logical shift right."""
    return _get_backend_module().LShR(a, b)


def RotateLeft(a: Any, b: int) -> Any:
    """Rotate left."""
    return _get_backend_module().RotateLeft(a, b)


def RotateRight(a: Any, b: int) -> Any:
    """Rotate right."""
    return _get_backend_module().RotateRight(a, b)


# Unsigned comparisons
def ULT(a: Any, b: Any) -> Any:
    """Unsigned less than."""
    return _get_backend_module().ULT(a, b)


def ULE(a: Any, b: Any) -> Any:
    """Unsigned less than or equal."""
    return _get_backend_module().ULE(a, b)


def UGT(a: Any, b: Any) -> Any:
    """Unsigned greater than."""
    return _get_backend_module().UGT(a, b)


def UGE(a: Any, b: Any) -> Any:
    """Unsigned greater than or equal."""
    return _get_backend_module().UGE(a, b)


# Arithmetic operations
def Int(name: str) -> Any:
    """Create an integer variable."""
    return _get_backend_module().Int(name)


def IntVal(val: int) -> Any:
    """Create an integer constant."""
    return _get_backend_module().IntVal(val)


def Real(name: str) -> Any:
    """Create a real variable."""
    return _get_backend_module().Real(name)


def RealVal(val: float) -> Any:
    """Create a real constant."""
    return _get_backend_module().RealVal(val)


# Quantifiers
def ForAll(vars: Any, body: Any) -> Any:
    """Universal quantification."""
    return _get_backend_module().ForAll(vars, body)


def Exists(vars: Any, body: Any) -> Any:
    """Existential quantification."""
    return _get_backend_module().Exists(vars, body)


# Sorts
def BitVecSort(size: int) -> Any:
    """Create a bitvector sort."""
    return _get_backend_module().BitVecSort(size)


def BoolSort() -> Any:
    """Get the boolean sort."""
    return _get_backend_module().BoolSort()


def IntSort() -> Any:
    """Get the integer sort."""
    return _get_backend_module().IntSort()


def RealSort() -> Any:
    """Get the real sort."""
    return _get_backend_module().RealSort()


# Uninterpreted sorts and functions
def DeclareSort(name: str) -> Any:
    """Declare an uninterpreted sort."""
    return _get_backend_module().DeclareSort(name)


def Function(name: str, *sorts: Any) -> Any:
    """Declare an uninterpreted function."""
    return _get_backend_module().Function(name, *sorts)


def Const(name: str, sort: Any) -> Any:
    """Create a constant of the given sort."""
    return _get_backend_module().Const(name, sort)


# Arrays
def Array(name: str, idx_sort: Any, elem_sort: Any) -> Any:
    """Create an array variable."""
    return _get_backend_module().Array(name, idx_sort, elem_sort)


def Select(array: Any, idx: Any) -> Any:
    """Select an element from an array."""
    return _get_backend_module().Select(array, idx)


def Store(array: Any, idx: Any, val: Any) -> Any:
    """Store a value in an array."""
    return _get_backend_module().Store(array, idx, val)


def K(sort: Any, val: Any) -> Any:
    """Create a constant array."""
    return _get_backend_module().K(sort, val)


# Utility functions
def simplify(expr: Any) -> Any:
    """Simplify an expression."""
    return _get_backend_module().simplify(expr)


def substitute(expr: Any, *substitutions: Any) -> Any:
    """Substitute variables in an expression."""
    return _get_backend_module().substitute(expr, *substitutions)


# Result constants
def sat() -> Any:
    """Get the sat result constant."""
    return _get_backend_module().sat


def unsat() -> Any:
    """Get the unsat result constant."""
    return _get_backend_module().unsat


def unknown() -> Any:
    """Get the unknown result constant."""
    return _get_backend_module().unknown


# Set operations
def EmptySet(sort: Any) -> Any:
    """Create an empty set of the given element sort."""
    return _get_backend_module().EmptySet(sort)


def SetAdd(s: Any, elem: Any) -> Any:
    """Add an element to a set."""
    return _get_backend_module().SetAdd(s, elem)


def IsMember(elem: Any, s: Any) -> Any:
    """Check if element is member of set."""
    return _get_backend_module().IsMember(elem, s)


def SetSort(elem_sort: Any) -> Any:
    """Create a set sort with the given element sort."""
    return _get_backend_module().SetSort(elem_sort)


def is_const(expr: Any) -> bool:
    """Check if an expression is a constant (nullary function application)."""
    return _get_backend_module().is_const(expr)
