"""Type definitions for solver abstraction layer.

This module provides type aliases that work with both Z3 and cvc5 backends.
Uses TYPE_CHECKING guards to avoid runtime import issues.
"""

from typing import TYPE_CHECKING, Union, TypeVar

if TYPE_CHECKING:
    import z3
    # Z3 expression types for static type checking
    SolverExpr = Union[z3.BoolRef, z3.BitVecRef, z3.ArithRef, z3.ExprRef]
    SolverModel = z3.ModelRef
    SolverSort = z3.SortRef
    BoolExpr = z3.BoolRef
    BitVecExpr = z3.BitVecRef
    ArithExpr = z3.ArithRef
else:
    # Runtime fallback - use generic object types
    SolverExpr = object
    SolverModel = object
    SolverSort = object
    BoolExpr = object
    BitVecExpr = object
    ArithExpr = object

# Type variable for expressions (useful in generic functions)
ExprType = TypeVar("ExprType")

# Backend name type
BackendName = str  # Literal["z3", "cvc5"] when we have more backends

# Constraint label type for unsat cores
ConstraintLabel = str
