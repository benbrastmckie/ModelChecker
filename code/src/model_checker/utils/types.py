"""
Type definitions for the utils package.

This module provides type aliases and protocol definitions used throughout
the utils package to ensure type safety and clear interfaces.
"""

from typing import TypeVar, Union, Any, Protocol, Optional, Dict, List, Tuple, TYPE_CHECKING
from pathlib import Path

# Type variables for generic functions
T = TypeVar('T')

# Use solver layer type aliases when possible, with z3 fallback for TYPE_CHECKING
if TYPE_CHECKING:
    import z3
    Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.SeqRef, z3.BitVecRef]
    Z3Sort = Union[z3.BoolSortRef, z3.ArithSortRef, z3.SeqSortRef, z3.BitVecSortRef]
else:
    # Runtime: use Any since actual types come from active backend
    from model_checker.solver.types import SolverExpr, SolverSort
    Z3Expr = SolverExpr
    Z3Sort = SolverSort

# Path-like types
PathLike = Union[str, Path]

# Configuration and data structures
ConfigDict = Dict[str, Any]
TableRow = List[Any]
TableData = List[TableRow]

# Version tuple type
VersionTuple = Tuple[int, int, int]

# Color codes for formatting
ColorCode = str

# Test-related types
TestResult = Any
MockObject = Any