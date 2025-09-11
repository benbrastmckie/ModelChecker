"""
Type definitions for the utils package.

This module provides type aliases and protocol definitions used throughout
the utils package to ensure type safety and clear interfaces.
"""

from typing import TypeVar, Union, Any, Protocol, Optional, Dict, List, Tuple
from pathlib import Path
import z3

# Type variables for generic functions
T = TypeVar('T')

# Z3 type aliases
Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.SeqRef, z3.BitVecRef]
Z3Sort = Union[z3.BoolSort, z3.ArithSort, z3.SeqSort, z3.BitVecSort]

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