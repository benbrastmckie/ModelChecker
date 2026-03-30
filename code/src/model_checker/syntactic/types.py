"""Type definitions for the syntactic package.

This module provides type aliases and protocols for the syntactic
processing components, enabling better type safety and IDE support.
"""

from typing import Union, List, Any, TYPE_CHECKING

if TYPE_CHECKING:
    import z3
    # For type checking, use the z3 type
    AtomType = z3.DatatypeRef
else:
    # At runtime, use Any since actual type depends on backend
    AtomType = Any

# Type aliases for clarity
OperatorName = str
FormulaString = str
PrefixList = List[Union[str, List]]