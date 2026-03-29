"""Type definitions for the syntactic package.

This module provides type aliases and protocols for the syntactic 
processing components, enabling better type safety and IDE support.
"""

from typing import Union, List
import z3

# Type aliases for clarity
AtomType = z3.DatatypeRef
OperatorName = str
FormulaString = str
PrefixList = List[Union[str, List]]