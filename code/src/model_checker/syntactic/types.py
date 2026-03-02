"""Type definitions for the syntactic package.

This module provides type aliases and protocols for the syntactic 
processing components, enabling better type safety and IDE support.
"""

from typing import Union, List, Dict, Any, Optional, Protocol
import z3

# Type aliases for clarity
AtomType = z3.DatatypeRef
OperatorName = str
FormulaString = str
PrefixList = List[Union[str, List]]


class ISemantics(Protocol):
    """Protocol for semantic implementations.
    
    All semantic theory implementations should provide an evaluate method
    that takes arguments and returns a Z3 boolean reference.
    """
    
    def evaluate(self, *args) -> z3.BoolRef:
        """Evaluate the semantic operation.
        
        Args:
            *args: Arguments for semantic evaluation
            
        Returns:
            Z3 boolean reference representing the evaluation result
        """
        ...