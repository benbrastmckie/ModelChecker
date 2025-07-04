"""
Witness Array Exclusion Theory

This package implements an alternative approach to exclusion semantics that attempts
to solve the Skolem function accessibility problem by using Z3 arrays to store
witness mappings.

Key Components:
- WitnessArraySemantics: Core semantics using array-based witness storage
- WitnessArrayExclusionOperator: Exclusion operator using witness arrays  
- create_operators: Function to create the operator collection

Innovation:
- Replace Skolem functions h_sk and y_sk with Z3 arrays h_array and y_array
- Arrays become part of the model and can be queried after solving
- Maintains exact three-condition exclusion semantics

Expected Outcome:
This approach tests whether the issue is with Skolem function representation
or with the fundamental two-phase architecture separation.
"""

from .semantic import WitnessArraySemantics
from .operators import create_operators, WitnessArrayExclusionOperator

__all__ = [
    'WitnessArraySemantics', 
    'create_operators',
    'WitnessArrayExclusionOperator',
]