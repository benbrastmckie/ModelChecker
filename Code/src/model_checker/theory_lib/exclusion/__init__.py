__version__ = "unknown"


# Define the public API of the package
__all__ = [
    "ExclusionSemantics", "UnilateralProposition", "ExclusionStructure",  # semantic
    "exclusion_operators",  # operators
]

# Import specific items from semantic
from .semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)

# Import all operators
from .operators import exclusion_operators
