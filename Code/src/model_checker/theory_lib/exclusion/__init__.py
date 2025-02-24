__version__ = "0.0.1"


# Define the public API of the package
__all__ = [
    "ExclusionSemantics", "UnilateralProposition", "ExclusionStructure",  # semantic
    "exclusion_operators",  # operators
    "example_range"  # examples
]

# Import specific items from semantic
from .semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)

# Import all operators
from .operators import exclusion_operators

from .examples import example_range
