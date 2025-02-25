__version__ = "0.0.1"

# Define the public API of the package
__all__ = [
    "ImpositionSemantics",  # semantic
    "imposition_operators",  # operators
]

# Import specific items from semantic
from .semantic import (
    ImpositionSemantics,
)

# Import all operators
from .operators import imposition_operators

# NOTE: this will cause circular imports
# from .examples import example_range
