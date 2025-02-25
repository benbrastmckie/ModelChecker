__version__ = "0.0.1"

# Define the public API of the package
__all__ = [
    "Semantics", "Proposition", "ModelStructure",  # semantic
    "default_operators",  # operators
]

# Import specific items from semantic
from .semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import all operators
from .operators import default_operators

# NOTE: this will cause circular imports
# from .examples import example_range
