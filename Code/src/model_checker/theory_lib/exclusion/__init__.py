__version__ = "0.0.1"

# Import specific items from semantic
from .semantic import (
    ExclusionSemantics,
    UnilateralProposition,
)

# Import specific items from primitive
from .operators import (
    UniAndOperator, UniOrOperator, ExclusionOperator, # extensional
    UniIdentityOperator, # constitutive
)

from .examples import (
    example_range,
    semantic_theories,
    ) 
