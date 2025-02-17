__version__ = "0.0.1"

# Import specific items from semantic
from .semantic import (
    Semantics,
    ImpositionSemantics,
    Proposition,
)

# Import specific items from primitive
from .operators import (
    # primitive operators
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    CounterfactualOperator,
    NecessityOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    MightCounterfactualOperator,
    DefPossibilityOperator,
)

from .examples import (
    example_range,
    semantic_theories,
    ) 
