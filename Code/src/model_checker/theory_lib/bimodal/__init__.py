__version__ = "unknown"

# Import specific items from semantic
from .semantic import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
)

# Import specific items from primitive
from .operators import (
    # primitive operators
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    NecessityOperator,
    PossibilityOperator,
    FutureOperator,
    PastOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
)

from .examples import (
    example_range,
    semantic_theories,
    ) 
