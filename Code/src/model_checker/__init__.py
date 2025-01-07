# __init__.py
from importlib.metadata import version
try:
    __version__ = version("model-checker")
except ImportError:
    __version__ = "unknown"

# Import specific items from utils
from .utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)

# Import model as a whole
from . import model

# Import specific items from utils
from .builder import (
    make_model_for,
    find_max_N,
    run_comparison,
    save_comparisons,
)

# Import specific items from semantic
from .semantic import (
    Semantics,
    ImpositionSemantics,
    Proposition,
)

# Import specific items from primitive
from .primitive import (
    AndOperator, NegationOperator, OrOperator,            # extensional
    TopOperator, BotOperator,                             # top and bottom
    IdentityOperator, GroundOperator, EssenceOperator,    # constitutive
    NecessityOperator, PossibilityOperator,               # modal
    CounterfactualOperator, ImpositionOperator,           # counterfactual
)

# Import specific items from defined
from .defined import (
    ConditionalOperator, BiconditionalOperator,           # extensional
    DefEssenceOperator, DefGroundOperator,                # constitutive
    MightCounterfactualOperator, MightImpositionOperator, # counterfactual
    
)

# Import syntactic as a whole
from . import syntactic

# Define the public API of the package
__all__ = [
    "ForAll", "Exists", "bitvec_to_substates",
    "model",
    "make_model_for", "find_max_N", "run_comparison", "save_comparisons",
    "Semantics", "ImpositionSemantics", "Proposition",
    "ConditionalOperator", "BiconditionalOperator",
    "DefEssenceOperator", "DefGroundOperator",
    "MightCounterfactualOperator", "MightImpositionOperator",
    "AndOperator", "NegationOperator", "OrOperator",
    "TopOperator", "BotOperator",
    "IdentityOperator", "GroundOperator", "EssenceOperator",
    "NecessityOperator", "PossibilityOperator",
    "CounterfactualOperator", "ImpositionOperator",
    "syntactic",
]
