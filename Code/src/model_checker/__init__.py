# __init__.py
from importlib.metadata import version
try:
    __version__ = version("model-checker")
except ImportError:
    __version__ = "unknown"

# Import model as a whole
from . import model

# Import syntactic as a whole
from . import syntactic

# Import specific items from utils
from .utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)

# Import specific items from utils
from .builder import (
    BuildModule,
    BuildProject,
    BuildExample,
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
    RelevanceOperator,                                    # relevance
    NecessityOperator, PossibilityOperator,               # modal
    CounterfactualOperator, ImpositionOperator,           # counterfactual
)

from .defined import (
    ConditionalOperator, BiconditionalOperator,           # extensional
    DefEssenceOperator, DefGroundOperator,                # constitutive
    MightCounterfactualOperator, MightImpositionOperator, # counterfactual
    
)


# Import specific items from __main__
from .__main__ import (
    ParseFileFlags,
    main,
)

# Define the public API of the package
__all__ = [
    "model", "syntactic",                                       # modules
    "ParseFileFlags",                                           # main.py
    "ForAll", "Exists", "bitvec_to_substates",                  # utils.py
    "BuildModule", "BuildProject", "BuildExample",              # builder.py
    "Semantics", "ImpositionSemantics", "Proposition",          # semantic.py
    "ConditionalOperator", "BiconditionalOperator",
    "DefEssenceOperator", "DefGroundOperator",
    "MightCounterfactualOperator", "MightImpositionOperator",
    "AndOperator", "NegationOperator", "OrOperator",
    "TopOperator", "BotOperator",
    "IdentityOperator", "GroundOperator", "EssenceOperator",
    "RelevanceOperator",
    "NecessityOperator", "PossibilityOperator",
    "CounterfactualOperator", "ImpositionOperator",
    "BuildModule", "BuildExample", "main",
]
