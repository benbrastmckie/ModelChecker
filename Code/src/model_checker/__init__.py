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

# Import syntactic as a whole
from . import syntactic

# Import specific items from utils
from .builder import (
    make_model_for,
    try_single_N,
    translate,
    # run_comparison, # update
    # save_comparisons, # update
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
    BuildModule,
    BuildExample,
    main,
)

# Define the public API of the package
__all__ = [
    "model", "syntactic",
    "ForAll", "Exists", "bitvec_to_substates",
    "make_model_for", "try_single_N", "translate", #"run_comparison", "save_comparisons",
    "Semantics", "ImpositionSemantics", "Proposition",
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
