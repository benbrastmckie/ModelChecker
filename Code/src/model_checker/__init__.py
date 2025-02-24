# __init__.py
from importlib.metadata import version
try:
    __version__ = version("model-checker")
except ImportError:
    __version__ = "unknown"


# Define the public API of the package
__all__ = [
    "model", "syntactic",                           # modules
    "ParseFileFlags",                               # main.py
    "ForAll", "Exists", "bitvec_to_substates",      # utils.py
    "BuildModule", "BuildProject", "BuildExample",  # builder.py
    "BuildModule", "BuildExample", "main",
]

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

# Import specific items from __main__
from .__main__ import (
    ParseFileFlags,
    main,
)
