"""Output management package for ModelChecker.

This package provides functionality for saving model checking results
in structured formats including markdown documentation and JSON data.
"""

from .manager import OutputManager
from .collectors import ModelDataCollector

__all__ = ['OutputManager', 'ModelDataCollector']