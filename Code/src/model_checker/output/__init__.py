"""Output management package for ModelChecker.

This package provides functionality for saving model checking results
in structured formats including markdown documentation and JSON data.
"""

from .manager import OutputManager
from .collectors import ModelDataCollector
from .formatters import MarkdownFormatter, ANSIToMarkdown
from .prompts import prompt_yes_no, prompt_choice

__all__ = [
    'OutputManager', 
    'ModelDataCollector', 
    'MarkdownFormatter', 
    'ANSIToMarkdown',
    'prompt_yes_no',
    'prompt_choice'
]