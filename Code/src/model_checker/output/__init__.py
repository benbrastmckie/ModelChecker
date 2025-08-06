"""Output management package for ModelChecker.

This package provides functionality for saving model checking results
in structured formats including markdown documentation and JSON data.
"""

from .manager import OutputManager
from .collectors import ModelDataCollector
from .formatters import MarkdownFormatter, ANSIToMarkdown
from .prompts import prompt_yes_no, prompt_choice
from .interactive import InteractiveSaveManager
from .input_provider import InputProvider, ConsoleInputProvider, MockInputProvider

__all__ = [
    'OutputManager', 
    'ModelDataCollector', 
    'MarkdownFormatter', 
    'ANSIToMarkdown',
    'prompt_yes_no',
    'prompt_choice',
    'InteractiveSaveManager',
    'InputProvider',
    'ConsoleInputProvider',
    'MockInputProvider'
]