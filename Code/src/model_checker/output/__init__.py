"""Output management package for ModelChecker.

This package provides functionality for saving model checking results
in structured formats including markdown documentation, JSON data, and
Jupyter notebooks.
"""

from .manager import OutputManager
from .collectors import ModelDataCollector
from .formatters import (
    MarkdownFormatter,
    JSONFormatter,
    ANSIToMarkdown
)
from .config import OutputConfig
from .sequential import SequentialSaveManager
# Backward compatibility alias
InteractiveSaveManager = SequentialSaveManager
from .input_provider import InputProvider, ConsoleInputProvider, MockInputProvider
from .prompts import prompt_yes_no, prompt_choice

# Notebook generation subpackage
from .notebook import StreamingNotebookGenerator, NotebookWriter, TemplateLoader

__all__ = [
    'OutputManager',
    'OutputConfig',
    'ModelDataCollector',
    'MarkdownFormatter',
    'JSONFormatter',
    'ANSIToMarkdown',
    'SequentialSaveManager',
    'InteractiveSaveManager',  # Backward compatibility
    'InputProvider',
    'ConsoleInputProvider',
    'MockInputProvider',
    'prompt_yes_no',
    'prompt_choice',
    # Notebook exports
    'StreamingNotebookGenerator',
    'NotebookWriter',
    'TemplateLoader',
]