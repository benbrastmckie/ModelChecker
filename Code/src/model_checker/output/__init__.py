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
from .config import OutputConfig, create_output_config
from .sequential_manager import SequentialSaveManager
from .input_provider import InputProvider, ConsoleInputProvider, MockInputProvider
from .prompts import prompt_yes_no, prompt_choice

# Notebook generation subpackage
from .notebook import StreamingNotebookGenerator, NotebookWriter, TemplateLoader

__all__ = [
    'OutputManager',
    'OutputConfig',
    'create_output_config',
    'ModelDataCollector',
    'MarkdownFormatter',
    'JSONFormatter',
    'ANSIToMarkdown',
    'SequentialSaveManager',
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