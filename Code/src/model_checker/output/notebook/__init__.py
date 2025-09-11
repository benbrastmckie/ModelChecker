"""Streaming notebook generation package.

This package provides memory-efficient, scalable notebook generation using
template decomposition and streaming output. It replaces the marker-based
approach with a cleaner streaming architecture.
"""

from .streaming_generator import StreamingNotebookGenerator
from .notebook_writer import NotebookWriter
from .template_loader import TemplateLoader

# Keep old generator for backwards compatibility during transition
from .generator import IndependentNotebookGenerator

__all__ = ['StreamingNotebookGenerator', 'NotebookWriter', 'TemplateLoader', 'IndependentNotebookGenerator']