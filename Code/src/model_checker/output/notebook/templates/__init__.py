"""Notebook templates for different theory types.

Each template knows how to generate notebook cells directly from
module variables without any intermediate transformation.
"""

from .base import DirectNotebookTemplate

__all__ = ['DirectNotebookTemplate']