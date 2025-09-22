"""File system abstraction for dependency injection.

This module provides file system operations as an injectable dependency,
enabling better testability and separation of concerns.
"""

import os
from typing import Protocol


class IFileSystem(Protocol):
    """Protocol for file system operations."""
    
    def exists(self, path: str) -> bool:
        """Check if path exists."""
        ...
    
    def read(self, path: str) -> str:
        """Read file contents."""
        ...
    
    def is_file(self, path: str) -> bool:
        """Check if path is a file."""
        ...
    
    def is_dir(self, path: str) -> bool:
        """Check if path is a directory."""
        ...
    
    def dirname(self, path: str) -> str:
        """Get directory name of path."""
        ...


class RealFileSystem:
    """Real file system implementation.
    
    This is the production implementation that performs
    actual file system operations.
    """
    
    def exists(self, path: str) -> bool:
        """Check if path exists."""
        return os.path.exists(path)
    
    def read(self, path: str) -> str:
        """Read file contents."""
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def is_file(self, path: str) -> bool:
        """Check if path is a file."""
        return os.path.isfile(path)
    
    def is_dir(self, path: str) -> bool:
        """Check if path is a directory."""
        return os.path.isdir(path)
    
    def dirname(self, path: str) -> str:
        """Get directory name of path."""
        return os.path.dirname(path)