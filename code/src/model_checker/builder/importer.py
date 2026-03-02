"""Module importing abstraction for dependency injection.

This module provides import operations as an injectable dependency,
enabling better testability and separation of concerns.
"""

import sys
import importlib.util
from types import ModuleType
from typing import Protocol

from .errors import PackageImportError


class IImporter(Protocol):
    """Protocol for module importing operations."""
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import a module from the given path."""
        ...


class RealImporter:
    """Real module importer implementation.
    
    This is the production implementation that performs
    actual module importing using importlib.
    """
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import a module from the given path.
        
        Args:
            name: Module name
            path: Path to module file
            
        Returns:
            The imported module
            
        Raises:
            PackageImportError: If module cannot be imported
        """
        try:
            # Create module spec
            spec = importlib.util.spec_from_file_location(name, path)
            if spec is None:
                raise PackageImportError(
                    f"Cannot create spec for module '{name}'",
                    f"Path: {path}",
                    "Ensure path points to a valid Python file"
                )
            
            # Create module from spec
            module = importlib.util.module_from_spec(spec)
            
            # Add to sys.modules
            sys.modules[name] = module
            
            # Execute module
            if spec.loader is None:
                raise PackageImportError(
                    f"No loader available for module '{name}'",
                    f"Path: {path}",
                    "Module spec is invalid"
                )
                
            spec.loader.exec_module(module)
            
            return module
            
        except FileNotFoundError as e:
            raise PackageImportError(
                f"Module file not found: {path}",
                f"Error: {str(e)}",
                "Check that the file path is correct"
            )
        except Exception as e:
            raise PackageImportError(
                f"Failed to import module '{name}'",
                f"Path: {path}, Error: {str(e)}",
                "Check module syntax and dependencies"
            )