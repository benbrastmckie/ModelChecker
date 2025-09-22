"""Import strategy implementations using Strategy pattern.

This module contains different strategies for importing modules,
removing complex conditionals from the loader.

NO BACKWARDS COMPATIBILITY: No LegacyImportStrategy exists.
Only clean, modern import strategies are provided.
"""

import os
import sys
import importlib
from types import ModuleType
from typing import Protocol
from pathlib import Path

from .errors import PackageImportError


class ImportStrategy(Protocol):
    """Protocol for import strategies.
    
    Each strategy handles a specific type of module import.
    NO OPTIONAL PARAMETERS allowed in any implementation.
    """
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import module using this strategy.
        
        Args:
            name: Module name (required)
            path: Module path (required)
            
        Returns:
            Imported module
            
        NO OPTIONAL PARAMETERS - all args required.
        """
        ...


class PackageImportStrategy:
    """Import strategy for Python packages.
    
    Handles importing modules that are part of a package
    (indicated by .modelchecker marker).
    
    NO LEGACY SUPPORT - no config.py handling.
    """
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import module as part of a package.
        
        Args:
            name: Module name (REQUIRED)
            path: Module path (REQUIRED)
            
        Returns:
            Imported module
            
        Raises:
            PackageImportError: If import fails
            
        NO FALLBACKS - fails fast on errors.
        """
        package_root = self._get_package_root(path)
        
        if not package_root:
            raise PackageImportError(
                f"Not a valid package: {path}",
                "No .modelchecker marker found in parent directories",
                "Add .modelchecker with 'package=true' to package root"
            )
        
        # Add parent of package to sys.path PERMANENTLY
        parent_dir = str(Path(package_root).parent)
        if parent_dir not in sys.path:
            sys.path.insert(0, parent_dir)
        
        # Construct full module name
        package_name = Path(package_root).name
        rel_path = Path(path).relative_to(package_root)
        
        # Remove .py extension
        module_path = str(rel_path.with_suffix(''))
        
        # Convert path separators to dots
        module_parts = module_path.replace(os.sep, '.')
        full_module_name = f"{package_name}.{module_parts}"
        
        try:
            # Direct import with no fallbacks
            module = importlib.import_module(full_module_name)
            return module
            
        except ImportError as e:
            raise PackageImportError(
                f"Cannot import {full_module_name}",
                f"Package root: {package_root}, Error: {str(e)}",
                "Ensure package has __init__.py and valid structure"
            )
    
    def _get_package_root(self, path: str) -> str:
        """Find package root by .modelchecker marker.
        
        Args:
            path: Module path
            
        Returns:
            Package root path or empty string if not found
            
        NO CONFIG.PY DETECTION - only .modelchecker.
        """
        current = Path(path)
        
        if current.is_file():
            current = current.parent
            
        while current != current.parent:
            marker = current / ".modelchecker"
            if marker.exists():
                # Validate marker content
                with open(marker, 'r') as f:
                    if 'package=true' in f.read():
                        return str(current)
            current = current.parent
            
        return ""


class StandardImportStrategy:
    """Import strategy for standalone modules.
    
    Handles importing regular Python modules that are not
    part of a package structure.
    """
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import module as standalone.
        
        Args:
            name: Module name (REQUIRED)
            path: Module path (REQUIRED)
            
        Returns:
            Imported module
            
        Raises:
            PackageImportError: If import fails
            
        NO OPTIONAL PARAMETERS.
        """
        # Add module directory to sys.path PERMANENTLY
        module_dir = str(Path(path).parent)
        if module_dir not in sys.path:
            sys.path.insert(0, module_dir)
        
        try:
            # Use importlib to import the module
            spec = importlib.util.spec_from_file_location(name, path)
            
            if spec is None:
                raise PackageImportError(
                    f"Cannot create module spec for '{name}'",
                    f"Path: {path}",
                    "Ensure file is a valid Python module"
                )
            
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            
            if spec.loader is None:
                raise PackageImportError(
                    f"No loader for module '{name}'",
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



class TheoryLibImportStrategy:
    """Import strategy for theory library files.
    
    Handles importing files from model_checker.theory_lib as proper Python modules
    to preserve relative imports within the theory library.
    """
    
    def import_module(self, name: str, path: str) -> ModuleType:
        """Import a theory library file as a Python module.
        
        Args:
            name: Module name (may be ignored)
            path: Full file path to the theory library file
            
        Returns:
            Imported module
            
        Raises:
            PackageImportError: If import fails
        """
        from pathlib import Path
        import importlib
        
        # Convert file path to module path
        path_obj = Path(path).resolve()
        
        # Find where model_checker starts in the path
        path_parts = path_obj.parts
        
        # Look for 'model_checker' in the path
        try:
            mc_index = path_parts.index('model_checker')
        except ValueError:
            # Fallback to standard import if not in model_checker structure
            raise PackageImportError(
                f"File is not in model_checker structure",
                f"Path: {path}",
                "Theory library files must be under model_checker/theory_lib"
            )
        
        # Build module name from path
        module_parts = list(path_parts[mc_index:])
        
        # Remove .py extension from last part
        if module_parts[-1].endswith('.py'):
            module_parts[-1] = module_parts[-1][:-3]
        
        # Create dotted module path
        module_name = '.'.join(module_parts)
        
        try:
            # Import as a proper Python module
            module = importlib.import_module(module_name)
            
            # Force reload to ensure fresh import
            importlib.reload(module)
            
            return module
            
        except ImportError as e:
            # Check for specific import errors
            if "No module named" in str(e):
                raise PackageImportError(
                    f"Module '{module_name}' not found",
                    f"Attempted import: {module_name}",
                    f"Original path: {path}",
                    "Ensure model_checker is in Python path"
                )
            elif "attempted relative import" in str(e):
                raise PackageImportError(
                    f"Relative import error in '{module_name}'",
                    f"Error: {str(e)}",
                    "Theory library modules must use relative imports"
                )
            else:
                raise PackageImportError(
                    f"Failed to import module '{module_name}'",
                    f"Path: {path}, Error: {str(e)}",
                    "Check module syntax and dependencies"
                )
        except Exception as e:
            raise PackageImportError(
                f"Failed to import module '{module_name}'",
                f"Path: {path}, Error: {str(e)}",
                "Check module syntax and dependencies"
            )


# NO LegacyImportStrategy class - not provided
# This is a BREAKING CHANGE - no legacy support