"""Module loading with clean architecture.

This module provides the ModuleLoader class with single responsibility:
loading Python modules. Detection is handled by ProjectDetector,
import strategies are handled by strategy classes.

NO BACKWARDS COMPATIBILITY - clean break from legacy implementation.
"""

import sys
from types import ModuleType
from pathlib import Path
from typing import Optional, Dict, Any

from .errors import PackageStructureError
from .detector import ProjectDetector, ProjectType
from .strategies import PackageImportStrategy, StandardImportStrategy


class ModuleLoader:
    """Clean module loader with single responsibility.
    
    This class ONLY loads modules. It does NOT:
    - Detect project types (use ProjectDetector)
    - Handle legacy config.py or project.yaml
    - Restore sys.path (changes are permanent)
    - Have optional parameters
    
    Total: <200 lines, ≤6 public methods
    """
    
    def __init__(self, module_name: str, module_path: str):
        """Initialize loader with module information.
        
        Args:
            module_name: Name of module to load
            module_path: Path to module file
            
        Raises:
            PackageStructureError: If module file doesn't exist
        """
        self.module_name = module_name
        self.module_path = module_path
        self.module_dir = str(Path(module_path).parent) if module_path else None
    
    def load_module(self) -> ModuleType:
        """Load the module using appropriate strategy.
        
        Returns:
            The loaded module
            
        Raises:
            ImportError: If module cannot be loaded
        """
        # Validate file exists
        if not Path(self.module_path).exists():
            raise ImportError(
                f"Module not found: {self.module_path}\n"
                f"Working directory: {Path.cwd()}\n"
                f"Ensure module file exists at specified path"
            )
        
        # Check if this is a theory_lib file that should be imported as a module
        if self._is_theory_lib_file():
            from .strategies import TheoryLibImportStrategy
            strategy = TheoryLibImportStrategy()
        elif self._is_package():
            strategy = PackageImportStrategy()
        else:
            strategy = StandardImportStrategy()
            
        return strategy.import_module(self.module_name, self.module_path)
    
    def get_module_directory(self) -> str:
        """Get directory containing the module.
        
        Returns:
            Path to module directory
        """
        return str(Path(self.module_path).parent)
    
    def _is_theory_lib_file(self) -> bool:
        """Check if module is part of the theory_lib directory.
        
        Returns:
            True if module is in theory_lib, False otherwise
        """
        # Get absolute path of the module
        module_path = Path(self.module_path).resolve()
        
        # Check if it's under src/model_checker/theory_lib
        return 'model_checker/theory_lib' in str(module_path) or 'model_checker\\theory_lib' in str(module_path)
    
    def _is_package(self) -> bool:
        """Check if module is part of a package.
        
        Returns:
            True if module is in a package, False otherwise
            
        ONLY checks for .modelchecker marker.
        """
        detector = ProjectDetector(self.module_path)
        return detector.detect_project_type() == ProjectType.PACKAGE
    
    def load_attribute(self, module: ModuleType, attr_name: str) -> Any:
        """Load a required attribute from a module with validation.
        
        Args:
            module: The module to load from
            attr_name: Name of the attribute to load
            
        Returns:
            The loaded attribute
            
        Raises:
            ImportError: If the attribute is missing
        """
        if not hasattr(module, attr_name):
            raise ImportError(
                f"Module '{module.__name__}' is missing required attribute '{attr_name}'"
            )
        return getattr(module, attr_name)
    
    def discover_theory_module(self) -> ModuleType:
        """Discover and load theory module from theory_lib.
        
        Returns:
            The loaded theory module
            
        Raises:
            ImportError: If theory module cannot be found
        """
        theory_name = self.module_name.lower()
        try:
            # Try to import from theory_lib
            module = __import__(f"model_checker.theory_lib.{theory_name}", 
                              fromlist=[theory_name])
            return module
        except ImportError:
            raise ImportError(
                f"Cannot find theory module '{theory_name}' in theory_lib"
            )
    
    def discover_theory_module_for_iteration(self, theory_name: str, semantic_theory: Dict[str, Any]) -> Optional[str]:
        """Discover which theory module a semantic theory belongs to.
        
        This is a compatibility method that delegates to the module-level function.
        
        Args:
            theory_name: Name of the theory
            semantic_theory: Dictionary containing the semantic theory
            
        Returns:
            The module name or None if not found
        """
        return discover_theory_module(theory_name, semantic_theory)


def discover_theory_module(theory_name: str, semantic_theory: Dict[str, Any]) -> Optional[str]:
    """Discover which theory module a semantic theory belongs to.
    
    Args:
        theory_name: Name of the theory (e.g., "Logos", "Exclusion")
        semantic_theory: Dictionary containing the semantic theory implementation
        
    Returns:
        The module name (e.g., "logos", "exclusion") or None if not found
    """
    # Method 1: Check the module path of the semantics class
    semantics_class = semantic_theory.get("semantics")
    if semantics_class and hasattr(semantics_class, '__module__'):
        module_path = semantics_class.__module__
        if 'theory_lib' in module_path:
            parts = module_path.split('.')
            if 'theory_lib' in parts:
                theory_idx = parts.index('theory_lib') + 1
                if theory_idx < len(parts):
                    return parts[theory_idx]
    
    # Method 2: Check for theory-specific markers
    prop_class = semantic_theory.get("proposition")
    if prop_class and hasattr(prop_class, '__name__'):
        prop_name = prop_class.__name__
        prop_to_theory = {
            'LogosProposition': 'logos',
            'ExclusionProposition': 'exclusion', 
            'BimodalProposition': 'bimodal',
            'ImpositionProposition': 'imposition'
        }
        for prop_pattern, theory_module in prop_to_theory.items():
            if prop_pattern in prop_name:
                return theory_module
    
    # Method 3: Check model class names
    model_class = semantic_theory.get("model")
    if model_class and hasattr(model_class, '__name__'):
        model_name = model_class.__name__
        theory_patterns = {
            'Logos': 'logos',
            'Exclusion': 'exclusion',
            'Bimodal': 'bimodal',
            'Imposition': 'imposition'
        }
        for pattern, module in theory_patterns.items():
            if pattern in model_name:
                return module
    
    # Method 4: Fallback to theory name
    if theory_name:
        return theory_name.lower()
    
    return None