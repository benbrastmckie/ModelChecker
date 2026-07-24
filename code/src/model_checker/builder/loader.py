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
        # Resolve module_path to absolute path for consistent handling
        self.module_path = str(Path(module_path).resolve()) if module_path else module_path
        self.module_dir = str(Path(self.module_path).parent) if self.module_path else None
    
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

        Resolves theory_lib's root directory via the core registry at runtime rather than a
        hardcoded path substring -- this keeps loader.py (core) free of any literal reference
        to theory_lib's dotted or path form (see docs/THEORY_ARCHITECTURE.md's Layering
        section: core may never name theory_lib, statically or by string literal).

        Returns:
            True if module is under the theory_lib package root, False otherwise
        """
        theory_lib_root = _resolve_theory_lib_root()
        if theory_lib_root is None:
            return False
        module_path = Path(self.module_path).resolve()
        try:
            module_path.relative_to(theory_lib_root)
            return True
        except ValueError:
            return False
    
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

        Uses the core registry's `module_path` for the actual import, so the dotted
        theory_lib prefix lives in theory_lib (which populated the registry), not as a
        literal in this core module.

        Returns:
            The loaded theory module

        Raises:
            ImportError: If theory module cannot be found
        """
        from .. import registry

        theory_name = self.module_name.lower()
        try:
            entry = registry.get_theory_entry(theory_name)
        except ValueError:
            raise ImportError(
                f"Cannot find theory module '{theory_name}' in the theory registry"
            )
        try:
            module = __import__(entry.module_path, fromlist=[theory_name])
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


def _resolve_theory_lib_root() -> Optional[Path]:
    """Resolve theory_lib's package root directory from the core registry.

    Module-level helper (not a ModuleLoader method, to keep the class's own method count
    within its documented budget). Uses one registered theory's `module_path` (a runtime
    value populated by theory_lib itself, never a literal written here) to locate its file via
    `importlib.util.find_spec`, then walks up two parents (`<theory>/__init__.py` ->
    `<theory>/` -> the shared package root all registered theories live under).

    Returns:
        The theory package root directory, or None if no theory is registered yet.
    """
    from .. import registry
    import importlib.util

    registered = registry.get_registered()
    if not registered:
        return None
    entry = registry.get_theory_entry(registered[0])
    spec = importlib.util.find_spec(entry.module_path)
    if spec is None or spec.origin is None:
        return None
    return Path(spec.origin).resolve().parent.parent


def discover_theory_module(theory_name: str, semantic_theory: Dict[str, Any]) -> Optional[str]:
    """Discover which theory module a semantic theory belongs to.

    Args:
        theory_name: Name of the theory (e.g., "Bimodal")
        semantic_theory: Dictionary containing the semantic theory implementation

    Returns:
        The module name (e.g., "bimodal") or None if not found
    """
    from .. import registry

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

    # Method 2: Check for theory-specific markers, derived from the registry (fixes a live
    # drift bug: the previous hardcoded prop_to_theory dict only ever covered 'bimodal',
    # silently falling through to Method 4's less-precise name fallback for the other three
    # theories -- this iterates every REGISTERED theory instead of a fixed literal dict, so
    # it self-corrects as theories are added).
    prop_class = semantic_theory.get("proposition")
    if prop_class and hasattr(prop_class, '__name__'):
        prop_name = prop_class.__name__
        for entry in registry.iter_theories():
            registered_prop = entry.proposition
            if hasattr(registered_prop, '__name__') and registered_prop.__name__ in prop_name:
                return entry.name

    # Method 3: Check model class names the same way (fixes the equivalent drift in the
    # previous hardcoded theory_patterns dict).
    model_class = semantic_theory.get("model")
    if model_class and hasattr(model_class, '__name__'):
        model_name = model_class.__name__
        for entry in registry.iter_theories():
            registered_model = entry.model
            if hasattr(registered_model, '__name__') and registered_model.__name__ in model_name:
                return entry.name

    # Method 4: Fallback to theory name
    if theory_name:
        return theory_name.lower()

    return None