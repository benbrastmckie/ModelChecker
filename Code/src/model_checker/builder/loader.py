"""Module loading and discovery utilities.

This module handles loading user modules, discovering theory implementations,
and managing project directories.
"""

# Standard library imports
import importlib
import importlib.util
import os
import sys
from typing import TYPE_CHECKING, Any, Dict, List, Optional, Union
from types import ModuleType
from pathlib import Path

# Local imports
from .types import TheoryName, TheoryDict, ModulePath

if TYPE_CHECKING:
    from types import ModuleType


class ModuleLoader:
    """Handles loading and discovery of user modules and theories."""
    
    def __init__(self, module_name, module_path):
        """Initialize with module information.
        
        Args:
            module_name: Name of the module to load
            module_path: Path to the module file
        """
        self.module_name = module_name
        self.module_path = module_path
        self.module_dir = os.path.dirname(self.module_path) if module_path else None
    
    def discover_theory_module_for_iteration(self, theory_name, semantic_theory):
        """Dynamically discover which theory module a semantic theory belongs to.
        
        This method attempts to find the correct theory module by:
        1. Checking the module path of the semantics class
        2. Looking for theory-specific markers (proposition types, settings)
        3. Falling back to theory name matching
        
        Used during iteration to determine the correct theory module for a semantic theory.
        
        Args:
            theory_name: Name of the theory (e.g., "Logos", "Exclusion")
            semantic_theory: Dictionary containing the semantic theory implementation
            
        Returns:
            str: The module name (e.g., "logos", "exclusion") or None if not found
        """
        # Method 1: Check the module path of the semantics class
        semantics_class = semantic_theory.get("semantics")
        if semantics_class and hasattr(semantics_class, '__module__'):
            module_path = semantics_class.__module__
            # Extract theory module name from path like 'model_checker.theory_lib.logos.semantics'
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
            # Map proposition classes to theory modules
            prop_to_theory = {
                'LogosProposition': 'logos',
                'ExclusionProposition': 'exclusion', 
                'BimodalProposition': 'bimodal',
                'ImpositionProposition': 'imposition'
            }
            for prop_pattern, theory_module in prop_to_theory.items():
                if prop_pattern in prop_name:
                    return theory_module
        
        # Method 3: Check for theory-specific settings
        model_class = semantic_theory.get("model")
        if model_class and hasattr(model_class, '__name__'):
            model_name = model_class.__name__
            # Common patterns in model class names
            if 'Logos' in model_name:
                return 'logos'
            elif 'Exclusion' in model_name:
                return 'exclusion'
            elif 'Bimodal' in model_name:
                return 'bimodal'
            elif 'Imposition' in model_name:
                return 'imposition'
        
        # Method 4: Fallback to theory name
        return theory_name.lower() if theory_name else None
    
    def _load_generated_project_with_absolute_imports(self, project_dir, theory_name, module_path):
        """Load a generated project module by converting relative imports to absolute.
        
        Generated projects copy theory files that use relative imports. When loaded
        outside their original package context, these fail. This method reads the
        file and converts relative imports to absolute imports dynamically.
        
        Args:
            project_dir: The generated project directory
            theory_name: The name of the theory (e.g., 'logos')
            module_path: Path to the module file
            
        Returns:
            The loaded module with working imports
        """
        # Read the module content
        with open(module_path, 'r') as f:
            content = f.read()
        
        # Convert relative imports to absolute imports
        # Replace patterns like "from .semantic import" with "from model_checker.theory_lib.logos.semantic import"
        import re
        
        # Pattern for relative imports: from .module import ...
        content = re.sub(
            r'from \.([\w\.]+) import',
            f'from model_checker.theory_lib.{theory_name}.\\1 import',
            content
        )
        
        # Pattern for relative imports: from ..module import ...
        content = re.sub(
            r'from \.\.([\w\.]+) import',
            f'from model_checker.theory_lib.{theory_name}.\\1 import',
            content
        )
        
        # Pattern for relative imports: from ...module import ...
        content = re.sub(
            r'from \.\.\.([\w\.]+) import',
            f'from model_checker.theory_lib.\\1 import',
            content
        )
        
        # Create a module and exec the modified code
        import types
        module = types.ModuleType(self.module_name)
        module.__file__ = module_path
        
        # Add module to sys.modules before exec
        sys.modules[self.module_name] = module
        
        try:
            # Execute the modified code in the module's namespace
            exec(content, module.__dict__)
            return module
        except Exception as e:
            # Remove from sys.modules on error
            if self.module_name in sys.modules:
                del sys.modules[self.module_name]
            raise ImportError(f"Failed to load generated project module: {str(e)}")
    
    def discover_theory_module(self) -> ModuleType:
        """Import a theory module from theory_lib.
        
        This is a simplified method for importing theory modules directly.
        Used when module_name is a theory name and module_path is None.
        
        Returns:
            module: The imported theory module
            
        Raises:
            ImportError: If the theory cannot be imported
        """
        try:
            theory_module = importlib.import_module(f"model_checker.theory_lib.{self.module_name}")
            return theory_module
        except ImportError:
            raise ImportError(f"Theory '{self.module_name}' not found in model_checker.theory_lib")
    
    def is_generated_project(self, module_dir: str) -> bool:
        """Detect if module is from a generated project.
        
        Generated projects have a specific structure with:
        - A config.py file
        - theory_lib imports configured in config.py
        
        Args:
            module_dir: Directory containing the module
            
        Returns:
            bool: True if this appears to be a generated project
        """
        config_path = os.path.join(module_dir, 'config.py')
        if os.path.exists(config_path):
            # Check if config.py contains theory imports
            try:
                with open(config_path, 'r') as f:
                    content = f.read()
                    # Look for patterns that indicate a generated project
                    if 'from model_checker.theory_lib import' in content:
                        return True
                    if 'theory = ' in content and '.get_theory(' in content:
                        return True
            except Exception:
                pass
        
        # Also check for other generated project markers
        markers = [
            'project.yaml',  # Project configuration
            'examples/',     # Examples directory
            'tests/',        # Tests directory
        ]
        
        marker_count = sum(1 for marker in markers 
                          if os.path.exists(os.path.join(module_dir, marker)))
        
        # If we have config.py and at least one other marker, it's likely generated
        return os.path.exists(config_path) and marker_count >= 1
    
    def find_project_directory(self, module_dir: str) -> Optional[str]:
        """Find the project root directory for generated projects.
        
        Searches up the directory tree for markers that indicate a project root:
        - project.yaml file
        - src/ directory with module inside
        - Typical project structure markers
        
        Args:
            module_dir: Starting directory to search from
            
        Returns:
            str: Path to project root, or None if not found
        """
        current_dir = os.path.abspath(module_dir)
        
        # Don't search beyond 25 levels up (increased to handle deep structures)
        for _ in range(25):
            # Check for project markers
            if os.path.exists(os.path.join(current_dir, 'project.yaml')):
                return current_dir
            
            # Check if this looks like a project root with src/
            src_dir = os.path.join(current_dir, 'src')
            if os.path.exists(src_dir) and os.path.isdir(src_dir):
                # Verify our module is inside src/
                if module_dir.startswith(src_dir):
                    return current_dir
            
            # Move up one directory
            parent = os.path.dirname(current_dir)
            if parent == current_dir:  # Reached root
                break
            current_dir = parent
        
        return None
    
    def load_module(self) -> ModuleType:
        """Load a Python module with package detection.
        
        Returns:
            ModuleType: The loaded Python module
            
        Raises:
            ImportError: If the module cannot be loaded
        """
        # Store original sys.path
        original_syspath = sys.path.copy()
        
        # Track if we're loading a generated package
        is_generated_package = False
        
        try:
            # Check if this is a generated project package
            if self._is_generated_project_package():
                is_generated_package = True
                return self._load_as_package_module()
            
            # Try other loading methods as before
            if 'model_checker/theory_lib' in self.module_path.replace('\\', '/'):
                module = self._load_theory_library_module()
                if module:
                    return module
            
            # Try loading as generated project (legacy)
            if self.is_generated_project(self.module_dir):
                module = self._load_generated_project_module()
                if module:
                    return module
            
            # Load as regular module
            return self._load_standard_module()
            
        finally:
            # Only restore sys.path for non-generated packages
            # Generated packages need to remain importable
            if not is_generated_package:
                sys.path = original_syspath
    
    def _load_theory_library_module(self) -> ModuleType:
        """Load a module from the theory library.
        
        Returns:
            module or None: The loaded module if successful, None otherwise
            
        Raises:
            ImportError: If module is a theory library file that can't be run directly
        """
        # Find the src directory that contains model_checker
        src_dir = self._find_src_directory()
        if not src_dir:
            return None
        
        sys.path.insert(0, src_dir)
        
        # Construct the full module path
        rel_path = os.path.relpath(self.module_path, src_dir)
        module_parts = rel_path.replace(os.sep, '.').replace('.py', '')
        
        # Import the module using its full package path
        try:
            return importlib.import_module(module_parts)
        except ImportError as e:
            if "relative import" in str(e) or "parent package" in str(e):
                self._raise_theory_library_error()
            raise
    
    def _find_src_directory(self) -> Optional[str]:
        """Find the src directory containing model_checker package.
        
        Returns:
            str or None: Path to src directory if found, None otherwise
        """
        current = os.path.dirname(self.module_path)
        while current and current != '/':
            if os.path.exists(os.path.join(current, 'model_checker', '__init__.py')):
                return current
            current = os.path.dirname(current)
        return None
    
    def _raise_theory_library_error(self) -> None:
        """Raise a helpful error for theory library modules that can't be run directly."""
        path_parts = self.module_path.replace('\\', '/').split('/')
        if 'theory_lib' not in path_parts:
            return
        
        theory_idx = path_parts.index('theory_lib') + 1
        if theory_idx >= len(path_parts):
            return
        
        theory_name = path_parts[theory_idx]
        
        # Check if this is a subtheory
        if (theory_idx + 1 < len(path_parts) and 
            path_parts[theory_idx + 1] == 'subtheories' and 
            theory_idx + 2 < len(path_parts)):
            
            subtheory_name = path_parts[theory_idx + 2]
            raise ImportError(
                f"\nCannot run theory library examples directly.\n"
                f"Theory library modules use relative imports that require proper package context.\n\n"
                f"Please use one of these methods instead:\n"
                f"1. Run tests: ./run_tests.py --examples {theory_name}\n"
                f"2. Use pytest: cd Code && pytest src/model_checker/theory_lib/{theory_name}/subtheories/{subtheory_name}/tests/\n"
                f"3. Create a standalone test file with absolute imports\n\n"
                f"Example standalone file:\n"
                f"  from model_checker.theory_lib.{theory_name} import {theory_name.capitalize()}Semantics\n"
                f"  from model_checker.theory_lib.{theory_name}.subtheories.{subtheory_name}.examples import *\n"
            )
        else:
            # Main theory examples
            raise ImportError(
                f"\nCannot run theory library examples directly.\n"
                f"Theory library modules use relative imports that require proper package context.\n\n"
                f"Please use one of these methods instead:\n"
                f"1. Run tests: ./run_tests.py --examples {theory_name}\n"
                f"2. Use pytest: cd Code && pytest src/model_checker/theory_lib/{theory_name}/tests/\n"
                f"3. Create a standalone test file with absolute imports"
            )
    
    def _load_generated_project_module(self) -> ModuleType:
        """Load a module from a generated project.
        
        Returns:
            module or None: The loaded module if successful, None otherwise
        """
        project_dir = self.find_project_directory(self.module_dir)
        if not project_dir:
            return None
        
        # Check if this is a generated project by looking for config.py
        config_path = os.path.join(project_dir, 'config.py')
        if not os.path.exists(config_path):
            sys.path.insert(0, project_dir)
            return None
        
        # Try to load with special handling for generated projects
        theory_name = self._extract_theory_from_config(config_path)
        if theory_name and self.module_path.endswith('examples.py'):
            return self._load_generated_project_with_absolute_imports(
                project_dir, theory_name, self.module_path
            )
        
        # Otherwise, try normal project loading
        sys.path.insert(0, project_dir)
        return None
    
    def _extract_theory_from_config(self, config_path: str) -> Optional[str]:
        """Extract the theory name from a generated project's config file.
        
        Args:
            config_path: Path to the config.py file
            
        Returns:
            str or None: Theory name if found, None otherwise
        """
        try:
            with open(config_path, 'r') as f:
                config_content = f.read()
            
            if 'from model_checker.theory_lib import' in config_content:
                import re
                match = re.search(r'from model_checker\.theory_lib import (\w+)', config_content)
                if match:
                    return match.group(1)
        except Exception:
            pass
        return None
    
    def _load_standard_module(self) -> ModuleType:
        """Load a standard Python module.
        
        Returns:
            module: The loaded module
            
        Raises:
            ImportError: If the module cannot be loaded
        """
        # Add module directory to Python path
        sys.path.insert(0, self.module_dir)
        
        # Load the module
        try:
            spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
            if spec is None:
                raise ImportError(f"Could not load spec for module '{self.module_name}'")
        except ImportError as e:
            raise ImportError(f"Failed to import module '{self.module_name}': {str(e)}")
        
        module = importlib.util.module_from_spec(spec)
        
        # Add to sys.modules to make it importable
        sys.modules[self.module_name] = module
        
        # Execute the module
        try:
            spec.loader.exec_module(module)
        except FileNotFoundError:
            raise ImportError(
                f"Module file not found: '{self.module_path}'. "
                f"Please check that the file path is correct."
            )
        except Exception as e:
            # Remove from sys.modules on error
            if self.module_name in sys.modules:
                del sys.modules[self.module_name]
            raise ImportError(f"Failed to import module '{self.module_name}': {str(e)}")
        
        return module
    
    def load_attribute(self, module: ModuleType, attr_name: str) -> Any:
        """Load a required attribute from the module with validation.
        
        Args:
            module: The loaded module
            attr_name: Name of the attribute to load
            
        Returns:
            The attribute value
            
        Raises:
            ImportError: If the attribute is missing or empty
        """
        if not hasattr(module, attr_name):
            raise ImportError(
                f"Module '{self.module_name}' is missing the required attribute '{attr_name}'."
            )
        
        value = getattr(module, attr_name)
        
        # Check for empty collections
        if isinstance(value, (dict, list)) and not value:
            raise ImportError(
                f"Module '{self.module_name}' has an empty '{attr_name}'. "
                f"Please define at least one item."
            )
        
        return value
    
    def _is_generated_project_package(self) -> bool:
        """Check if module is in a generated project package.
        
        Returns:
            bool: True if this is a generated package project
        """
        module_dir = os.path.dirname(self.module_path)
        
        # Walk up directory tree looking for markers
        current_dir = module_dir
        for _ in range(10):  # Limit search depth
            marker_path = os.path.join(current_dir, '.modelchecker')
            init_path = os.path.join(current_dir, '__init__.py')
            
            if os.path.exists(marker_path) and os.path.exists(init_path):
                # Verify it's a package-type project
                try:
                    with open(marker_path, 'r') as f:
                        content = f.read()
                        if 'package=true' in content:
                            return True
                except:
                    pass
            
            # Move up one directory
            parent = os.path.dirname(current_dir)
            if parent == current_dir:  # Reached root
                break
            current_dir = parent
        
        return False
    
    def _load_as_package_module(self) -> ModuleType:
        """Load module with package context for relative imports.
        
        This method handles generated packages that use relative imports by:
        1. Finding the package root via .modelchecker marker
        2. Adding the parent directory to sys.path for import resolution
        3. Importing the module with full package context
        
        Returns:
            ModuleType: The loaded module
            
        Raises:
            ImportError: If the module cannot be loaded
        """
        # Find the package root (directory with .modelchecker)
        package_root = self._find_package_root()
        if not package_root:
            raise ImportError("Could not find package root with .modelchecker marker")
        
        # Add parent of package to sys.path to enable package imports
        parent_dir = os.path.dirname(package_root)
        
        # Store whether we added to sys.path for cleanup
        added_to_path = False
        if parent_dir not in sys.path:
            sys.path.insert(0, parent_dir)
            added_to_path = True
        
        # Calculate module path relative to package
        package_name = os.path.basename(package_root)
        rel_path = os.path.relpath(self.module_path, package_root)
        
        # Convert file path to module name
        if rel_path.endswith('.py'):
            rel_path = rel_path[:-3]
        module_parts = rel_path.replace(os.sep, '.')
        
        # Full module name including package
        full_module_name = f"{package_name}.{module_parts}"
        
        # Import the module with package context
        try:
            # First ensure the package itself can be imported
            try:
                __import__(package_name)
            except ImportError as pkg_err:
                # If package can't be imported, provide helpful error
                raise ImportError(
                    f"Cannot import package '{package_name}'. "
                    f"Make sure the parent directory '{parent_dir}' is accessible. "
                    f"Original error: {str(pkg_err)}"
                )
            
            # Now import the specific module
            module = importlib.import_module(full_module_name)
            
            # Note: We don't automatically execute main/run functions
            # The module should be loaded and returned for normal processing
            
            return module
            
        except ImportError as e:
            # Clean up sys.path if we modified it and import failed
            if added_to_path and parent_dir in sys.path:
                sys.path.remove(parent_dir)
            
            # Provide helpful error message
            raise ImportError(
                f"Failed to import {full_module_name} from package {package_name}. "
                f"Package root: {package_root}, Parent dir: {parent_dir}. "
                f"Original error: {str(e)}"
            )
    
    def _find_package_root(self) -> Optional[str]:
        """Find the root directory of the generated package.
        
        Returns:
            Optional[str]: Path to package root or None if not found
        """
        current_dir = os.path.dirname(self.module_path)
        
        for _ in range(10):  # Limit search depth
            marker_path = os.path.join(current_dir, '.modelchecker')
            if os.path.exists(marker_path):
                return current_dir
            
            parent = os.path.dirname(current_dir)
            if parent == current_dir:  # Reached root
                break
            current_dir = parent
        
        return None