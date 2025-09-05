"""Module loading and discovery utilities.

This module handles loading user modules, discovering theory implementations,
and managing project directories.
"""

# Standard library imports
import importlib
import importlib.util
import os
import sys


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
    
    def discover_theory_module(self):
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
    
    def is_generated_project(self, module_dir):
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
    
    def find_project_directory(self, module_dir):
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
    
    def load_module(self):
        """Load a Python module from the given file path.
        
        This method handles module loading with proper sys.path management
        for both standalone modules and generated projects.
        
        Returns:
            module: The loaded Python module
            
        Raises:
            ImportError: If the module cannot be loaded
        """
        # Store original sys.path
        original_syspath = sys.path.copy()
        
        try:
            # Special handling for theory library modules
            if 'model_checker/theory_lib' in self.module_path.replace('\\', '/'):
                # This is a theory library file - we need to import it as a package module
                # Find the src directory that contains model_checker
                current = os.path.dirname(self.module_path)
                src_dir = None
                while current and current != '/':
                    if os.path.exists(os.path.join(current, 'model_checker', '__init__.py')):
                        # Found the src directory
                        src_dir = current
                        sys.path.insert(0, current)
                        break
                    current = os.path.dirname(current)
                
                if src_dir:
                    # Construct the full module path
                    rel_path = os.path.relpath(self.module_path, src_dir)
                    # Convert file path to module path
                    module_parts = rel_path.replace(os.sep, '.').replace('.py', '')
                    
                    # Import the module using its full package path
                    try:
                        imported_module = importlib.import_module(module_parts)
                        return imported_module
                    except ImportError as e:
                        # If relative imports fail, provide helpful error
                        if "relative import" in str(e) or "parent package" in str(e):
                            # Extract theory and subtheory info for helpful error
                            path_parts = self.module_path.replace('\\', '/').split('/')
                            if 'theory_lib' in path_parts:
                                theory_idx = path_parts.index('theory_lib') + 1
                                if theory_idx < len(path_parts):
                                    theory_name = path_parts[theory_idx]
                                    
                                    # Check if this is a subtheory
                                    if theory_idx + 1 < len(path_parts) and path_parts[theory_idx + 1] == 'subtheories':
                                        if theory_idx + 2 < len(path_parts):
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
                        raise
            
            # For generated projects, we need special handling
            if self.is_generated_project(self.module_dir):
                project_dir = self.find_project_directory(self.module_dir)
                if project_dir:
                    # Check if this is a generated project by looking for config.py
                    config_path = os.path.join(project_dir, 'config.py')
                    if os.path.exists(config_path):
                        # This is a generated project - it has relative imports that need
                        # the original theory context. We'll need to modify the imports
                        # dynamically or provide the proper context
                        
                        # Read the config.py to understand which theory this is from
                        try:
                            with open(config_path, 'r') as f:
                                config_content = f.read()
                            
                            # Extract the theory import
                            if 'from model_checker.theory_lib import' in config_content:
                                # Find which theory is imported
                                import re
                                match = re.search(r'from model_checker\.theory_lib import (\w+)', config_content)
                                if match:
                                    theory_name = match.group(1)
                                    
                                    # For examples.py, we'll need to handle the relative imports
                                    # by creating a modified version that uses absolute imports
                                    if self.module_path.endswith('examples.py'):
                                        return self._load_generated_project_with_absolute_imports(
                                            project_dir, theory_name, self.module_path
                                        )
                        except Exception:
                            pass
                    
                    # Otherwise, try normal project loading
                    sys.path.insert(0, project_dir)
            
            # Add module directory to Python path
            sys.path.insert(0, self.module_dir)
            
            # Load the module
            try:
                spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
                if spec is None:
                    raise ImportError(f"Could not load spec for module '{self.module_name}'")
            except ImportError as e:
                # Wrap the ImportError with our standard message
                raise ImportError(f"Failed to import module '{self.module_name}': {str(e)}")
                
            module = importlib.util.module_from_spec(spec)
            
            # Add to sys.modules to make it importable
            sys.modules[self.module_name] = module
            
            # Execute the module
            try:
                spec.loader.exec_module(module)
            except FileNotFoundError:
                # Try to give a more helpful error message
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
            
        finally:
            # Restore original sys.path
            sys.path = original_syspath
    
    def load_attribute(self, module, attr_name):
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