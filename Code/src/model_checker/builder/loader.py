"""Module loading and discovery utilities.

This module handles loading user modules, discovering theory implementations,
and managing project directories.
"""

# Standard library imports
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
        self.module_dir = os.path.dirname(self.module_path)
    
    def discover_theory_module(self, theory_name, semantic_theory):
        """Dynamically discover which theory module a semantic theory belongs to.
        
        This method attempts to find the correct theory module by:
        1. Checking the module path of the semantics class
        2. Looking for theory-specific markers (proposition types, settings)
        3. Falling back to theory name matching
        
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
        
        # Don't search beyond 5 levels up
        for _ in range(5):
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
            # For generated projects, add project root to path
            if self.is_generated_project(self.module_dir):
                project_dir = self.find_project_directory(self.module_dir)
                if project_dir:
                    # Add both project root and src/ to path
                    sys.path.insert(0, project_dir)
                    src_dir = os.path.join(project_dir, 'src')
                    if os.path.exists(src_dir):
                        sys.path.insert(0, src_dir)
            
            # Add module directory to Python path
            sys.path.insert(0, self.module_dir)
            
            # Load the module
            spec = importlib.util.spec_from_file_location(self.module_name, self.module_path)
            if spec is None:
                raise ImportError(f"Could not load spec for module '{self.module_name}'")
                
            module = importlib.util.module_from_spec(spec)
            
            # Add to sys.modules to make it importable
            sys.modules[self.module_name] = module
            
            # Execute the module
            try:
                spec.loader.exec_module(module)
            except FileNotFoundError:
                # Try to give a more helpful error message
                raise ImportError(
                    f"Could not find the file '{self.module_path}'. "
                    f"Please check that the file path is correct."
                )
            except Exception as e:
                # Remove from sys.modules on error
                if self.module_name in sys.modules:
                    del sys.modules[self.module_name]
                raise ImportError(f"Error executing module '{self.module_name}': {str(e)}")
            
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