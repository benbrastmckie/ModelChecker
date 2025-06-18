"""
Operator registry system for the logos theory.

This module provides dynamic loading and management of subtheory operators,
supporting selective loading, conflict resolution, and dependency management.
"""

import importlib
from model_checker.syntactic import OperatorCollection


class LogosOperatorRegistry:
    """
    Dynamic registry for loading and managing subtheory operators.
    
    Supports selective loading, conflict resolution, and dependency management
    across all logos subtheories.
    """
    
    def __init__(self):
        self.loaded_subtheories = {}
        self.operator_collection = OperatorCollection()
        self.dependencies = {
            'modal': ['extensional'],
            'counterfactual': ['extensional'],
            'constitutive': [],
            'relevance': ['constitutive'],
            'extensional': []
        }
    
    def load_subtheory(self, name):
        """
        Load a specific subtheory and its operators.
        
        Args:
            name: Name of the subtheory to load
            
        Returns:
            The loaded subtheory module
            
        Raises:
            ValueError: If subtheory cannot be loaded
        """
        if name in self.loaded_subtheories:
            return self.loaded_subtheories[name]
        
        # Load dependencies first
        for dep in self.dependencies.get(name, []):
            self.load_subtheory(dep)
        
        try:
            module_path = f'.subtheories.{name}'
            module = importlib.import_module(module_path, package=__package__)
            
            # Get operators from the subtheory
            if hasattr(module, 'get_operators'):
                operators = module.get_operators()
                for op_class in operators.values():
                    self.operator_collection.add_operator(op_class)
            
            self.loaded_subtheories[name] = module
            return module
            
        except ImportError as e:
            raise ValueError(f"Failed to load subtheory '{name}': {e}")
    
    def load_subtheories(self, names):
        """
        Load multiple subtheories.
        
        Args:
            names: List of subtheory names to load
            
        Returns:
            List of loaded subtheory modules
        """
        modules = []
        for name in names:
            module = self.load_subtheory(name)
            modules.append(module)
        return modules
    
    def get_operators(self):
        """
        Get all loaded operators.
        
        Returns:
            OperatorCollection containing all loaded operators
        """
        return self.operator_collection
    
    def get_loaded_subtheories(self):
        """
        Get list of currently loaded subtheory names.
        
        Returns:
            List of loaded subtheory names
        """
        return list(self.loaded_subtheories.keys())
    
    def unload_subtheory(self, name):
        """
        Unload a specific subtheory.
        
        Args:
            name: Name of the subtheory to unload
            
        Note:
            This removes the subtheory from the registry but does not
            remove its operators from the collection.
        """
        if name in self.loaded_subtheories:
            del self.loaded_subtheories[name]
    
    def reload_subtheory(self, name):
        """
        Reload a specific subtheory.
        
        Args:
            name: Name of the subtheory to reload
        """
        if name in self.loaded_subtheories:
            self.unload_subtheory(name)
        return self.load_subtheory(name)
    
    def check_dependencies(self, name):
        """
        Check if all dependencies for a subtheory are loaded.
        
        Args:
            name: Name of the subtheory to check
            
        Returns:
            True if all dependencies are loaded, False otherwise
        """
        deps = self.dependencies.get(name, [])
        return all(dep in self.loaded_subtheories for dep in deps)
    
    def get_operator_by_name(self, operator_name):
        """
        Get a specific operator by name.
        
        Args:
            operator_name: Name of the operator to retrieve
            
        Returns:
            The operator class if found, None otherwise
        """
        try:
            return self.operator_collection[operator_name]
        except KeyError:
            return None
    
    def list_available_operators(self):
        """
        List all available operators from loaded subtheories.
        
        Returns:
            Dictionary mapping operator names to their classes
        """
        return dict(self.operator_collection.items())
    
    def get_subtheory_operators(self, subtheory_name):
        """
        Get operators specific to a subtheory.
        
        Args:
            subtheory_name: Name of the subtheory
            
        Returns:
            Dictionary of operators from that subtheory
        """
        if subtheory_name not in self.loaded_subtheories:
            return {}
        
        module = self.loaded_subtheories[subtheory_name]
        if hasattr(module, 'get_operators'):
            return module.get_operators()
        return {}
    
    def validate_operator_compatibility(self):
        """
        Validate that all loaded operators are compatible.
        
        Returns:
            List of compatibility issues (empty if no issues)
        """
        issues = []
        
        # Check for operator name conflicts
        operator_names = {}
        for subtheory_name, module in self.loaded_subtheories.items():
            if hasattr(module, 'get_operators'):
                ops = module.get_operators()
                for op_name in ops:
                    if op_name in operator_names:
                        issues.append(
                            f"Operator name conflict: '{op_name}' defined in both "
                            f"'{operator_names[op_name]}' and '{subtheory_name}'"
                        )
                    else:
                        operator_names[op_name] = subtheory_name
        
        return issues
    
    def clear_all(self):
        """Clear all loaded subtheories and operators."""
        self.loaded_subtheories.clear()
        self.operator_collection = OperatorCollection()