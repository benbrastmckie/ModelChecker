"""
Backward compatibility layer for the ModelChecker API.

This module provides compatibility wrappers that allow old code to work
with the new API during the migration period.
"""

import warnings
from typing import Dict, Any, List, Optional, Union
from dataclasses import dataclass

from .config import migrate_settings_dict, SettingsTranslator


class LegacyResult:
    """
    Compatibility wrapper for result objects.
    
    Provides the old boolean-style interface while wrapping the new
    structured result objects.
    """
    
    def __init__(self, new_result):
        """
        Initialize with a new-style result object.
        
        Args:
            new_result: New-style CheckResult object
        """
        self._result = new_result
        self._deprecation_warning_shown = False
    
    def __bool__(self):
        """Allow old code: if result: ..."""
        self._show_deprecation_warning("Boolean evaluation")
        return self._result.is_valid
    
    def check_result(self):
        """Maintain old method name for checking validity."""
        self._show_deprecation_warning("check_result method")
        return self._result.is_valid
    
    def _show_deprecation_warning(self, context: str):
        """Show deprecation warning once per instance."""
        if not self._deprecation_warning_shown:
            warnings.warn(
                f"{context} on result objects is deprecated. "
                f"Use .is_valid property on the new result object instead.",
                DeprecationWarning,
                stacklevel=3
            )
            self._deprecation_warning_shown = True
    
    # Forward all other attributes to the new result object
    def __getattr__(self, name):
        return getattr(self._result, name)


class LegacyBuildExample:
    """
    Compatibility wrapper for BuildExample.
    
    Provides the old BuildExample interface while using the new
    ExampleBuilder internally.
    """
    
    def __init__(self, name: str, theory: Dict[str, Any], example: List[Any]):
        """
        Initialize with old-style parameters.
        
        Args:
            name: Example name
            theory: Theory dictionary
            example: [premises, conclusions, settings] list
        """
        warnings.warn(
            "BuildExample is deprecated. Use ExampleBuilder from model_checker.builders instead.",
            DeprecationWarning,
            stacklevel=2
        )
        
        self.name = name
        self.theory = theory
        
        # Parse the example
        if not isinstance(example, list) or len(example) < 3:
            raise ValueError("example must be a list with [premises, conclusions, settings]")
        
        self.premises, self.conclusions, self.settings = example[:3]
        
        # Convert settings to new format
        if isinstance(self.settings, dict):
            try:
                self.config = migrate_settings_dict(self.settings)
            except Exception as e:
                warnings.warn(f"Could not migrate settings: {e}", UserWarning)
                self.config = None
        else:
            self.config = self.settings
        
        # Store for lazy initialization
        self._builder = None
        self._result = None
    
    def _get_builder(self):
        """Lazily initialize the new builder."""
        if self._builder is None:
            try:
                # Import here to avoid circular dependencies
                from model_checker.builders import ExampleBuilder
                self._builder = ExampleBuilder(self.name, self.theory)
            except ImportError:
                # Fallback if new API is not available yet
                warnings.warn(
                    "New API not available. Some functionality may be limited.",
                    UserWarning
                )
                self._builder = None
        
        return self._builder
    
    def check_result(self) -> bool:
        """Check if the example is valid using the old interface."""
        if self._result is None:
            builder = self._get_builder()
            if builder is None:
                # Fallback behavior
                return False
            
            try:
                result = builder.check(
                    premises=self.premises,
                    conclusions=self.conclusions,
                    config=self.config
                )
                self._result = LegacyResult(result)
            except Exception as e:
                warnings.warn(f"Error during checking: {e}", UserWarning)
                return False
        
        return self._result.check_result()
    
    # Provide access to internal components for advanced users
    @property
    def model_structure(self):
        """Access to model structure (if available)."""
        builder = self._get_builder()
        if builder and hasattr(builder, 'model_structure'):
            return builder.model_structure
        return None
    
    @property
    def example_settings(self):
        """Access to example settings in old format."""
        if isinstance(self.settings, dict):
            return self.settings
        elif hasattr(self.config, 'to_dict'):
            return self.config.to_dict()
        else:
            return {}


class LegacyBuildModule:
    """
    Compatibility wrapper for BuildModule.
    
    Provides the old BuildModule interface while using the new
    ProjectLoader internally.
    """
    
    def __init__(self, file_path: str):
        """
        Initialize with a file path.
        
        Args:
            file_path: Path to the module file
        """
        warnings.warn(
            "BuildModule is deprecated. Use ProjectLoader from model_checker.builders instead.",
            DeprecationWarning,
            stacklevel=2
        )
        
        self.file_path = file_path
        self._loader = None
        
    def _get_loader(self):
        """Lazily initialize the new loader."""
        if self._loader is None:
            try:
                from model_checker.builders import ProjectLoader
                self._loader = ProjectLoader.from_file(self.file_path)
            except ImportError:
                warnings.warn(
                    "New API not available. Some functionality may be limited.",
                    UserWarning
                )
                self._loader = None
        
        return self._loader
    
    def run_examples(self) -> Dict[str, bool]:
        """Run all examples in the module."""
        loader = self._get_loader()
        if loader is None:
            return {}
        
        # Run examples and convert results to old format
        results = {}
        try:
            for example_name in loader.get_example_names():
                result = loader.run_example(example_name)
                results[example_name] = result.is_valid if hasattr(result, 'is_valid') else bool(result)
        except Exception as e:
            warnings.warn(f"Error running examples: {e}", UserWarning)
        
        return results


class LegacyBuildProject:
    """
    Compatibility wrapper for BuildProject.
    
    Provides the old BuildProject interface while using the new
    ProjectBuilder internally.
    """
    
    def __init__(self, theory_name: str, project_name: str):
        """
        Initialize with theory and project names.
        
        Args:
            theory_name: Name of the theory
            project_name: Name of the project to create
        """
        warnings.warn(
            "BuildProject is deprecated. Use ProjectBuilder from model_checker.builders instead.",
            DeprecationWarning,
            stacklevel=2
        )
        
        self.theory_name = theory_name
        self.project_name = project_name
        self._builder = None
    
    def _get_builder(self):
        """Lazily initialize the new builder."""
        if self._builder is None:
            try:
                from model_checker.builders import ProjectBuilder
                self._builder = ProjectBuilder(self.theory_name)
            except ImportError:
                warnings.warn(
                    "New API not available. Some functionality may be limited.",
                    UserWarning
                )
                self._builder = None
        
        return self._builder
    
    def create(self) -> bool:
        """Create the project."""
        builder = self._get_builder()
        if builder is None:
            return False
        
        try:
            result = builder.create(self.project_name)
            return result.success if hasattr(result, 'success') else bool(result)
        except Exception as e:
            warnings.warn(f"Error creating project: {e}", UserWarning)
            return False


def create_legacy_check_formula():
    """Create a legacy version of check_formula that issues deprecation warnings."""
    
    def legacy_check_formula(formula: str, 
                           theory_name: str = "logos",
                           premises: Optional[List[str]] = None,
                           settings: Optional[Dict[str, Any]] = None):
        """Legacy check_formula function with deprecation warning."""
        warnings.warn(
            "check_formula from the main model_checker module is deprecated. "
            "Use check_formula from model_checker.jupyter instead.",
            DeprecationWarning,
            stacklevel=2
        )
        
        try:
            from model_checker.jupyter import check_formula as new_check_formula
            
            # Convert settings if provided
            if settings:
                # For check_formula, we might need to handle settings differently
                # This is a simplified conversion
                new_settings = SettingsTranslator.translate_dict(settings)
                return new_check_formula(formula, theory_name, premises, new_settings)
            else:
                return new_check_formula(formula, theory_name, premises)
                
        except ImportError:
            # Fallback if new API is not available
            warnings.warn(
                "New Jupyter API not available. check_formula functionality is limited.",
                UserWarning
            )
            return False
    
    return legacy_check_formula


def create_legacy_model_explorer():
    """Create a legacy version of ModelExplorer that issues deprecation warnings."""
    
    class LegacyModelExplorer:
        """Legacy ModelExplorer with deprecation warnings."""
        
        def __init__(self, theory_name: str = "logos"):
            warnings.warn(
                "ModelExplorer is deprecated. Use InteractiveExplorer from model_checker.jupyter instead.",
                DeprecationWarning,
                stacklevel=2
            )
            
            self.theory_name = theory_name
            self._explorer = None
        
        def _get_explorer(self):
            """Lazily initialize the new explorer."""
            if self._explorer is None:
                try:
                    from model_checker.jupyter import InteractiveExplorer
                    self._explorer = InteractiveExplorer(self.theory_name)
                except ImportError:
                    warnings.warn(
                        "New Jupyter API not available. Explorer functionality is limited.",
                        UserWarning
                    )
                    self._explorer = None
            
            return self._explorer
        
        def display(self):
            """Display the explorer."""
            explorer = self._get_explorer()
            if explorer:
                return explorer.display()
            else:
                print("Explorer not available - please install model-checker[jupyter]")
        
        def __getattr__(self, name):
            """Forward other attributes to the new explorer."""
            explorer = self._get_explorer()
            if explorer:
                return getattr(explorer, name)
            else:
                raise AttributeError(f"'{type(self).__name__}' object has no attribute '{name}'")
    
    return LegacyModelExplorer


# Create legacy functions
legacy_check_formula = create_legacy_check_formula()
LegacyModelExplorer = create_legacy_model_explorer()


def install_compatibility_layer():
    """
    Install the compatibility layer in the main model_checker module.
    
    This function can be called during the transition period to make
    old imports work with deprecation warnings.
    """
    import sys
    import model_checker
    
    # Install legacy classes
    model_checker.BuildExample = LegacyBuildExample
    model_checker.BuildModule = LegacyBuildModule  
    model_checker.BuildProject = LegacyBuildProject
    model_checker.ModelExplorer = LegacyModelExplorer
    
    # Install legacy functions
    model_checker.check_formula = legacy_check_formula
    
    # Add to __all__ if it exists
    if hasattr(model_checker, '__all__'):
        legacy_items = [
            'BuildExample', 'BuildModule', 'BuildProject',
            'ModelExplorer', 'check_formula'
        ]
        for item in legacy_items:
            if item not in model_checker.__all__:
                model_checker.__all__.append(item)


def remove_compatibility_layer():
    """
    Remove the compatibility layer from the main model_checker module.
    
    This function can be called when the compatibility period ends.
    """
    import sys
    import model_checker
    
    # Remove legacy classes and functions
    legacy_items = [
        'BuildExample', 'BuildModule', 'BuildProject',
        'ModelExplorer', 'check_formula'
    ]
    
    for item in legacy_items:
        if hasattr(model_checker, item):
            delattr(model_checker, item)
        
        # Remove from __all__ if it exists
        if hasattr(model_checker, '__all__') and item in model_checker.__all__:
            model_checker.__all__.remove(item)


# Context manager for temporary compatibility
class CompatibilityContext:
    """Context manager for temporarily enabling compatibility layer."""
    
    def __enter__(self):
        install_compatibility_layer()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        remove_compatibility_layer()


# Example usage and testing
def _example_compatibility():
    """Example of compatibility layer usage."""
    
    print("Testing compatibility layer...")
    
    # Test legacy settings translation
    old_settings = {
        "N": 3,
        "max_time": 5,
        "contingent": True,
        "expectation": True
    }
    
    print(f"Old settings: {old_settings}")
    
    try:
        config = migrate_settings_dict(old_settings)
        print(f"Migrated config: {config}")
        print(f"Back to dict: {config.to_dict()}")
    except Exception as e:
        print(f"Migration failed: {e}")
    
    # Test compatibility context
    with CompatibilityContext():
        print("Compatibility layer installed")
        # Legacy code would work here
    
    print("Compatibility layer removed")


if __name__ == "__main__":
    _example_compatibility()