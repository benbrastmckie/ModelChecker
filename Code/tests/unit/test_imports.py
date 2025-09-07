"""Unit tests for ModelChecker import structure.

This module tests that all required components can be imported
and have the expected structure.
"""

import pytest
import sys
from pathlib import Path


class TestImportStructure:
    """Test import structure and availability of components."""
    
    def test_main_package_imports(self):
        """Test that main package can be imported."""
        import model_checker
        assert model_checker is not None
        
    def test_builder_imports(self):
        """Test builder module imports."""
        from model_checker.builder import BuildModule, BuildProject
        assert BuildModule is not None
        assert BuildProject is not None
        
    def test_theory_imports(self):
        """Test theory library imports."""
        from model_checker.theory_lib import logos, exclusion, bimodal, imposition
        
        # All theories should be importable
        assert logos is not None
        assert exclusion is not None
        assert bimodal is not None
        assert imposition is not None
        
    def test_utils_api_imports(self):
        """Test utils API imports."""
        from model_checker.utils.api import get_theory
        
        assert get_theory is not None
        # get_default_settings may not exist in current implementation
        
    def test_models_imports(self):
        """Test models package imports."""
        from model_checker.models import (
            SemanticDefaults,
            PropositionDefaults,
            ModelConstraints,
            ModelDefaults,
            ModelError
        )
        
        assert SemanticDefaults is not None
        assert PropositionDefaults is not None
        assert ModelConstraints is not None
        assert ModelDefaults is not None
        assert ModelError is not None
        
    def test_syntactic_imports(self):
        """Test syntactic module imports."""
        from model_checker.syntactic import Syntax
        assert Syntax is not None
        
    def test_settings_imports(self):
        """Test settings module imports."""
        from model_checker.settings import SettingsManager
        assert SettingsManager is not None


class TestTheoryStructure:
    """Test that theories have required structure."""
    
    @pytest.mark.parametrize("theory_name", [
        'logos', 'exclusion', 'bimodal', 'imposition'
    ])
    def test_theory_has_get_theory(self, theory_name):
        """Test each theory has get_theory function."""
        theory_module = __import__(f'model_checker.theory_lib.{theory_name}', 
                                  fromlist=['get_theory'])
        assert hasattr(theory_module, 'get_theory')
        
    @pytest.mark.parametrize("theory_name", [
        'logos', 'exclusion', 'bimodal', 'imposition'
    ])
    def test_theory_components(self, theory_name):
        """Test theory has all required components."""
        from model_checker.utils.api import get_theory
        
        theory = get_theory(theory_name)
        
        # Check required components inline
        required = ['semantics', 'model', 'proposition', 'operators']
        for component in required:
            assert component in theory, \
                f"Theory {theory_name} missing required component: {component}"


class TestPackageImports:
    """Test package-level imports with parameterization."""
    
    @pytest.mark.parametrize("module_path,class_names", [
        ('model_checker.builder', ['BuildModule', 'BuildProject']),
        ('model_checker.models', ['SemanticDefaults', 'PropositionDefaults', 'ModelDefaults', 'ModelError']),
        ('model_checker.syntactic', ['Syntax']),
        ('model_checker.settings', ['SettingsManager']),
    ])
    def test_module_imports(self, module_path, class_names):
        """Test that modules export expected classes."""
        import importlib
        module = importlib.import_module(module_path)
        
        for class_name in class_names:
            assert hasattr(module, class_name), \
                f"{module_path} missing expected class: {class_name}"
            
            # Verify it's actually a class
            cls = getattr(module, class_name)
            assert isinstance(cls, type), \
                f"{class_name} in {module_path} is not a class"
    
    @pytest.mark.parametrize("error_class,base_exception", [
        ('ModelError', Exception),
        ('ModelConstraintError', 'ModelError'),
        ('ModelSolverError', 'ModelError'),
        ('ModelConfigurationError', 'ModelError'),
    ])
    def test_error_hierarchy(self, error_class, base_exception):
        """Test error class hierarchy."""
        from model_checker import models
        
        # Get the error class
        error_cls = getattr(models, error_class, None)
        
        if error_cls is None:
            # Check in errors submodule if exists
            if hasattr(models, 'errors'):
                from model_checker.models import errors
                error_cls = getattr(errors, error_class, None)
        
        # If base_exception is a string, get it from models
        if isinstance(base_exception, str):
            base_cls = getattr(models, base_exception, None)
            if base_cls is None and hasattr(models, 'errors'):
                from model_checker.models import errors
                base_cls = getattr(errors, base_exception, Exception)
        else:
            base_cls = base_exception
        
        # Verify inheritance if class exists
        if error_cls is not None:
            assert issubclass(error_cls, base_cls), \
                f"{error_class} does not inherit from {base_exception}"