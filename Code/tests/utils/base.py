"""Base classes for ModelChecker tests.

This module provides reusable base classes that encapsulate
common testing patterns and reduce code duplication.
"""

import pytest
from abc import ABC, abstractmethod
from typing import Dict, List, Any, Optional
from pathlib import Path


class BaseTheoryTest(ABC):
    """Base class for theory testing.
    
    Subclasses should implement get_theory_name() to specify
    which theory to test.
    """
    
    @abstractmethod
    def get_theory_name(self) -> str:
        """Return theory name to test.
        
        Returns:
            str: Name of the theory (e.g., 'logos', 'exclusion')
        """
        pass
    
    def test_theory_loads(self):
        """Test theory can be loaded."""
        from model_checker.utils.api import get_theory
        
        theory = get_theory(self.get_theory_name())
        assert theory is not None, f"Theory '{self.get_theory_name()}' could not be loaded"
    
    def test_theory_has_required_components(self):
        """Test theory has all required components."""
        from model_checker.utils.api import get_theory
        from tests.utils.assertions import assert_theory_components
        
        theory = get_theory(self.get_theory_name())
        assert_theory_components(theory)
    
    def test_theory_semantics(self):
        """Test theory semantics has required attributes."""
        from model_checker.utils.api import get_theory
        
        theory = get_theory(self.get_theory_name())
        semantics = theory['semantics']
        
        # Check for required semantic attributes
        assert hasattr(semantics, 'DEFAULT_EXAMPLE_SETTINGS')
        assert hasattr(semantics, 'DEFAULT_GENERAL_SETTINGS')
        
        # Settings should be dictionaries
        assert isinstance(semantics.DEFAULT_EXAMPLE_SETTINGS, dict)
        assert isinstance(semantics.DEFAULT_GENERAL_SETTINGS, dict)
    
    def test_theory_operators(self):
        """Test theory operators are properly defined."""
        from model_checker.utils.api import get_theory
        
        theory = get_theory(self.get_theory_name())
        operators = theory['operators']
        
        # Check basic operators exist
        basic_ops = ['wedge', 'vee', 'neg']
        for op in basic_ops:
            assert op in operators, f"Missing basic operator: {op}"
            
            operator = operators[op]
            assert hasattr(operator, 'symbol')
            assert hasattr(operator, 'arity')


class BaseCLITest:
    """Base class for CLI testing.
    
    Provides helper methods for running CLI commands and
    asserting on their results.
    """
    
    def run_cli(self, *args, **kwargs) -> Any:
        """Run CLI with arguments.
        
        Args:
            *args: CLI arguments
            **kwargs: Additional options for run_cli_command
            
        Returns:
            subprocess.CompletedProcess: Result of command execution
        """
        from tests.utils.helpers import run_cli_command
        return run_cli_command(list(args), **kwargs)
    
    def assert_cli_success(self, *args, **kwargs) -> Any:
        """Assert CLI command succeeds.
        
        Args:
            *args: CLI arguments
            **kwargs: Additional options for run_cli_command
            
        Returns:
            subprocess.CompletedProcess: Command result
            
        Raises:
            AssertionError: If command fails
        """
        from tests.utils.helpers import assert_cli_success
        return assert_cli_success(list(args), **kwargs)
    
    def assert_cli_failure(self, *args, expected_error: Optional[str] = None, **kwargs) -> Any:
        """Assert CLI command fails.
        
        Args:
            *args: CLI arguments
            expected_error: Optional error message to check for
            **kwargs: Additional options for run_cli_command
            
        Returns:
            subprocess.CompletedProcess: Command result
            
        Raises:
            AssertionError: If command succeeds or error doesn't match
        """
        from tests.utils.helpers import assert_cli_failure
        return assert_cli_failure(list(args), expected_error, **kwargs)


class BaseModelTest:
    """Base class for model testing.
    
    Provides helper methods for creating and validating models.
    """
    
    def create_model(self, settings: Optional[Dict[str, Any]] = None):
        """Create a model with given settings.
        
        Args:
            settings: Optional settings dictionary
            
        Returns:
            ModelDefaults: Created model instance
        """
        from model_checker.models import ModelDefaults
        
        if settings is None:
            settings = {'N': 3}
        
        return ModelDefaults(settings)
    
    def assert_model_valid(self, model):
        """Assert model is valid and satisfiable.
        
        Args:
            model: ModelDefaults instance to validate
            
        Raises:
            AssertionError: If model is invalid
        """
        from tests.utils.assertions import assert_model_satisfiable
        assert_model_satisfiable(model)
    
    def assert_model_invalid(self, model):
        """Assert model is unsatisfiable.
        
        Args:
            model: ModelDefaults instance to validate
            
        Raises:
            AssertionError: If model is satisfiable
        """
        from tests.utils.assertions import assert_model_unsatisfiable
        assert_model_unsatisfiable(model)


class BaseExampleTest:
    """Base class for example testing.
    
    Provides helper methods for working with examples.
    """
    
    def create_example(self, 
                      assumptions: List[str],
                      conclusions: List[str],
                      settings: Optional[Dict[str, Any]] = None) -> List:
        """Create an example structure.
        
        Args:
            assumptions: List of assumption formulas
            conclusions: List of conclusion formulas
            settings: Optional settings dictionary
            
        Returns:
            list: Example structure [assumptions, conclusions, settings]
        """
        if settings is None:
            settings = {'N': 3}
        
        return [assumptions, conclusions, settings]
    
    def validate_example(self, example: List):
        """Validate example structure.
        
        Args:
            example: Example list to validate
            
        Raises:
            AssertionError: If example structure is invalid
        """
        from tests.utils.assertions import assert_example_structure
        assert_example_structure(example)
    
    def run_example(self, example: List, theory_name: str = 'logos'):
        """Run an example through model checking.
        
        Args:
            example: Example to run
            theory_name: Theory to use
            
        Returns:
            str: Output from model checking
        """
        from tests.utils.helpers import capture_model_output
        return capture_model_output(example, theory_name)


class BaseIntegrationTest:
    """Base class for integration testing.
    
    Combines multiple components for end-to-end testing.
    """
    
    def create_test_project(self, tmp_path: Path, 
                          project_name: str = 'test_project',
                          theory_name: str = 'logos') -> Path:
        """Create a test project.
        
        Args:
            tmp_path: Temporary directory path
            project_name: Name of the project
            theory_name: Theory to use
            
        Returns:
            Path: Path to created project
        """
        from tests.utils.helpers import create_temp_project
        return create_temp_project(tmp_path, project_name, theory_name)
    
    def validate_project_structure(self, project_path: Path):
        """Validate project has expected structure.
        
        Args:
            project_path: Path to project directory
            
        Raises:
            AssertionError: If project structure is invalid
        """
        required_files = ['__init__.py', 'examples.py']
        
        for filename in required_files:
            file_path = project_path / filename
            assert file_path.exists(), f"Missing required file: {filename}"
            assert file_path.stat().st_size > 0, f"File {filename} is empty"
    
    def run_project_tests(self, project_path: Path):
        """Run tests for a project.
        
        Args:
            project_path: Path to project directory
            
        Returns:
            bool: True if tests pass
        """
        # Import and validate the project module
        import sys
        import importlib
        
        sys.path.insert(0, str(project_path.parent))
        try:
            module = importlib.import_module(project_path.name)
            
            # Check module has required attributes
            assert hasattr(module, 'examples')
            return True
            
        finally:
            sys.path.remove(str(project_path.parent))