"""Unit tests for Jupyter exception hierarchy."""

import pytest
from model_checker.jupyter.exceptions import (
    JupyterError,
    JupyterEnvironmentError,
    JupyterDependencyError,
    JupyterWidgetError,
    JupyterVisualizationError,
    JupyterFormulaError,
    JupyterTheoryError,
    JupyterTimeoutError
)


class TestJupyterExceptions:
    """Test custom exception classes."""
    
    def test_base_exception(self):
        """Test base JupyterError."""
        with pytest.raises(JupyterError) as exc_info:
            raise JupyterError("Test error")
        assert str(exc_info.value) == "Test error"
    
    def test_environment_error(self):
        """Test JupyterEnvironmentError."""
        with pytest.raises(JupyterEnvironmentError) as exc_info:
            raise JupyterEnvironmentError("Environment issue")
        assert "Environment issue" in str(exc_info.value)
        assert isinstance(exc_info.value, JupyterError)
    
    def test_dependency_error_with_feature(self):
        """Test JupyterDependencyError with feature specified."""
        error = JupyterDependencyError("ipywidgets", "ModelExplorer")
        assert error.dependency == "ipywidgets"
        assert error.feature == "ModelExplorer"
        assert "ModelExplorer requires ipywidgets" in str(error)
        assert "pip install model-checker[jupyter]" in str(error)
    
    def test_dependency_error_without_feature(self):
        """Test JupyterDependencyError without feature."""
        error = JupyterDependencyError("matplotlib")
        assert error.dependency == "matplotlib"
        assert error.feature is None
        assert "Missing required dependency: matplotlib" == str(error)
    
    def test_widget_error(self):
        """Test JupyterWidgetError."""
        with pytest.raises(JupyterWidgetError) as exc_info:
            raise JupyterWidgetError("Widget creation failed")
        assert "Widget creation failed" in str(exc_info.value)
    
    def test_visualization_error_with_reason(self):
        """Test JupyterVisualizationError with reason."""
        error = JupyterVisualizationError("graph", "Missing networkx")
        assert error.viz_type == "graph"
        assert error.reason == "Missing networkx"
        assert "Failed to create graph visualization: Missing networkx" == str(error)
    
    def test_visualization_error_without_reason(self):
        """Test JupyterVisualizationError without reason."""
        error = JupyterVisualizationError("tree")
        assert error.viz_type == "tree"
        assert error.reason is None
        assert "Failed to create tree visualization" == str(error)
    
    def test_formula_error(self):
        """Test JupyterFormulaError."""
        error = JupyterFormulaError("p & q", "Invalid operator")
        assert error.formula == "p & q"
        assert error.issue == "Invalid operator"
        assert "Error processing formula 'p & q': Invalid operator" == str(error)
    
    def test_theory_error(self):
        """Test JupyterTheoryError."""
        error = JupyterTheoryError("unknown_theory", "Theory not found")
        assert error.theory_name == "unknown_theory"
        assert error.issue == "Theory not found"
        assert "Error with theory 'unknown_theory': Theory not found" == str(error)
    
    def test_timeout_error(self):
        """Test JupyterTimeoutError."""
        error = JupyterTimeoutError("Model checking", 10.5)
        assert error.operation == "Model checking"
        assert error.timeout == 10.5
        assert "Model checking timed out after 10.5 seconds" == str(error)
    
    def test_exception_hierarchy(self):
        """Test that all exceptions inherit from JupyterError."""
        exceptions = [
            JupyterEnvironmentError("test"),
            JupyterDependencyError("test"),
            JupyterWidgetError("test"),
            JupyterVisualizationError("test"),
            JupyterFormulaError("test", "test"),
            JupyterTheoryError("test", "test"),
            JupyterTimeoutError("test", 1.0)
        ]
        
        for exc in exceptions:
            assert isinstance(exc, JupyterError)
            assert isinstance(exc, Exception)