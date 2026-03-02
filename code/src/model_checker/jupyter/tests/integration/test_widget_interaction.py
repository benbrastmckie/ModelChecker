"""Integration tests for widget interactions."""

import pytest
from unittest.mock import Mock, patch, MagicMock
from model_checker.jupyter.tests.fixtures.mock_widgets import create_mock_widgets, MockOutput


class TestModelExplorerIntegration:
    """Test ModelExplorer widget interactions."""
    
    @pytest.fixture
    def mock_dependencies(self):
        """Mock all required dependencies."""
        mock_widgets = create_mock_widgets()
        with patch('model_checker.jupyter.interactive.HAVE_IPYWIDGETS', True), \
             patch('model_checker.jupyter.interactive.widgets', mock_widgets), \
             patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True), \
             patch('model_checker.jupyter.ui_builders.widgets', mock_widgets), \
             patch('model_checker.jupyter.interactive.display'), \
             patch('model_checker.jupyter.interactive.clear_output'), \
             patch('model_checker.jupyter.interactive.HTML'):
            yield
    
    @pytest.fixture
    def mock_build_example(self):
        """Mock BuildExample class."""
        with patch('model_checker.builder.example.BuildExample') as mock:
            instance = Mock()
            instance.semantics = Mock()
            instance.semantics.run = Mock(return_value=True)
            mock.return_value = instance
            yield mock
    
    def test_model_explorer_initialization(self, mock_dependencies):
        """Test ModelExplorer initialization."""
        from model_checker.jupyter.interactive import ModelExplorer
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1', 'theory2']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    explorer = ModelExplorer(theory_name='theory1')
                    
                    assert explorer.theory_name == 'theory1'
                    assert explorer.available_theories == ['theory1', 'theory2']
                    assert explorer.model is None
                    mock_setup.assert_called_once()
    
    def test_check_button_click(self, mock_dependencies, mock_build_example):
        """Test check button click handler."""
        from model_checker.jupyter.interactive import ModelExplorer
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    explorer = ModelExplorer()
                    
                    # Set formula and premises
                    explorer.formula_input.value = "p → q"
                    explorer.premises_input.value = "p"
                    
                    # Simulate button click
                    explorer._on_check_click(None)
                    
                    # Check that BuildExample was called
                    mock_build_example.assert_called_once()
    
    def test_theory_change_handler(self, mock_dependencies):
        """Test theory change handler."""
        from model_checker.jupyter.interactive import ModelExplorer
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1', 'theory2']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    explorer = ModelExplorer(theory_name='theory1')
                    
                    # Simulate theory change
                    change = {'new': 'theory2'}
                    explorer._on_theory_change(change)
                    
                    assert explorer.theory_name == 'theory2'
    
    def test_setting_update(self, mock_dependencies):
        """Test updating settings."""
        from model_checker.jupyter.interactive import ModelExplorer
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    explorer = ModelExplorer()
                    
                    # Update a setting
                    explorer._update_setting('N', 5)
                    assert explorer.settings['N'] == 5
                    
                    explorer._update_setting('max_time', 10.0)
                    assert explorer.settings['max_time'] == 10.0


class TestFormulaCheckerIntegration:
    """Test FormulaChecker widget interactions."""
    
    @pytest.fixture
    def mock_dependencies(self):
        """Mock all required dependencies."""
        mock_widgets = create_mock_widgets()
        with patch('model_checker.jupyter.interactive.HAVE_IPYWIDGETS', True), \
             patch('model_checker.jupyter.interactive.widgets', mock_widgets), \
             patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True), \
             patch('model_checker.jupyter.ui_builders.widgets', mock_widgets), \
             patch('model_checker.jupyter.interactive.display'), \
             patch('model_checker.jupyter.interactive.clear_output'), \
             patch('model_checker.jupyter.interactive.HTML'):
            yield
    
    def test_formula_checker_initialization(self, mock_dependencies):
        """Test FormulaChecker initialization."""
        from model_checker.jupyter.interactive import FormulaChecker
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1', 'theory2']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    checker = FormulaChecker(theory_name='theory1')
                    
                    assert checker.theory_name == 'theory1'
                    assert checker.available_theories == ['theory1', 'theory2']
    
    def test_set_formula(self, mock_dependencies):
        """Test setting formula programmatically."""
        from model_checker.jupyter.interactive import FormulaChecker
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    checker = FormulaChecker()
                    
                    # Set formula
                    checker.set_formula("p ∧ q")
                    
                    # Should be normalized to LaTeX
                    assert "\\wedge" in checker.formula_input.value or "∧" in checker.formula_input.value
    
    def test_set_premises_list(self, mock_dependencies):
        """Test setting premises as a list."""
        from model_checker.jupyter.interactive import FormulaChecker
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    checker = FormulaChecker()
                    
                    # Set premises as list
                    checker.set_premises(["p", "q → r"])
                    
                    # Should be joined with newlines
                    assert "p" in checker.premises_input.value
                    assert "q" in checker.premises_input.value
    
    def test_check_formula_method(self, mock_dependencies):
        """Test check_formula method triggers button click."""
        from model_checker.jupyter.interactive import FormulaChecker
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    checker = FormulaChecker()
                    
                    # Mock the button click
                    checker.check_button.click = Mock()
                    
                    # Call check_formula
                    checker.check_formula()
                    
                    # Should trigger button click
                    checker.check_button.click.assert_called_once()
    
    def test_display_method(self, mock_dependencies):
        """Test display method."""
        from model_checker.jupyter.interactive import FormulaChecker
        
        with patch('model_checker.jupyter.environment.setup_environment') as mock_setup:
            mock_setup.return_value = {"status": "success"}
            
            with patch('model_checker.jupyter.environment.get_available_theories') as mock_theories:
                mock_theories.return_value = ['theory1']
                
                with patch('model_checker.theory_lib.get_semantic_theories') as mock_semantics:
                    mock_semantics.return_value = {'test': Mock()}
                    
                    with patch('model_checker.jupyter.interactive.display') as mock_display:
                        checker = FormulaChecker()
                        
                        # Call display
                        checker.display()
                        
                        # Should call display with the UI
                        mock_display.assert_called_once_with(checker.ui)