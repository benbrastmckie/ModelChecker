"""Unit tests for UI builder classes."""

import pytest
from unittest.mock import Mock, MagicMock, patch
from model_checker.jupyter.tests.fixtures.mock_widgets import create_mock_widgets


class TestModelExplorerUIBuilder:
    """Test ModelExplorer UI builder."""
    
    @pytest.fixture
    def mock_parent(self):
        """Create a mock parent object."""
        parent = Mock()
        parent.available_theories = ['theory1', 'theory2']
        parent.theory_name = 'theory1'
        parent.settings = {
            'N': 3,
            'max_time': 5.0,
            'contingent': False,
            'non_empty': True,
            'expectation': True,
            'print_constraints': False
        }
        parent._on_theory_change = Mock()
        parent._on_check_click = Mock()
        parent._on_next_model_click = Mock()
        parent._on_viz_change = Mock()
        parent._update_setting = Mock()
        return parent
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_build_main_ui(self, mock_parent):
        """Test building the main UI."""
        from model_checker.jupyter.ui_builders import ModelExplorerUIBuilder
        
        builder = ModelExplorerUIBuilder(mock_parent)
        ui = builder.build_main_ui()
        
        # Check that UI components were created
        assert hasattr(mock_parent, 'formula_input')
        assert hasattr(mock_parent, 'premises_input')
        assert hasattr(mock_parent, 'theory_selector')
        assert hasattr(mock_parent, 'check_button')
        assert hasattr(mock_parent, 'next_model_button')
        assert hasattr(mock_parent, 'viz_selector')
        assert hasattr(mock_parent, 'output_area')
        
        # Check UI structure
        assert ui is not None
        assert hasattr(ui, 'children')
        assert len(ui.children) == 2  # control_panel and output_area
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', False)
    def test_build_main_ui_without_ipywidgets(self, mock_parent):
        """Test that building UI fails without ipywidgets."""
        from model_checker.jupyter.ui_builders import ModelExplorerUIBuilder
        
        builder = ModelExplorerUIBuilder(mock_parent)
        with pytest.raises(ImportError, match="ipywidgets is required"):
            builder.build_main_ui()
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_build_settings_accordion(self, mock_parent):
        """Test building the settings accordion."""
        from model_checker.jupyter.ui_builders import ModelExplorerUIBuilder
        
        builder = ModelExplorerUIBuilder(mock_parent)
        accordion = builder._build_settings_accordion()
        
        # Check that sliders and checkboxes were created
        assert hasattr(mock_parent, 'n_slider')
        assert hasattr(mock_parent, 'max_time_slider')
        assert hasattr(mock_parent, 'contingent_checkbox')
        assert hasattr(mock_parent, 'non_empty_checkbox')
        assert hasattr(mock_parent, 'expectation_selector')
        assert hasattr(mock_parent, 'print_constraints_checkbox')
        
        # Check accordion structure
        assert accordion is not None
        assert hasattr(accordion, 'children')
        assert hasattr(accordion, 'set_title')


class TestFormulaCheckerUIBuilder:
    """Test FormulaChecker UI builder."""
    
    @pytest.fixture
    def mock_parent(self):
        """Create a mock parent object."""
        parent = Mock()
        parent.available_theories = ['theory1', 'theory2']
        parent.theory_name = 'theory1'
        parent._on_check_click = Mock()
        return parent
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_build_main_ui(self, mock_parent):
        """Test building the main UI."""
        from model_checker.jupyter.ui_builders import FormulaCheckerUIBuilder
        
        builder = FormulaCheckerUIBuilder(mock_parent)
        ui = builder.build_main_ui()
        
        # Check that UI components were created
        assert hasattr(mock_parent, 'formula_input')
        assert hasattr(mock_parent, 'premises_input')
        assert hasattr(mock_parent, 'theory_selector')
        assert hasattr(mock_parent, 'check_button')
        assert hasattr(mock_parent, 'output_area')
        
        # Check UI structure
        assert ui is not None
        assert hasattr(ui, 'children')
        assert len(ui.children) == 5  # formula, premises, theory, button, output
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_build_formula_input(self, mock_parent):
        """Test building formula input widget."""
        from model_checker.jupyter.ui_builders import FormulaCheckerUIBuilder
        
        builder = FormulaCheckerUIBuilder(mock_parent)
        widget = builder._build_formula_input()
        
        assert widget is not None
        assert widget.value == 'p → q'
        assert widget.description == 'Formula:'
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_build_check_button(self, mock_parent):
        """Test building check button."""
        from model_checker.jupyter.ui_builders import FormulaCheckerUIBuilder
        
        builder = FormulaCheckerUIBuilder(mock_parent)
        button = builder._build_check_button()
        
        assert button is not None
        assert button.description == 'Check Formula'
        assert button.button_style == 'primary'
        
        # Test that click handler was registered
        button.click()
        mock_parent._on_check_click.assert_called_once()
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_theory_dropdown_with_observer(self, mock_parent):
        """Test that theory dropdown observer is set if method exists."""
        mock_parent._on_theory_change = Mock()
        
        from model_checker.jupyter.ui_builders import FormulaCheckerUIBuilder
        
        builder = FormulaCheckerUIBuilder(mock_parent)
        dropdown = builder._build_theory_dropdown()
        
        assert dropdown is not None
        assert dropdown.value == 'theory1'
        assert dropdown.options == ['theory1', 'theory2']
    
    @patch('model_checker.jupyter.ui_builders.HAVE_IPYWIDGETS', True)
    @patch('model_checker.jupyter.ui_builders.widgets', create_mock_widgets())
    def test_theory_dropdown_without_observer(self, mock_parent):
        """Test that theory dropdown works without observer method."""
        # Remove the _on_theory_change method
        del mock_parent._on_theory_change
        
        from model_checker.jupyter.ui_builders import FormulaCheckerUIBuilder
        
        builder = FormulaCheckerUIBuilder(mock_parent)
        dropdown = builder._build_theory_dropdown()
        
        assert dropdown is not None
        assert dropdown.value == 'theory1'