"""Mock widget fixtures for testing Jupyter integration.

This module provides mock implementations of ipywidgets components
to enable testing without requiring a real Jupyter environment.
"""

from unittest.mock import Mock, MagicMock
from typing import Any, Dict, List, Optional


class MockWidget:
    """Base mock widget class."""
    
    def __init__(self, **kwargs):
        """Initialize mock widget with attributes."""
        self.value = kwargs.get('value', None)
        self.description = kwargs.get('description', '')
        self.disabled = kwargs.get('disabled', False)
        self.layout = kwargs.get('layout', MockLayout())
        self.style = kwargs.get('style', {})
        self._observers = []
        
    def observe(self, handler, names=['value']):
        """Mock observe method for event handling."""
        self._observers.append((handler, names))
        
    def unobserve_all(self):
        """Mock unobserve_all method."""
        self._observers.clear()


class MockDropdown(MockWidget):
    """Mock Dropdown widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock dropdown."""
        super().__init__(**kwargs)
        self.options = kwargs.get('options', [])
        self.value = kwargs.get('value', self.options[0] if self.options else None)


class MockButton(MockWidget):
    """Mock Button widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock button."""
        super().__init__(**kwargs)
        self.description = kwargs.get('description', 'Button')
        self.button_style = kwargs.get('button_style', '')
        self._click_handlers = []
        
    def on_click(self, handler):
        """Mock on_click method."""
        self._click_handlers.append(handler)
        
    def click(self):
        """Simulate button click."""
        for handler in self._click_handlers:
            handler(self)


class MockTextarea(MockWidget):
    """Mock Textarea widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock textarea."""
        super().__init__(**kwargs)
        self.value = kwargs.get('value', '')
        self.placeholder = kwargs.get('placeholder', '')
        self.rows = kwargs.get('rows', 10)


class MockCheckbox(MockWidget):
    """Mock Checkbox widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock checkbox."""
        super().__init__(**kwargs)
        self.value = kwargs.get('value', False)
        self.indent = kwargs.get('indent', True)


class MockOutput(MockWidget):
    """Mock Output widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock output."""
        super().__init__(**kwargs)
        self._outputs = []
        
    def clear_output(self, wait=False):
        """Mock clear_output method."""
        self._outputs.clear()
        
    def append_stdout(self, text):
        """Mock append_stdout method."""
        self._outputs.append(('stdout', text))
        
    def append_stderr(self, text):
        """Mock append_stderr method."""
        self._outputs.append(('stderr', text))
        
    def __enter__(self):
        """Context manager entry."""
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        if exc_val:
            self.append_stderr(str(exc_val))


class MockVBox(MockWidget):
    """Mock VBox container."""
    
    def __init__(self, children=None, **kwargs):
        """Initialize mock VBox."""
        super().__init__(**kwargs)
        self.children = children or []


class MockHBox(MockWidget):
    """Mock HBox container."""
    
    def __init__(self, children=None, **kwargs):
        """Initialize mock HBox."""
        super().__init__(**kwargs)
        self.children = children or []


class MockTab(MockWidget):
    """Mock Tab widget."""
    
    def __init__(self, children=None, **kwargs):
        """Initialize mock Tab."""
        super().__init__(**kwargs)
        self.children = children or []
        self.selected_index = 0
        self._titles = {}
        
    def set_title(self, index, title):
        """Mock set_title method."""
        self._titles[index] = title


class MockLayout:
    """Mock Layout object."""
    
    def __init__(self, **kwargs):
        """Initialize mock layout."""
        self.width = kwargs.get('width', 'auto')
        self.height = kwargs.get('height', 'auto')
        self.display = kwargs.get('display', 'block')


class MockIPython:
    """Mock IPython display module."""
    
    @staticmethod
    def display(*args, **kwargs):
        """Mock display function."""
        pass
        
    @staticmethod
    def clear_output(wait=False):
        """Mock clear_output function."""
        pass
        
    class HTML:
        """Mock HTML display class."""
        
        def __init__(self, html):
            """Initialize with HTML content."""
            self.html = html
            
    class Markdown:
        """Mock Markdown display class."""
        
        def __init__(self, markdown):
            """Initialize with Markdown content."""
            self.markdown = markdown


class MockText(MockWidget):
    """Mock Text widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock text input."""
        super().__init__(**kwargs)
        self.value = kwargs.get('value', '')
        self.placeholder = kwargs.get('placeholder', '')


class MockAccordion(MockWidget):
    """Mock Accordion widget."""
    
    def __init__(self, children=None, **kwargs):
        """Initialize mock accordion."""
        super().__init__(**kwargs)
        self.children = children or []
        self.selected_index = None
        self._titles = {}
        
    def set_title(self, index, title):
        """Mock set_title method."""
        self._titles[index] = title


class MockIntSlider(MockWidget):
    """Mock IntSlider widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock int slider."""
        super().__init__(**kwargs)
        self.value = kwargs.get('value', 0)
        self.min = kwargs.get('min', 0)
        self.max = kwargs.get('max', 100)
        self.step = kwargs.get('step', 1)


class MockFloatSlider(MockWidget):
    """Mock FloatSlider widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock float slider."""
        super().__init__(**kwargs)
        self.value = kwargs.get('value', 0.0)
        self.min = kwargs.get('min', 0.0)
        self.max = kwargs.get('max', 1.0)
        self.step = kwargs.get('step', 0.01)


class MockRadioButtons(MockWidget):
    """Mock RadioButtons widget."""
    
    def __init__(self, **kwargs):
        """Initialize mock radio buttons."""
        super().__init__(**kwargs)
        self.options = kwargs.get('options', [])
        self.value = kwargs.get('value', self.options[0] if self.options else None)


class MockWidgetsModule:
    """Mock ipywidgets module."""
    
    def __init__(self):
        """Initialize mock widgets module."""
        self.Text = MockText
        self.Textarea = MockTextarea
        self.Button = MockButton
        self.Dropdown = MockDropdown
        self.Checkbox = MockCheckbox
        self.IntSlider = MockIntSlider
        self.FloatSlider = MockFloatSlider
        self.RadioButtons = MockRadioButtons
        self.Output = MockOutput
        self.VBox = MockVBox
        self.HBox = MockHBox
        self.Tab = MockTab
        self.Accordion = MockAccordion
        self.Layout = MockLayout


def create_mock_widgets():
    """Create a complete mock widgets module.
    
    Returns:
        MockWidgetsModule: Mock ipywidgets module
    """
    return MockWidgetsModule()


def create_mock_ipython():
    """Create mock IPython display module.
    
    Returns:
        MockIPython: Mock IPython display module
    """
    return MockIPython()


def patch_jupyter_imports():
    """Create a context manager that patches Jupyter imports.
    
    Returns:
        dict: Dictionary of patches to apply
    """
    from unittest.mock import patch
    
    patches = {
        'ipywidgets': create_mock_widgets(),
        'IPython.display': create_mock_ipython(),
    }
    
    return patches