"""
Standardized mock object factories for consistent testing.

Provides factory functions for creating properly configured mock objects
with reasonable defaults and customization options.
"""

from unittest.mock import Mock, MagicMock
from typing import Any, Dict, Optional, Union
from .test_data import TestTheories, TestSettings


class MockSemantics:
    """Standard mock semantics class."""
    DEFAULT_EXAMPLE_SETTINGS = TestSettings.DEFAULT_EXAMPLE
    DEFAULT_GENERAL_SETTINGS = TestSettings.DEFAULT_GENERAL
    
    def __init__(self):
        self.data = "test_data"
    
    def validate_model(self, model):
        return True


class MockProposition:
    """Mock proposition class."""
    pass


class MockModel:
    """Mock model class."""
    pass


class MockOperator:
    """Base mock operator class."""
    name = "MockOperator"
    arity = 2
    symbol = "∘"
    
    def __init__(self, name=None, arity=None, symbol=None):
        if name:
            self.name = name
        else:
            self.name = "MockOperator"
        if arity:
            self.arity = arity
        else:
            self.arity = 2
        if symbol:
            self.symbol = symbol
        else:
            self.symbol = "∘"


class MockOperatorOr(MockOperator):
    """Mock disjunction operator."""
    name = "MockOperatorOr"
    arity = 2
    symbol = "∨"


class MockOperatorAnd(MockOperator):
    """Mock conjunction operator.""" 
    name = "MockOperatorAnd"
    arity = 2
    symbol = "∧"


class MockNegation(MockOperator):
    """Mock negation operator."""
    name = "MockNegation"
    arity = 1
    symbol = "¬"


class MockConjunction(MockOperator):
    """Mock conjunction operator."""
    name = "MockConjunction"
    arity = 2
    symbol = "∧"


class MockDisjunction(MockOperator):
    """Mock disjunction operator."""
    name = "MockDisjunction"
    arity = 2
    symbol = "∨"


class MockNecessity(MockOperator):
    """Mock necessity operator."""
    name = "MockNecessity"
    arity = 1
    symbol = "□"


class MockObjectFactory:
    """Factory for creating standardized mock objects."""
    
    @staticmethod
    def create_build_module(components: Optional[Dict[str, Any]] = None) -> Mock:
        """Create BuildModule mock with specified components."""
        mock = Mock()
        mock.general_settings = TestSettings.DEFAULT_GENERAL
        mock.output_manager = Mock()
        mock.output_manager.should_save.return_value = False
        mock.interactive_manager = None
        
        # Add component mocks
        if components:
            for component_name, component_mock in components.items():
                setattr(mock, component_name, component_mock)
        else:
            # Default minimal components
            mock.loader = Mock()
            mock.runner = Mock()
            mock.comparison = Mock()
            mock.translation = Mock()
        
        return mock
    
    @staticmethod
    def create_theory_dict(theory_type: str = "minimal") -> Dict[str, Any]:
        """Create theory dictionary based on type."""
        if theory_type == "minimal":
            return TestTheories.MINIMAL.copy()
        elif theory_type == "with_operators":
            return TestTheories.WITH_OPERATORS.copy()
        elif theory_type == "complex":
            return TestTheories.COMPLEX.copy()
        else:
            raise ValueError(f"Unknown theory type: {theory_type}")
    
    @staticmethod
    def create_semantics(with_defaults: bool = True) -> MockSemantics:
        """Create mock semantics with optional default settings."""
        semantics = MockSemantics()
        if with_defaults:
            semantics.DEFAULT_GENERAL_SETTINGS = TestSettings.DEFAULT_GENERAL
            semantics.DEFAULT_EXAMPLE_SETTINGS = TestSettings.DEFAULT_EXAMPLE
        return semantics
    
    @staticmethod
    def create_runner(build_module: Optional[Mock] = None) -> Mock:
        """Create ModelRunner mock with build_module reference."""
        runner = Mock()
        runner.build_module = build_module or MockObjectFactory.create_build_module()
        runner.run_model_check.return_value = Mock(status="success")
        runner.run_examples.return_value = []
        return runner
    
    @staticmethod
    def create_comparison(build_module: Optional[Mock] = None) -> Mock:
        """Create ModelComparison mock with build_module reference."""
        comparison = Mock()
        comparison.build_module = build_module or MockObjectFactory.create_build_module()
        comparison.compare_semantics.return_value = []
        comparison.run_comparison.return_value = Mock(status="success")
        return comparison
    
    @staticmethod
    def create_translation() -> Mock:
        """Create OperatorTranslation mock."""
        translation = Mock()
        translation.translate.return_value = [["A"], ["B"], {"N": 2}]
        translation.translate_example.return_value = []
        return translation
    
    @staticmethod
    def create_loader(module_path: str = "/tmp/test.py") -> Mock:
        """Create ModuleLoader mock."""
        loader = Mock()
        loader.module_path = module_path
        loader.load_module.return_value = Mock()
        loader.discover_theory_module.return_value = Mock()
        return loader
    
    @staticmethod
    def create_flags(options: Union[Dict[str, Any], str] = None, **kwargs) -> Mock:
        """Create mock flags with specified options.
        
        Args:
            options: Either a dict of options or file_path as string
            **kwargs: Additional options when options is a string
        """
        defaults = {
            "file_path": "/tmp/test.py",
            "comparison": False,
            "interactive": False, 
            "iterations": False,
            "quiet": False,
            "output": None,  # None means use all formats by default
            "save": None  # None means --save flag not used
        }
        
        if isinstance(options, dict):
            # If options is a dict, use it to update defaults
            defaults.update(options)
        elif isinstance(options, str):
            # If options is a string, treat it as file_path
            defaults["file_path"] = options
            defaults.update(kwargs)
        elif options is not None:
            raise TypeError(f"Expected dict or str for options, got {type(options)}")
        else:
            # No options provided, just use kwargs
            defaults.update(kwargs)
            
        # Create mock that settings manager will recognize as a mock
        mock_flags = Mock(**defaults)
        # Ensure _parsed_args doesn't exist so it's recognized as mock
        if hasattr(mock_flags, '_parsed_args'):
            delattr(mock_flags, '_parsed_args')
        return mock_flags
    
    @staticmethod
    def create_complete_theory() -> Dict[str, Any]:
        """Create complete theory with all required components."""
        return {
            "semantics": MockSemantics,
            "proposition": MockProposition,
            "model": MockModel,
            "operators": {
                "\\neg": MockOperator("negation", 1, "¬"),
                "\\wedge": MockOperator("conjunction", 2, "∧")
            },
            "dictionary": {"&": "∧", "!": "¬"},
            "settings": TestSettings.DEFAULT_EXAMPLE
        }
    
    @staticmethod
    def create_mock_input_provider(responses: list) -> Mock:
        """Create mock input provider with predefined responses."""
        provider = Mock()
        provider.get_input.side_effect = responses
        return provider
    
    # Legacy compatibility methods for older tests
    @staticmethod  
    def MockOperator(name="MockOperator", arity=2, symbol="∘"):
        """Legacy method for creating mock operators."""
        return MockOperator(name, arity, symbol)

# Add class attributes for legacy compatibility - import from test_data to avoid conflicts
from .test_data import MockSemantics as TestDataMockSemantics, MockProposition as TestDataMockProposition, MockModel as TestDataMockModel
from .test_data import MockOperator, MockNegation, MockConjunction, MockDisjunction, MockNecessity
MockObjectFactory.MockSemantics = TestDataMockSemantics
MockObjectFactory.MockProposition = TestDataMockProposition
MockObjectFactory.MockModel = TestDataMockModel

# Add operator classes for legacy compatibility
MockObjectFactory.MockOperator = MockOperator
MockObjectFactory.MockOperatorOr = MockDisjunction  
MockObjectFactory.MockOperatorAnd = MockConjunction
MockObjectFactory.MockOperatorNot = MockNegation
MockObjectFactory.MockNegation = MockNegation
MockObjectFactory.MockConjunction = MockConjunction
MockObjectFactory.MockDisjunction = MockDisjunction
MockObjectFactory.MockNecessity = MockNecessity