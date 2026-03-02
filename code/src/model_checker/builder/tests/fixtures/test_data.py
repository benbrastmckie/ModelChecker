"""
Centralized test data for consistent testing across builder test suite.

This module provides standardized test data, preventing duplication
and ensuring consistency across all test files.
"""

from unittest.mock import Mock


# Import mock classes for theory data
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults
from model_checker.syntactic.collection import OperatorCollection

class MockSemantics(SemanticDefaults):
    """Mock semantics class for test data."""
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2, "contingent": False}
    DEFAULT_GENERAL_SETTINGS = {"print_impossible": False, "save_output": False}


class MockProposition(PropositionDefaults):
    """Mock proposition class for test data."""
    pass


class MockModel(ModelDefaults):
    """Mock model class for test data."""
    pass


class MockOperator:
    """Mock operator class for test data."""
    name = "MockOperator"
    
    def __init__(self, name="MockOperator", arity=2, symbol="∘"):
        self.name = name
        self.arity = arity 
        self.symbol = symbol


class MockNegation(MockOperator):
    """Mock negation operator."""
    name = "MockNegation"
    
    def __init__(self):
        super().__init__("MockNegation", 1, "¬")


class MockConjunction(MockOperator):
    """Mock conjunction operator."""
    name = "MockConjunction"
    
    def __init__(self):
        super().__init__("MockConjunction", 2, "∧")


class MockDisjunction(MockOperator):
    """Mock disjunction operator."""
    name = "MockDisjunction"
    
    def __init__(self):
        super().__init__("MockDisjunction", 2, "∨")


class MockNecessity(MockOperator):
    """Mock necessity operator."""
    name = "MockNecessity"
    
    def __init__(self):
        super().__init__("MockNecessity", 1, "□")


class TestTheories:
    """Standard theory configurations for testing."""
    
    # Create operator collections
    _minimal_ops = OperatorCollection()
    
    _with_operators_ops = OperatorCollection()
    _with_operators_ops.add_operator(MockNegation)
    _with_operators_ops.add_operator(MockConjunction)
    
    _complex_ops = OperatorCollection()
    _complex_ops.add_operator(MockNegation)
    _complex_ops.add_operator(MockConjunction)
    _complex_ops.add_operator(MockDisjunction)
    _complex_ops.add_operator(MockNecessity)
    
    MINIMAL = {
        "semantics": MockSemantics,
        "proposition": MockProposition,
        "model": MockModel, 
        "operators": _minimal_ops,
        "dictionary": {}
    }
    
    WITH_OPERATORS = {
        "semantics": MockSemantics,
        "proposition": MockProposition,
        "model": MockModel,
        "operators": _with_operators_ops,
        "dictionary": {"&": "∧", "!": "¬"}
    }
    
    COMPLEX = {
        "semantics": MockSemantics, 
        "proposition": MockProposition,
        "model": MockModel,
        "operators": _complex_ops,
        "dictionary": {"&": "∧", "|": "∨", "[]": "□"},
        "settings": {"N": 3, "modal": True}
    }
    
    # Alias for legacy tests
    COMPLETE_THEORY = COMPLEX
    ADVANCED = COMPLEX  # Alias for advanced theory tests
    
    # Theory-specific aliases for test compatibility
    LOGOS_THEORY = COMPLEX
    EXCLUSION_THEORY = WITH_OPERATORS


class TestExamples:
    """Standard example cases for testing."""
    
    SIMPLE_VALID = [["A"], ["B"], {"N": 2}]
    EMPTY_PREMISES = [[], ["A"], {"N": 2}]
    EMPTY_CONCLUSIONS = [["A"], [], {"N": 2}]
    MODAL_EXAMPLE = [["□A"], ["A"], {"N": 2}]
    INVALID_SETTINGS = [["A"], ["B"], {"N": -1}]
    
    # Alias for legacy tests
    BASIC_VALID = SIMPLE_VALID
    COMPLEX_VALID = [["(p ∧ q) → r", "p ∧ q"], ["r"], {"N": 3}]
    
    # Workflow-specific data
    WORKFLOW_DATA = {
        "input": SIMPLE_VALID,
        "expected_stages": ["load", "process", "output"],
        "expected_output_format": "models"
    }
    
    # Comparison testing data
    COMPARISON_THEORIES = [
        ("Theory1", SIMPLE_VALID),
        ("Theory2", MODAL_EXAMPLE)
    ]


class TestModules:
    """Standard module content for file-based testing."""
    
    MINIMAL_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
'''
    
    WITH_EXAMPLES = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "SIMPLE": [["A"], ["B"], {"N": 2}],
    "MODAL": [["□A"], ["A"], {"N": 2}],
    "EMPTY": [[], ["A"], {"N": 2}]
}
general_settings = {"print_impossible": False}
'''
    
    SYNTAX_ERROR_CONTENT = '''
this is not valid python syntax !
semantic_theories = undefined_variable
'''
    
    IMPORT_ERROR_CONTENT = '''
from nonexistent_package import something
semantic_theories = {}
example_range = {}
'''

    MISSING_ATTRIBUTES_CONTENT = '''
example_range = {"TEST": [["A"], ["B"], {"N": 2}]}
# Missing semantic_theories!
'''

    REALISTIC_MODULE_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Realistic": theory}
example_range = {
    "BASIC": [["A"], ["B"], {"N": 2}],
    "MODAL": [["□A"], ["A"], {"N": 2}]  
}
general_settings = {"save_output": False}
'''

    OUTPUT_ENABLED_MODULE_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {
    "OutputTest": theory
}

example_range = {
    "OUTPUT_EXAMPLE": [
        ["p ∧ q"],
        ["p"], 
        {"N": 2, "expectation": True}
    ]
}

general_settings = {
    "save_output": True,
    "print_impossible": False
}
'''

    # Additional module contents for component integration tests
    LOGOS_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {
    "LogosTest": theory
}

example_range = {
    "LOGOS_EXAMPLE": [
        ["p ∧ q"],
        ["p"], 
        {"N": 2, "expectation": True}
    ]
}

general_settings = {
    "save_output": False,
    "print_impossible": False
}
'''

    EXCLUSION_CONTENT = '''
from model_checker.theory_lib.exclusion import get_theory

theory = get_theory(['unilateral'])
semantic_theories = {
    "ExclusionTest": theory
}

example_range = {
    "EXCLUSION_EXAMPLE": [
        ["p ∧ q"],
        ["p"], 
        {"N": 2, "expectation": True}
    ]
}

general_settings = {
    "save_output": False
}
'''

    MULTI_THEORY_CONTENT = '''
from model_checker.theory_lib.logos import get_theory as get_logos_theory
from model_checker.theory_lib.exclusion import get_theory as get_exclusion_theory

logos_theory = get_logos_theory(['extensional'])
exclusion_theory = get_exclusion_theory(['unilateral'])

semantic_theories = {
    "Logos": logos_theory,
    "Exclusion": exclusion_theory
}

example_range = {
    "MULTI_TEST": [
        ["p ∧ q"],
        ["p"], 
        {"N": 2, "expectation": True}
    ]
}

general_settings = {
    "save_output": False
}
'''

    COMPLETE_MODULE_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Complete": theory}

example_range = {
    "COMPLETE_EXAMPLE": [["p"], ["p"], {"N": 2}]
}

general_settings = {
    "save_output": False,
    "print_impossible": False
}
'''


class TestFlags:
    """Standard flag configurations for testing."""
    
    @staticmethod
    def create_minimal(**overrides):
        """Create minimal flags with optional overrides."""
        defaults = {
            "file_path": "/tmp/test.py",
            "comparison": False, 
            "interactive": False,
            "iterations": False,
            "quiet": False
        }
        defaults.update(overrides)
        return Mock(**defaults)
    
    @staticmethod  
    def create_with_comparison(**overrides):
        """Create flags with comparison enabled."""
        return TestFlags.create_minimal(comparison=True, **overrides)
    
    @staticmethod
    def create_interactive(**overrides):
        """Create flags with interactive mode enabled."""  
        return TestFlags.create_minimal(interactive=True, **overrides)
    
    @staticmethod
    def create_with_iterations(**overrides):
        """Create flags with iterations enabled."""
        return TestFlags.create_minimal(iterations=True, **overrides)


class TestSettings:
    """Standard settings configurations for testing."""
    
    DEFAULT_GENERAL = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False
    }
    
    DEFAULT_EXAMPLE = {
        "N": 2,
        "contingent": False,
        "expectation": True
    }
    
    CUSTOM_GENERAL = {
        "print_impossible": True,
        "save_output": True,
        "output_directory": "/tmp/test_output"
    }
    
    CUSTOM_EXAMPLE = {
        "N": 3,
        "modal": True,
        "reflexive": True
    }


class TestConstants:
    """Common test constants and values."""
    
    VALID_FORMULAS = [
        "A",
        "(A \\wedge B)", 
        "\\neg \\Box A",
        "A → B",
        "□(A → B) → (□A → □B)"
    ]
    
    INVALID_FORMULAS = [
        "A ∧ B",  # Unicode not allowed in LaTeX context
        "",       # Empty formula
        None      # None value
    ]
    
    TIMEOUT_VALUES = [1, 5, 10, 30]  # Various timeout scenarios
    
    N_VALUES = [2, 3, 4, 5, 6]  # Valid N values for testing
    
    # Legacy test constants
    COMPLETE_THEORY = TestTheories.COMPLEX
    BASIC_VALID = TestExamples.SIMPLE_VALID
    REALISTIC_MODULE_CONTENT = TestModules.REALISTIC_MODULE_CONTENT
    
    # Additional constants needed by legacy tests
    DEFAULT_SETTINGS = TestSettings.DEFAULT_GENERAL
    TEST_FLAGS_CONFIGS = {
        "basic": Mock(file_path="/tmp/test.py", comparison=False, interactive=False)
    }
    
    # Dictionary constants for serialization tests
    STANDARD_DICTIONARY = {"&": "∧", "|": "∨", "!": "¬", "[]": "□"}
    UNICODE_DICTIONARY = {"and": "∧", "or": "∨", "not": "¬", "necessarily": "□"}
    
    # Default semantic theory for runner tests
    DEFAULT_SEMANTIC_THEORY = TestTheories.MINIMAL
    ADVANCED_SEMANTIC_THEORY = TestTheories.ADVANCED