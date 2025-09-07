"""Mock theory implementations for testing.

This module provides mock implementations of theories and their components
for use in tests that need to isolate from actual theory implementations.
"""

from unittest.mock import Mock, MagicMock


def create_mock_theory(name='test'):
    """Create a complete mock theory for testing.
    
    Args:
        name: Name of the mock theory
        
    Returns:
        dict: Mock theory dictionary with all required components
    """
    # Create mock semantics class
    mock_semantics = type('MockSemantics', (), {
        'DEFAULT_EXAMPLE_SETTINGS': {'N': 2, 'max_time': 5},
        'DEFAULT_GENERAL_SETTINGS': {
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'print_impossible': False,
            'maximize': False
        },
        '__init__': lambda self: None
    })
    
    # Create mock model class
    mock_model = MagicMock()
    mock_model.__name__ = 'MockModel'
    
    # Create mock proposition class
    mock_proposition = MagicMock()
    mock_proposition.__name__ = 'MockProposition'
    
    # Create mock operators
    mock_operators = {
        'wedge': MagicMock(symbol='∧', arity=2, name='wedge'),
        'vee': MagicMock(symbol='∨', arity=2, name='vee'),
        'neg': MagicMock(symbol='¬', arity=1, name='neg'),
        'arrow': MagicMock(symbol='→', arity=2, name='arrow'),
    }
    
    # Assemble theory dictionary
    theory = {
        'name': name,
        'semantics': mock_semantics,
        'model': mock_model,
        'proposition': mock_proposition,
        'operators': mock_operators
    }
    
    return theory


def create_mock_build_example():
    """Create a mock BuildExample for testing.
    
    Returns:
        Mock: Mock BuildExample instance
    """
    mock_example = Mock()
    mock_example.name = 'test_example'
    mock_example.theory = create_mock_theory()
    mock_example.settings = {'N': 2}
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.satisfiable = True
    
    return mock_example


def create_mock_build_module():
    """Create a mock BuildModule for testing.
    
    Returns:
        Mock: Mock BuildModule instance
    """
    mock_module = Mock()
    mock_module.module_name = 'test_module'
    mock_module.module_path = '/tmp/test_module.py'
    mock_module.semantic_theories = {'Test': create_mock_theory()}
    mock_module.example_range = {
        'TEST': [[], ['A'], {'N': 2}]
    }
    mock_module.general_settings = {
        'print_constraints': False,
        'print_z3': False
    }
    
    return mock_module


def create_mock_model_structure():
    """Create a mock ModelDefaults structure for testing.
    
    Returns:
        Mock: Mock ModelDefaults instance
    """
    mock_model = Mock()
    mock_model.z3_model = Mock()
    mock_model.z3_model_status = True
    mock_model.satisfiable = True
    mock_model.timeout = False
    mock_model.settings = {'N': 2, 'print_z3': False}
    mock_model.premises = []
    mock_model.conclusions = []
    mock_model.N = 2
    
    # Add print methods
    mock_model.print_all = Mock()
    mock_model.print_input_sentences = Mock()
    mock_model.print_grouped_constraints = Mock()
    mock_model.print_model = Mock()
    
    return mock_model