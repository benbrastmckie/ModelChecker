"""
Logos Theory: Modular Implementation of Hyperintensional Truthmaker Semantics

This theory provides a modular approach to logical operators organized by domain:
- Extensional: Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥)
- Modal: Necessity and possibility operators (□,◇)
- Constitutive: Ground, essence, and identity operators (≡,≤,⊑,≼)
- Counterfactual: Counterfactual conditional operators (□→,◇→)
- Relevance: Content-sensitive relevance operators

API:
    get_theory(subtheories=None): Get theory instance with specified subtheories
    list_subtheories(): Get available subtheories with descriptions
    Core classes: LogosSemantics, LogosProposition, LogosModelStructure
    Registry: LogosOperatorRegistry for dynamic operator loading
"""

from .semantic import LogosSemantics, LogosProposition, LogosModelStructure
from .operators import LogosOperatorRegistry
from .subtheories import list_subtheories, AVAILABLE_SUBTHEORIES
from .examples import get_examples_by_subtheory, get_examples_by_type, get_example_stats
from .iterate import LogosModelIterator, iterate_example

def get_theory(subtheories=None):
    """
    Get a logos theory instance with specified subtheories.
    
    Args:
        subtheories: List of subtheory names to load, or None for default set
                    Available: ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']
    
    Returns:
        Dict with 'semantics', 'proposition', 'model' classes and 'operators' collection
        
    Examples:
        # Load all default subtheories
        theory = get_theory()
        
        # Load only specific subtheories  
        theory = get_theory(['extensional', 'modal'])
        
        # Access components
        semantics_class = theory['semantics']
        operators = theory['operators']
    """
    registry = LogosOperatorRegistry()
    if subtheories:
        registry.load_subtheories(subtheories)
    else:
        # Default: load core subtheories (excluding relevance which is experimental)
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual'])
    
    return {
        'semantics': LogosSemantics,
        'proposition': LogosProposition,
        'model': LogosModelStructure,
        'operators': registry.get_operators()
    }

# Public API exports - class aliases for convenience
Semantics = LogosSemantics
Proposition = LogosProposition  
ModelStructure = LogosModelStructure
OperatorRegistry = LogosOperatorRegistry

__all__ = [
    # Main API
    'get_theory',
    'list_subtheories',
    'get_examples_by_subtheory',
    'get_examples_by_type', 
    'get_example_stats',
    
    # Core classes
    'LogosSemantics',
    'LogosProposition', 
    'LogosModelStructure',
    'LogosOperatorRegistry',
    
    # Iterator support
    'LogosModelIterator',
    'iterate_example',
    
    # Convenience aliases
    'Semantics',
    'Proposition',
    'ModelStructure', 
    'OperatorRegistry',
    
    # Constants
    'AVAILABLE_SUBTHEORIES'
]