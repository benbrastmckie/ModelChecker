"""
Logos Theory: Modular Implementation of Hyperintensional Truthmaker Semantics

This theory provides a modular approach to logical operators organized by domain:
- Extensional: Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥)
- Modal: Necessity and possibility operators (□,◇)
- Constitutive: Ground, essence, and identity operators (≡,≤,⊑,≼)
- Counterfactual: Counterfactual conditional operators (□→,◇→)
- Relevance: Content-sensitive relevance operators
"""

from .semantic import LogosSemantics, LogosProposition, LogosModelStructure
from .operators import LogosOperatorRegistry

def get_theory(subtheories=None):
    """
    Get a logos theory instance with specified subtheories.
    
    Args:
        subtheories: List of subtheory names to load, or None for all
    
    Returns:
        Dict with 'semantics', 'proposition', 'model' classes
    """
    registry = LogosOperatorRegistry()
    if subtheories:
        registry.load_subtheories(subtheories)
    else:
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual'])
    
    return {
        'semantics': LogosSemantics,
        'proposition': LogosProposition,
        'model': LogosModelStructure,
        'operators': registry.get_operators()
    }

# Public API
Semantics = LogosSemantics
Proposition = LogosProposition  
ModelStructure = LogosModelStructure