"""
Extensional Subtheory for Logos Theory

This subtheory implements extensional (extensional) logical operators:
- Negation (¬)
- Conjunction (∧) 
- Disjunction (∨)
- Material Implication (→)
- Biconditional (↔)
- Top (⊤)
- Bottom (⊥)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .operators import (
    get_operators,
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
    TopOperator,
    BotOperator
)

def get_examples():
    """
    Get all extensional examples (lazy loaded to avoid circular imports).

    Returns:
        dict: Dictionary containing all extensional examples
    """
    # Lazy import to avoid circular dependency
    from .examples import countermodel_examples, theorem_examples, unit_tests
    return {
        'countermodels': countermodel_examples,
        'theorems': theorem_examples,
        'all': unit_tests
    }

__all__ = [
    'get_operators',
    'get_examples',
    'NegationOperator',
    'AndOperator', 
    'OrOperator',
    'ConditionalOperator',
    'BiconditionalOperator',
    'TopOperator',
    'BotOperator'
]