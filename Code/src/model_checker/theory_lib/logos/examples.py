"""
Example configurations for the logos theory.

This module provides test cases and examples demonstrating the capabilities
of the modular logos theory across all subtheories.
"""

# Basic test examples for logos theory validation
test_example_range = {
    # Extensional logic examples
    "EXTENSIONAL_MODUS_PONENS": [
        ["p", "p \\rightarrow q"],  # premises
        ["q"],                      # conclusions
        {"N": 4}                   # settings
    ],
    
    "EXTENSIONAL_CONJUNCTION_INTRO": [
        ["p", "q"],
        ["p \\wedge q"],
        {"N": 4}
    ],
    
    "EXTENSIONAL_CONJUNCTION_ELIM": [
        ["p \\wedge q"],
        ["p"],
        {"N": 4}
    ],
    
    "EXTENSIONAL_DISJUNCTION_INTRO": [
        ["p"],
        ["p \\vee q"],
        {"N": 4}
    ],
    
    "EXTENSIONAL_NEGATION_CONSISTENCY": [
        ["p", "\\neg p"],
        ["\\bot"],
        {"N": 4}
    ],
    
    # Modal logic examples
    "MODAL_NECESSITY_IMPLICATION": [
        ["\\Box p"],
        ["p"],
        {"N": 4}
    ],
    
    "MODAL_NECESSITY_DISTRIBUTION": [
        ["\\Box (p \\rightarrow q)", "\\Box p"],
        ["\\Box q"],
        {"N": 4}
    ],
    
    "MODAL_POSSIBILITY_CONSISTENCY": [
        ["\\Diamond p"],
        ["\\neg \\Box \\neg p"],
        {"N": 4}
    ],
    
    # Constitutive logic examples
    "CONSTITUTIVE_IDENTITY_REFLEXIVE": [
        [],
        ["p \\equiv p"],
        {"N": 4}
    ],
    
    "CONSTITUTIVE_GROUND_TRANSITIVITY": [
        ["p \\leq q", "q \\leq r"],
        ["p \\leq r"],
        {"N": 4}
    ],
    
    "CONSTITUTIVE_ESSENCE_PROPERTY": [
        ["p \\sqsubseteq q", "q"],
        ["p"],
        {"N": 4}
    ],
    
    # Mixed operator examples
    "MIXED_MODAL_CONJUNCTION": [
        ["\\Box p", "\\Box q"],
        ["\\Box (p \\wedge q)"],
        {"N": 4}
    ],
    
    "MIXED_CONSTITUTIVE_MODAL": [
        ["\\Box (p \\equiv q)", "\\Box p"],
        ["\\Box q"],
        {"N": 4}
    ],
    
    # Simple validity tests (should be valid)
    "SIMPLE_TAUTOLOGY": [
        [],
        ["\\top"],
        {"N": 4}
    ],
    
    "SIMPLE_LAW_EXCLUDED_MIDDLE": [
        [],
        ["p \\vee \\neg p"],
        {"N": 4}
    ],
}

# Full example range for comprehensive testing
example_range = test_example_range.copy()

# Add more complex examples for demonstration
example_range.update({
    "COMPLEX_MODAL_NECESSITY": [
        ["\\Box (p \\rightarrow q)", "\\Diamond p"],
        ["\\Diamond q"],
        {"N": 8, "max_time": 15000}
    ],
    
    "COMPLEX_CONSTITUTIVE_CHAIN": [
        ["p \\leq q", "q \\sqsubseteq r", "r \\preceq s"],
        ["p \\preceq s"],
        {"N": 8, "max_time": 15000}
    ],
    
    "COMPLEX_MIXED_LOGIC": [
        ["\\Box (p \\equiv q)", "(p \\wedge r) \\vee (q \\wedge s)"],
        ["(\\Box p \\wedge r) \\vee (\\Box q \\wedge s)"],
        {"N": 8, "max_time": 20000}
    ],
})

# Semantic theory variants (for compatibility with existing framework)
semantic_theories = {
    'bilateral': {
        'description': 'Standard bilateral truthmaker semantics with modular operators',
        'settings': {'bilateral': True}
    },
    'modular': {
        'description': 'Modular subtheory-based semantics',
        'settings': {'modular': True}
    }
}