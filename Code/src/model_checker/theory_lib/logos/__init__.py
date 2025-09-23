"""
Logos Theory: Modular Implementation of Hyperintensional Truthmaker Semantics

This theory provides a modular approach to logical operators organized by domain:
- Extensional: Extensional operators (¬,∧,∨,→,↔,⊤,⊥)
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

__version__ = "1.0.0"
__model_checker_version__ = "0.9.20"  # ModelChecker version this was built with

from .semantic import LogosSemantics, LogosProposition, LogosModelStructure
from .operators import LogosOperatorRegistry
from .subtheories import list_subtheories, AVAILABLE_SUBTHEORIES
from .iterate import LogosModelIterator, iterate_example, iterate_example_generator

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

def get_examples():
    """Get logos theory example range.
    
    Returns:
        dict: Mapping of example names to example cases
    """
    from .examples import example_range
    return example_range


def get_test_examples():
    """Get logos theory test example range.
    
    Returns:
        dict: Mapping of test names to test cases
    """
    from .examples import unit_tests
    return unit_tests


def get_examples_by_subtheory(subtheory_name):
    """
    Get examples from a specific subtheory.
    
    Args:
        subtheory_name (str): Name of the subtheory ('extensional', 'modal', etc.)
        
    Returns:
        dict: Examples from the specified subtheory
        
    Raises:
        ValueError: If subtheory_name is not valid
    """
    from .examples import subtheory_examples
    
    if subtheory_name not in subtheory_examples:
        valid_names = list(subtheory_examples.keys())
        raise ValueError(f"Invalid subtheory '{subtheory_name}'. Valid options: {valid_names}")
    
    return subtheory_examples[subtheory_name]


def get_examples_by_type(example_type='all'):
    """
    Get examples filtered by type.
    
    Args:
        example_type (str): 'countermodel' (CM), 'theorem' (TH), or 'all'
        
    Returns:
        dict: Filtered examples
    """
    from .examples import unit_tests
    
    if example_type == 'all':
        return unit_tests
    elif example_type == 'countermodel':
        return {k: v for k, v in unit_tests.items() if '_CM_' in k}
    elif example_type == 'theorem':  
        return {k: v for k, v in unit_tests.items() if '_TH_' in k or '_DEF_' in k}
    else:
        raise ValueError("example_type must be 'countermodel', 'theorem', or 'all'")


def get_example_stats():
    """
    Get statistics about the example distribution across subtheories.
    
    Returns:
        dict: Statistics including counts per subtheory and total examples
    """
    from .examples import (
        extensional_examples, modal_examples, constitutive_examples,
        counterfactual_examples, relevance_examples, unit_tests
    )
    
    stats = {
        'extensional': len(extensional_examples),
        'modal': len(modal_examples),
        'constitutive': len(constitutive_examples),
        'counterfactual': len(counterfactual_examples),
        'relevance': len(relevance_examples),
        'basic': 0,
        'total': len(unit_tests)
    }
    return stats


def print_example_report():
    """
    Print a detailed report of all examples being run, organized by subtheory.
    Shows example names, their subtheory source, and file paths.
    """
    from .examples import example_range, unit_tests, example_metadata
    
    print("\n" + "=" * 80)
    print("LOGOS THEORY EXAMPLE REPORT")
    print("=" * 80)
    
    # Count active examples
    active_examples = len(example_range)
    total_available = len(unit_tests)
    
    print(f"\nActive Examples: {active_examples} of {total_available} available")
    
    # Group examples by subtheory
    by_subtheory = {}
    for example_name in example_range:
        if example_name in example_metadata:
            subtheory = example_metadata[example_name]['subtheory']
            if subtheory not in by_subtheory:
                by_subtheory[subtheory] = []
            by_subtheory[subtheory].append(example_name)
    
    # Print by subtheory
    if by_subtheory:
        print("\nExamples by Subtheory:")
        print("-" * 40)
        for subtheory in sorted(by_subtheory.keys()):
            examples = sorted(by_subtheory[subtheory])
            print(f"\n{subtheory.upper()} SUBTHEORY ({len(examples)} examples)")
            
            # Separate countermodels and theorems
            cms = [e for e in examples if '_CM_' in e]
            ths = [e for e in examples if '_TH_' in e]
            defs = [e for e in examples if '_DEF_' in e]
            
            if cms:
                print(f"  Countermodels: {', '.join(cms)}")
            if ths:
                print(f"  Theorems: {', '.join(ths)}")
            if defs:
                print(f"  Definitions: {', '.join(defs)}")
    
    # Print summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("-" * 40)
    
    total_cm = sum(1 for name in example_range if '_CM_' in name)
    total_th = sum(1 for name in example_range if '_TH_' in name)
    total_def = sum(1 for name in example_range if '_DEF_' in name)
    
    print(f"Total Examples: {active_examples}")
    print(f"  - Countermodels: {total_cm}")
    print(f"  - Theorems: {total_th}")
    if total_def > 0:
        print(f"  - Definitions: {total_def}")
    if by_subtheory:
        print(f"Subtheories Active: {len(by_subtheory)}")
    
    print("\n" + "-" * 80)
    print("Theory: Logos (Hyperintensional Bilateral Semantics)")
    print("Author: Benjamin Brast-McKie")
    print("Implementation: Benjamin Brast-McKie, Miguel Buitrago")
    print("-" * 80)
    
    print("\nThe examples above have been aggregated from the various subtheories that")
    print("comprise the Logos theory. Each subtheory's examples can also be run directly.")
    print()
    print("For more information, see:")
    print("  - Logos documentation: src/model_checker/theory_lib/logos/README.md")
    print("  - Subtheories documentation: src/model_checker/theory_lib/logos/subtheories/README.md")
    print("  - General usage guide: Docs/usage/README.md")
    print("=" * 80)


__all__ = [
    # Main API
    'get_theory',
    'get_examples',
    'get_test_examples',
    'list_subtheories',
    'get_examples_by_subtheory',
    'get_examples_by_type', 
    'get_example_stats',
    'print_example_report',
    
    # Core classes
    'LogosSemantics',
    'LogosProposition', 
    'LogosModelStructure',
    'LogosOperatorRegistry',
    
    # Iterator support
    'LogosModelIterator',
    'iterate_example',
    'iterate_example_generator',
    
    # Convenience aliases
    'Semantics',
    'Proposition',
    'ModelStructure', 
    'OperatorRegistry',
    
    # Constants
    'AVAILABLE_SUBTHEORIES'
]