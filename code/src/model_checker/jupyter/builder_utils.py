"""Builder utilities for Jupyter notebooks.

This module provides helper functions for creating and working with 
BuildExample instances in Jupyter notebooks.
"""

from typing import Dict, List, Any, Optional


def create_build_example(name: str, semantic_theory: Dict, example_case: List, 
                        theory_name: Optional[str] = None):
    """
    Create a BuildExample instance for use in Jupyter notebooks.
    
    This is a convenience function that creates a minimal BuildModule
    and then creates a BuildExample, making it easier to use in notebooks.
    
    Args:
        name: Name for the example
        semantic_theory: The semantic theory dictionary
        example_case: List containing [premises, conclusions, settings]
        theory_name: Optional name of the theory for context
        
    Returns:
        BuildExample instance ready for model checking
        
    Example:
        >>> from model_checker.theory_lib import logos
        >>> example = [['p'], ['p → q'], {'N': 2}]
        >>> model = create_build_example("test", logos.semantics, example)
    """
    from model_checker.builder.example import BuildExample
    
    # Create a minimal BuildModule mock
    class MinimalBuildModule:
        """Minimal BuildModule for notebook usage."""
        def __init__(self):
            self.module_name = name
            self.print_impossible = True  # Show impossible states for clarity
            self.print_constraints = False  
            self.print_z3 = False
            self.save_output = False
            self.maximize = False
            # Add general settings with defaults
            self.general_settings = {
                'print_impossible': True,
                'print_constraints': False,
                'print_z3': False,
                'save_output': False,
                'maximize': False,
            }
            # Update with user-provided settings if any
            if len(example_case) > 2 and example_case[2]:
                self.general_settings.update(example_case[2])
            # Add semantic_theories as single theory (not comparison)
            self.semantic_theories = {name: semantic_theory}
            # Add module_flags as a simple object with defaults
            self.module_flags = type('Flags', (), {
                'N': None,  # Will use settings from example_case
                'contingent': None,
                'non_contingent': None,
                'non_empty': None,
                'max_time': None,
                'print_constraints': False,
                'print_z3': False,
                'print_impossible': True
            })()
    
    build_module = MinimalBuildModule()
    
    # Create and return the BuildExample
    return BuildExample(build_module, semantic_theory, example_case, theory_name)


def build_and_check(name: str, semantic_theory: Dict, example_case: List,
                   theory_name: Optional[str] = None, verbose: bool = False):
    """
    Build and check a model in one step.
    
    This convenience function creates a BuildExample and immediately
    runs the model checking process.
    
    Args:
        name: Name for the example
        semantic_theory: The semantic theory dictionary
        example_case: List containing [premises, conclusions, settings]
        theory_name: Optional name of the theory for context
        verbose: Whether to print detailed output
        
    Returns:
        Tuple of (BuildExample instance, satisfiable bool)
        
    Example:
        >>> from model_checker.theory_lib import logos
        >>> example = [['p'], ['p → q'], {'N': 2}]
        >>> model, sat = build_and_check("test", logos.semantics, example)
        >>> print(f"Satisfiable: {sat}")
    """
    import sys
    
    # Create the BuildExample (model is already solved during creation)
    model = create_build_example(name, semantic_theory, example_case, theory_name)
    
    # Check if model was found (satisfiable)
    if hasattr(model, 'model_structure') and model.model_structure:
        sat = model.model_structure.satisfiable
        
        if verbose:
            if sat:
                print(f"✓ Model found for {name}")
                # Print the model interpretation
                model.model_structure.print_input_sentences(sys.stdout)
            else:
                print(f"✗ No model found for {name}")
                if hasattr(model.model_structure, 'unsat_core') and model.model_structure.unsat_core:
                    print("Unsat core:", model.model_structure.unsat_core)
        
        return model, sat
    
    return model, None