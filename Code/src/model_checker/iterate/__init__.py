"""Iteration module for finding multiple semantically distinct models.

This package provides a framework for systematically finding multiple
semantically distinct models for a logical example. It handles:
- Creating constraints to ensure model distinctness
- Checking model isomorphism
- Visualizing differences between models

The iteration framework uses a base class approach where each theory
implements its own model iterator by extending the BaseModelIterator
class from the core module.

Usage:
    Each theory should provide its own iterate_example implementation in 
    its iterate.py module that specifies which iterator class to use.
    
    For example, the default theory provides:
    
    ```python
    # In theory_lib/default/iterate.py
    def iterate_example(example, max_iterations=None):
        # Create the theory-specific iterator
        iterator = DefaultModelIterator(example)
        
        # Set max iterations if provided
        if max_iterations is not None:
            iterator.max_iterations = max_iterations
        
        # Perform iteration
        return iterator.iterate()
    ```
    
    Users should import the iterate_example function from the specific theory
    module they are using, not from this package directly.
"""

from model_checker.iterate.core import BaseModelIterator

__all__ = ['BaseModelIterator']