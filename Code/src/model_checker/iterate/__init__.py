"""Iteration module for finding multiple semantically distinct models.

This package provides a framework for systematically finding multiple
semantically distinct models for a logical example. It handles:
- Creating constraints to ensure model distinctness
- Checking model isomorphism
- Visualizing differences between models

The iteration framework uses a base class approach where each theory
implements its own model iterator by extending the BaseModelIterator
class from the core module.
"""

from model_checker.iterate.core import BaseModelIterator, iterate_example

__all__ = ['BaseModelIterator', 'iterate_example']