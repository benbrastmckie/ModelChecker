"""Parallel utilities for model iteration."""

import concurrent.futures
from typing import List, Callable
import z3
import logging

logger = logging.getLogger(__name__)


def parallel_constraint_generation(
    constraint_funcs: List[Callable],
    max_workers: int = None
) -> List[z3.ExprRef]:
    """Generate constraints in parallel.
    
    Args:
        constraint_funcs: List of functions that return Z3 constraints
        max_workers: Maximum number of parallel workers
        
    Returns:
        List of generated constraints
    """
    constraints = []
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all constraint generation tasks
        futures = [executor.submit(func) for func in constraint_funcs]
        
        # Collect results
        for future in concurrent.futures.as_completed(futures):
            try:
                constraint = future.result()
                if constraint is not None:
                    constraints.append(constraint)
            except Exception as e:
                logger.warning(f"Constraint generation failed: {e}")
    
    return constraints