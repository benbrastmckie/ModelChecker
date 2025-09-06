"""Utility functions for ModelRunner.

This module contains helper functions and utilities used by ModelRunner
to keep the main runner module focused and under 500 lines.
"""

import time
import sys
from typing import Dict, Any, Tuple, Optional

from ..output.progress import UnifiedProgress


def format_model_output(model_structure, settings: Dict[str, Any], example_name: str) -> str:
    """Format model structure for display output.
    
    Args:
        model_structure: The model structure to format
        settings: Settings dictionary for formatting preferences
        example_name: Name of the example being formatted
        
    Returns:
        str: Formatted model output
    """
    output_lines = []
    
    # Add header if requested
    if settings.get('show_header', True):
        output_lines.append(f"\n{'='*60}")
        output_lines.append(f"Example: {example_name}")
        output_lines.append(f"{'='*60}\n")
    
    # Format model details
    if hasattr(model_structure, 'format_output'):
        output_lines.append(model_structure.format_output())
    else:
        output_lines.append(str(model_structure))
    
    return '\n'.join(output_lines)


def calculate_model_statistics(model_structure) -> Dict[str, Any]:
    """Calculate statistics for a model structure.
    
    Args:
        model_structure: The model to analyze
        
    Returns:
        dict: Statistics about the model
    """
    stats = {
        'domain_size': 0,
        'relation_count': 0,
        'valuation_count': 0,
        'constraint_count': 0,
        'solve_time': 0.0
    }
    
    # Extract domain size
    if hasattr(model_structure, 'domain'):
        stats['domain_size'] = len(model_structure.domain)
    
    # Extract relation information
    if hasattr(model_structure, 'accessibility'):
        stats['relation_count'] = len(model_structure.accessibility)
    
    # Extract valuation information
    if hasattr(model_structure, 'valuation'):
        stats['valuation_count'] = len(model_structure.valuation)
    
    # Extract constraint count
    if hasattr(model_structure, 'z3_model_assertions'):
        stats['constraint_count'] = model_structure.z3_model_assertions
    
    # Extract solve time
    if hasattr(model_structure, 'z3_model_runtime'):
        stats['solve_time'] = model_structure.z3_model_runtime
    
    return stats


def validate_runner_state(runner) -> None:
    """Validate runner is in correct state for operations.
    
    Args:
        runner: The ModelRunner instance to validate
        
    Raises:
        RuntimeError: If runner is in invalid state
    """
    if not hasattr(runner, 'build_module'):
        raise RuntimeError("Runner missing build_module reference")
    
    if not hasattr(runner.build_module, 'semantic_theories'):
        raise RuntimeError("Build module missing semantic_theories")
    
    if not hasattr(runner.build_module, 'example_range'):
        raise RuntimeError("Build module missing example_range")


def create_progress_tracker_for_iteration(
    example_case: list,
    iterate_count: int
) -> UnifiedProgress:
    """Create a unified progress tracker for model iterations.
    
    Args:
        example_case: Example case with settings
        iterate_count: Total models to find
        
    Returns:
        UnifiedProgress: Configured progress tracker instance
    """
    max_time = 60.0
    if len(example_case) > 2 and isinstance(example_case[2], dict):
        max_time = example_case[2].get('max_time', 60.0)
    
    return UnifiedProgress(
        total_models=iterate_count,
        max_time=max_time
    )


def store_timing_information(
    model_structure,
    start_time: float
) -> None:
    """Store timing information in the model structure for reporting.
    
    Args:
        model_structure: The model structure to update
        start_time: When model search started
    """
    model_structure._search_start_time = start_time
    model_structure._total_search_time = time.time() - start_time


def handle_iteration_error(
    error: Exception,
    example_name: str,
    theory_name: str
) -> None:
    """Handle and report iteration errors appropriately.
    
    Args:
        error: The exception that occurred
        example_name: Name of the example that failed
        theory_name: Name of the theory being used
    """
    print(f"\nError during iteration of {example_name} with {theory_name}:", 
          file=sys.stderr)
    print(f"  {type(error).__name__}: {str(error)}", file=sys.stderr)
    
    # Add debug information if available
    if hasattr(error, '__traceback__'):
        import traceback
        print("\nDebug traceback:", file=sys.stderr)
        traceback.print_tb(error.__traceback__, limit=3, file=sys.stderr)


def extract_iteration_settings(example_case: list) -> Dict[str, Any]:
    """Extract iteration-related settings from example case.
    
    Args:
        example_case: The example case containing settings
        
    Returns:
        dict: Iteration settings including count, max_time, etc.
    """
    settings = {
        'iterate': 1,
        'max_time': 60.0,
        'show_countdown': False,
        'show_progress': True
    }
    
    if len(example_case) > 2 and isinstance(example_case[2], dict):
        case_settings = example_case[2]
        settings['iterate'] = case_settings.get('iterate', 1)
        settings['max_time'] = case_settings.get('max_time', 60.0)
        settings['show_countdown'] = case_settings.get('show_countdown', False)
        settings['show_progress'] = case_settings.get('show_progress', True)
    
    return settings


def prepare_example_case_with_settings(
    example_case: list,
    semantic_theory: Dict[str, Any],
    module_flags
) -> list:
    """Prepare example case with translations and settings.
    
    Args:
        example_case: The example case to prepare
        semantic_theory: Theory configuration for translations
        module_flags: Module flags with overrides
        
    Returns:
        list: Modified example_case with applied translations and settings
    """
    # Check if we should show countdown
    show_countdown = getattr(module_flags, 'countdown', False)
    
    # Apply countdown setting if present
    if show_countdown and len(example_case) > 2 and isinstance(example_case[2], dict):
        example_case[2]['show_countdown'] = True
    
    return example_case


def calculate_model_differences(
    current_model,
    previous_model
) -> Dict[str, Any]:
    """Calculate differences between two model structures.
    
    Args:
        current_model: The current model structure
        previous_model: The previous model structure to compare against
        
    Returns:
        dict: Dictionary describing the differences
    """
    differences = {
        'domain_changes': [],
        'relation_changes': [],
        'valuation_changes': [],
        'summary': ''
    }
    
    # Compare domains
    if hasattr(current_model, 'domain') and hasattr(previous_model, 'domain'):
        current_domain = set(current_model.domain)
        previous_domain = set(previous_model.domain)
        
        added = current_domain - previous_domain
        removed = previous_domain - current_domain
        
        if added:
            differences['domain_changes'].append(f"Added: {added}")
        if removed:
            differences['domain_changes'].append(f"Removed: {removed}")
    
    # Compare relations
    if hasattr(current_model, 'accessibility') and hasattr(previous_model, 'accessibility'):
        current_relations = set(current_model.accessibility)
        previous_relations = set(previous_model.accessibility)
        
        added = current_relations - previous_relations
        removed = previous_relations - current_relations
        
        if added:
            differences['relation_changes'].append(f"Added: {added}")
        if removed:
            differences['relation_changes'].append(f"Removed: {removed}")
    
    # Create summary
    total_changes = (len(differences['domain_changes']) + 
                    len(differences['relation_changes']) + 
                    len(differences['valuation_changes']))
    
    if total_changes == 0:
        differences['summary'] = "Models are identical"
    else:
        differences['summary'] = f"Found {total_changes} differences"
    
    return differences


def format_comparison_results(
    results: list,
    example_name: str
) -> str:
    """Format comparison results for display.
    
    Args:
        results: List of (theory_name, max_N) tuples
        example_name: Name of the example
        
    Returns:
        str: Formatted comparison output
    """
    output_lines = []
    output_lines.append(f"\n{'='*60}")
    output_lines.append(f"Comparison Results for {example_name}")
    output_lines.append(f"{'='*60}")
    
    # Sort by max_N descending
    sorted_results = sorted(results, key=lambda x: x[1], reverse=True)
    
    for theory_name, max_n in sorted_results:
        output_lines.append(f"  {theory_name:20s}: Maximum N = {max_n}")
    
    output_lines.append("")
    return '\n'.join(output_lines)


def validate_iteration_count(iterate_count: int) -> None:
    """Validate iteration count is within acceptable range.
    
    Args:
        iterate_count: Number of iterations requested
        
    Raises:
        ValueError: If iteration count is invalid
    """
    if iterate_count < 1:
        raise ValueError(f"Iteration count must be positive, got {iterate_count}")
    
    if iterate_count > 1000:
        raise ValueError(f"Iteration count too large: {iterate_count} > 1000")


def should_show_progress(
    iterate_count: int,
    module_flags
) -> bool:
    """Determine if progress tracking should be shown.
    
    Args:
        iterate_count: Number of iterations
        module_flags: Module flags with preferences
        
    Returns:
        bool: True if progress should be shown
    """
    # Don't show progress for single iteration
    if iterate_count == 1:
        return False
    
    # Check if explicitly disabled
    if hasattr(module_flags, 'no_progress') and module_flags.no_progress:
        return False
    
    # Show progress for multiple iterations
    return True