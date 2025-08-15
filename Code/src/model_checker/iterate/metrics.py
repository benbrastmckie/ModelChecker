"""Iteration termination control, statistics collection, and result formatting.

This module provides utilities for managing the iteration process, including
termination logic, statistics collection, and formatting of results.
Progress tracking has been moved to the output.progress module.
"""

import time
import logging
from typing import Optional, Dict, Any

logger = logging.getLogger(__name__)


class IterationStatistics:
    """Collect and analyze statistics about found models."""
    
    def __init__(self):
        self.model_stats = []
        self.completion_time = None
    
    def add_model(self, model_structure, differences: Dict[str, Any]):
        """Add statistics for a found model."""
        stats = {
            'world_count': len(getattr(model_structure, 'z3_world_states', [])),
            'possible_count': len(getattr(model_structure, 'z3_possible_states', [])),
            'difference_count': self._count_differences(differences),
            'timestamp': time.time(),
        }
        self.model_stats.append(stats)
    
    def _count_differences(self, differences: Dict[str, Any]) -> int:
        """Count total number of differences."""
        if not differences:
            return 0
        count = 0
        for category, changes in differences.items():
            if isinstance(changes, dict):
                if 'added' in changes:
                    count += len(changes['added'])
                if 'removed' in changes:
                    count += len(changes['removed'])
                # Count other changes
                for k, v in changes.items():
                    if k not in ['added', 'removed'] and isinstance(v, dict):
                        count += len(v)
        return count
    
    def get_summary(self) -> Dict[str, Any]:
        """Get summary statistics."""
        if not self.model_stats:
            return {}
        
        world_counts = [m['world_count'] for m in self.model_stats]
        diff_counts = [m['difference_count'] for m in self.model_stats[1:]]
        
        # Calculate average safely
        avg_worlds = sum(world_counts) / len(world_counts) if world_counts else 0
        avg_differences = sum(diff_counts) / len(diff_counts) if diff_counts else 0
        
        return {
            'total_models': len(self.model_stats),
            'avg_worlds': avg_worlds,
            'world_diversity': len(set(world_counts)),
            'avg_differences': avg_differences,
            'max_differences': max(diff_counts) if diff_counts else 0,
        }
    
    def set_completion_time(self, elapsed_time):
        """Set the total completion time for the iteration."""
        self.completion_time = elapsed_time
    
    def print_summary(self):
        """Print a summary of iteration statistics."""
        stats = self.get_summary()
        if not stats:
            return
        
        print("\n=== Iteration Statistics ===")
        print(f"Total models found: {stats['total_models']}")
        print(f"Average worlds per model: {stats['avg_worlds']:.1f}")
        print(f"World count diversity: {stats['world_diversity']} different counts")
        if stats['avg_differences'] > 0:
            print(f"Average differences between consecutive models: {stats['avg_differences']:.1f}")
            print(f"Maximum differences: {stats['max_differences']}")
        if self.completion_time is not None:
            print(f"Total completion time: {self.completion_time:.2f} seconds")


class TerminationManager:
    """Manages iteration termination conditions and logic."""
    
    def __init__(self, settings):
        """Initialize termination manager.
        
        Args:
            settings: Dictionary of iteration settings
        """
        self.settings = settings
        self.start_time = None
        self.timeout = settings.get('max_time', 300)  # Default 5 minutes
        self.max_consecutive_invalid = settings.get('max_consecutive_invalid', 20)
        
    def start_timing(self):
        """Start the iteration timer."""
        self.start_time = time.time()
        logger.debug(f"Iteration timing started with timeout: {self.timeout}s")
        
    def should_terminate(self, current_iteration, max_iterations, 
                        consecutive_invalid_count, checked_model_count):
        """Check if iteration should terminate.
        
        Args:
            current_iteration: Current iteration number
            max_iterations: Maximum iterations requested
            consecutive_invalid_count: Number of consecutive invalid models
            checked_model_count: Total models checked
            
        Returns:
            tuple: (should_terminate: bool, reason: str)
        """
        # Check if we've found enough models
        if current_iteration >= max_iterations:
            return True, f"Found all {max_iterations} requested models"
        
        # Skip global timeout check - we handle per-model timeouts separately
        # if self.start_time is not None:
        #     elapsed = time.time() - self.start_time
        #     if elapsed > self.timeout:
        #         return True, f"Timeout ({self.timeout}s) reached after {elapsed:.1f}s"
        
        # Check consecutive invalid models
        if consecutive_invalid_count >= self.max_consecutive_invalid:
            return True, f"Too many consecutive invalid models ({consecutive_invalid_count})"
        
        # Check for lack of progress
        if checked_model_count > 10 * max_iterations and current_iteration < max_iterations / 2:
            return True, "Insufficient progress - checked too many models with few results"
        
        return False, ""
    
    def get_elapsed_time(self):
        """Get elapsed time since start.
        
        Returns:
            float: Elapsed time in seconds
        """
        if self.start_time is None:
            return 0.0
        return time.time() - self.start_time
    
    def should_attempt_escape(self, consecutive_invalid_count):
        """Determine if we should attempt constraint escape.
        
        Args:
            consecutive_invalid_count: Number of consecutive invalid models
            
        Returns:
            bool: True if escape should be attempted
        """
        # Attempt escape after 3 consecutive failures
        return consecutive_invalid_count >= 3
    
    def get_progress_ratio(self, current, total):
        """Calculate progress ratio.
        
        Args:
            current: Current count
            total: Total target
            
        Returns:
            float: Progress ratio (0.0 to 1.0)
        """
        if total <= 0:
            return 0.0
        return min(1.0, current / total)


class ResultFormatter:
    """Formats iteration results for display."""
    
    def format_iteration_summary(self, model_structures, statistics, elapsed_time):
        """Format a summary of the iteration results.
        
        Args:
            model_structures: List of found model structures
            statistics: IterationStatistics instance
            elapsed_time: Total elapsed time
            
        Returns:
            str: Formatted summary
        """
        summary = []
        summary.append("\n" + "="*60)
        summary.append("ITERATION SUMMARY")
        summary.append("="*60)
        summary.append(f"Models found: {len(model_structures)}")
        summary.append(f"Total time: {elapsed_time:.2f} seconds")
        
        # Add statistics if available
        stats = statistics.get_summary()
        if stats:
            summary.append(f"Models checked: {stats.get('total_checked', 'N/A')}")
            if 'success_rate' in stats:
                summary.append(f"Success rate: {stats['success_rate']*100:.1f}%")
            if 'average_model_time' in stats:
                summary.append(f"Average time per model: {stats['average_model_time']:.3f}s")
        
        summary.append("="*60)
        return "\n".join(summary)
    
    def format_difference_report(self, differences):
        """Format differences between models.
        
        Args:
            differences: Dictionary of differences
            
        Returns:
            str: Formatted difference report
        """
        if not differences:
            return "\n=== DIFFERENCES FROM PREVIOUS MODEL ===\nNo significant differences detected."
        
        report = ["\n=== DIFFERENCES FROM PREVIOUS MODEL ==="]
        
        # Format world changes
        if 'world_changes' in differences:
            changes = differences['world_changes']
            if changes.get('added') or changes.get('removed'):
                report.append("\nWorld Changes:")
                for state in changes.get('added', []):
                    report.append(f"  + State {state} (now a world)")
                for state in changes.get('removed', []):
                    report.append(f"  - State {state} (no longer a world)")
        
        # Format possible state changes
        if 'possible_changes' in differences:
            changes = differences['possible_changes']
            if changes.get('added') or changes.get('removed'):
                report.append("\nPossible State Changes:")
                for state in changes.get('added', []):
                    report.append(f"  + State {state} (now possible)")
                for state in changes.get('removed', []):
                    report.append(f"  - State {state} (now impossible)")
        
        return "\n".join(report)
    
    def format_progress_update(self, current, total, checked, elapsed):
        """Format a progress update message.
        
        Args:
            current: Current model count
            total: Total models requested
            checked: Total models checked
            elapsed: Elapsed time
            
        Returns:
            str: Formatted progress message
        """
        percent = (current / total) * 100 if total > 0 else 0
        return f"Finding {total} models: [{self._create_progress_bar(current, total)}] {current}/{total} ({percent:.0f}%) - checked {checked} - {elapsed:.1f}s"
    
    def _create_progress_bar(self, current, total, width=20):
        """Create a text progress bar.
        
        Args:
            current: Current value
            total: Total value
            width: Bar width in characters
            
        Returns:
            str: Progress bar string
        """
        if total <= 0:
            return "░" * width
        
        filled = int(width * current / total)
        return "[" + "█" * filled + "░" * (width - filled) + "]"