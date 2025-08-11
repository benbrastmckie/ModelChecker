"""Iteration termination logic and conditions.

This module handles determining when iteration should terminate,
including timeout handling, resource management, and success conditions.
"""

import time
import logging

logger = logging.getLogger(__name__)


class TerminationManager:
    """Manages iteration termination conditions and logic."""
    
    def __init__(self, settings):
        """Initialize termination manager.
        
        Args:
            settings: Dictionary of iteration settings
        """
        self.settings = settings
        self.start_time = None
        self.timeout = settings.get('timeout', 300)  # Default 5 minutes
        self.max_consecutive_invalid = settings.get('max_consecutive_invalid', 20)
        
    def start_timing(self):
        """Start the iteration timer."""
        self.start_time = time.time()
        logger.debug(f"Iteration timing started with timeout: {self.timeout}s")
    
    def should_terminate(self, current_iteration, max_iterations, consecutive_invalid_count, 
                        checked_model_count):
        """Check if iteration should terminate.
        
        Args:
            current_iteration: Current iteration number
            max_iterations: Maximum iterations requested
            consecutive_invalid_count: Count of consecutive invalid models
            checked_model_count: Total number of models checked
            
        Returns:
            tuple: (should_terminate: bool, reason: str)
        """
        # Check if we've found enough models
        if current_iteration >= max_iterations:
            return True, f"Found all {max_iterations} requested models"
        
        # Check timeout
        if self._is_timeout_exceeded():
            elapsed = self.get_elapsed_time()
            return True, f"Timeout ({self.timeout}s) exceeded after {elapsed:.1f}s"
        
        # Check consecutive invalid model limit
        if consecutive_invalid_count >= self.max_consecutive_invalid:
            return True, f"Too many consecutive invalid models ({consecutive_invalid_count})"
        
        # Check for reasonable progress
        if self._should_terminate_due_to_lack_of_progress(current_iteration, checked_model_count):
            return True, "Insufficient progress - likely no more distinct models exist"
        
        return False, ""
    
    def _is_timeout_exceeded(self):
        """Check if the timeout has been exceeded.
        
        Returns:
            bool: True if timeout exceeded
        """
        if self.start_time is None:
            return False
            
        elapsed = time.time() - self.start_time
        return elapsed > self.timeout
    
    def get_elapsed_time(self):
        """Get elapsed time since iteration started.
        
        Returns:
            float: Elapsed time in seconds
        """
        if self.start_time is None:
            return 0.0
        return time.time() - self.start_time
    
    def _should_terminate_due_to_lack_of_progress(self, current_iteration, checked_model_count):
        """Check if we should terminate due to lack of progress.
        
        This implements a heuristic to avoid infinite loops when no more
        distinct models exist but the solver keeps finding isomorphic ones.
        
        Args:
            current_iteration: Current iteration number
            checked_model_count: Total number of models checked
            
        Returns:
            bool: True if we should terminate due to lack of progress
        """
        # If we've checked significantly more models than found, 
        # we're likely hitting only isomorphic models
        if current_iteration == 1:
            return False  # Don't apply this check for the first iteration
        
        # Calculate ratio of found models to checked models
        found_models = current_iteration
        ratio = found_models / checked_model_count if checked_model_count > 0 else 1.0
        
        # If we've checked a lot of models but found very few distinct ones,
        # and we've been running for a reasonable time, consider terminating
        min_checks_threshold = 50
        min_time_threshold = 30  # seconds
        ratio_threshold = 0.1  # 10% success rate
        
        if (checked_model_count > min_checks_threshold and 
            ratio < ratio_threshold and 
            self.get_elapsed_time() > min_time_threshold):
            
            logger.info(f"Low progress detected: {found_models}/{checked_model_count} "
                       f"models found ({ratio:.1%} success rate)")
            return True
        
        return False
    
    def get_termination_summary(self, current_iteration, max_iterations, 
                               checked_model_count, reason=""):
        """Get a summary of the termination conditions.
        
        Args:
            current_iteration: Final iteration number
            max_iterations: Maximum iterations requested
            checked_model_count: Total models checked
            reason: Termination reason
            
        Returns:
            dict: Termination summary
        """
        elapsed = self.get_elapsed_time()
        found_models = current_iteration
        
        return {
            'found_models': found_models,
            'requested_models': max_iterations,
            'checked_models': checked_model_count,
            'elapsed_time': elapsed,
            'termination_reason': reason,
            'success_rate': found_models / checked_model_count if checked_model_count > 0 else 0,
            'models_per_second': found_models / elapsed if elapsed > 0 else 0,
            'timeout_used': self.timeout,
            'timeout_exceeded': self._is_timeout_exceeded()
        }
    
    def estimate_remaining_time(self, current_iteration, max_iterations):
        """Estimate remaining time based on current progress.
        
        Args:
            current_iteration: Current iteration number
            max_iterations: Maximum iterations requested
            
        Returns:
            float or None: Estimated remaining time in seconds, or None if unable to estimate
        """
        if current_iteration <= 1 or self.start_time is None:
            return None
        
        elapsed = self.get_elapsed_time()
        if elapsed <= 0:
            return None
        
        # Calculate average time per model found
        models_found = current_iteration
        time_per_model = elapsed / models_found
        
        # Estimate time for remaining models
        remaining_models = max_iterations - current_iteration
        estimated_remaining = remaining_models * time_per_model
        
        # Don't estimate beyond the timeout
        time_until_timeout = max(0, self.timeout - elapsed)
        
        return min(estimated_remaining, time_until_timeout)
    
    def should_show_progress_update(self, last_update_time, update_interval=1.0):
        """Check if a progress update should be shown.
        
        Args:
            last_update_time: Time of last progress update
            update_interval: Minimum interval between updates in seconds
            
        Returns:
            bool: True if progress should be updated
        """
        current_time = time.time()
        return (current_time - last_update_time) >= update_interval
    
    def format_time_remaining(self, remaining_seconds):
        """Format remaining time in a human-readable way.
        
        Args:
            remaining_seconds: Seconds remaining
            
        Returns:
            str: Formatted time string
        """
        if remaining_seconds is None:
            return "unknown"
        
        if remaining_seconds < 60:
            return f"{remaining_seconds:.0f}s"
        elif remaining_seconds < 3600:
            minutes = remaining_seconds / 60
            return f"{minutes:.1f}m"
        else:
            hours = remaining_seconds / 3600
            return f"{hours:.1f}h"