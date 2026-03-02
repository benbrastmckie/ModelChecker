"""Core progress tracking interface and base implementation.

This module provides the core progress tracking functionality for
the ModelChecker framework, including the base ProgressBar interface
and the UnifiedProgress tracker for model iteration.
"""

import time
from typing import Optional, Dict, Any, List


class ProgressBar:
    """Base class for progress bars.
    
    This class defines the interface that all progress bar implementations
    must follow. Subclasses should implement the three core methods:
    start, update, and complete.
    """
    
    def start(self, total: int = 100, message: str = "") -> None:
        """Start progress tracking.
        
        Args:
            total: Total number of items to process
            message: Optional message to display
        """
        raise NotImplementedError("Subclasses must implement start()")
    
    def update(self, current: int, **kwargs) -> None:
        """Update progress.
        
        Args:
            current: Current progress value
            **kwargs: Additional progress information
        """
        raise NotImplementedError("Subclasses must implement update()")
    
    def complete(self, success: bool = True) -> None:
        """Complete progress tracking.
        
        Args:
            success: Whether the operation completed successfully
        """
        raise NotImplementedError("Subclasses must implement complete()")


class UnifiedProgress:
    """Unified progress tracking for all model checking operations.
    
    This class provides a consistent interface for progress tracking
    across initial model checking and iteration phases.
    """
    
    def __init__(self, 
                 total_models: int = 1,
                 max_time: Optional[float] = None,
                 display: Optional['ProgressDisplay'] = None):
        """Initialize unified progress tracker.
        
        Args:
            total_models: Total number of models to find
            max_time: Timeout for all operations in seconds
            display: Custom display handler (defaults to TerminalDisplay)
        """
        self.total_models = total_models
        self.max_time = max_time or 60.0
        
        # Lazy import to avoid circular dependency
        if display is None:
            from .display import TerminalDisplay
            display = TerminalDisplay()
        self.display = display
        
        # State tracking
        self.current_model = 0
        self.models_found = 0
        self.models_checked = 0
        self.isomorphic_skipped = 0
        self.current_search_skipped = 0  # Track skipped for current search
        self.start_time = None
        self.current_search_start = None
        
        # Progress bars for each model
        self.model_progress_bars: List[ProgressBar] = []
        
    def start_model_search(self, model_number: int, start_time: Optional[float] = None) -> None:
        """Start searching for a specific model.
        
        Args:
            model_number: The model number being searched for
            start_time: Optional start time to sync with iterator timing
        """
        # Don't create a new progress bar if we already have one for this model
        if self.current_model == model_number and self.model_progress_bars and \
           hasattr(self.model_progress_bars[-1], 'model_number') and \
           self.model_progress_bars[-1].model_number == model_number:
            return  # Already searching for this model
            
        self.current_model = model_number
        # Use provided start time or fallback to current time
        self.current_search_start = start_time or time.time()
        self.current_search_skipped = 0  # Reset skipped count for new search
        
        # Only start overall timing on first model
        if self.start_time is None:
            self.start_time = time.time()
        
        # Stop any previous progress bar that might still be animating
        if self.model_progress_bars:
            last_bar = self.model_progress_bars[-1]
            if hasattr(last_bar, 'active') and last_bar.active:
                last_bar.complete(False)  # Force stop
        
        # Create animated progress bar for this model with synchronized time
        # Use max_time for all models
        timeout = self.max_time
        
        from .animated import TimeBasedProgress
        progress_bar = TimeBasedProgress(
            timeout=timeout,
            model_number=model_number,
            total_models=self.total_models,
            display=self.display,
            start_time=self.current_search_start  # Pass synchronized time
        )
        self.model_progress_bars.append(progress_bar)
        progress_bar.start()
        
    def model_checked(self) -> None:
        """Increment checked model counter."""
        self.models_checked += 1
        if self.model_progress_bars:
            # Update the current progress bar
            current_bar = self.model_progress_bars[-1]
            if hasattr(current_bar, 'update_checked'):
                current_bar.update_checked(self.models_checked)
            
    def model_skipped_isomorphic(self) -> None:
        """Increment isomorphic skip counter."""
        self.isomorphic_skipped += 1
        self.current_search_skipped += 1
        if self.model_progress_bars:
            # Update the current progress bar with current search count
            current_bar = self.model_progress_bars[-1]
            if hasattr(current_bar, 'update_skipped'):
                current_bar.update_skipped(self.current_search_skipped)
        
    def complete_model_search(self, found: bool) -> None:
        """Complete search for current model."""
        if found:
            self.models_found += 1
            
        if self.model_progress_bars:
            self.model_progress_bars[-1].complete(found)
            
    def finish(self) -> None:
        """Complete all progress tracking."""
        # Stop any active progress bars first
        for bar in self.model_progress_bars:
            if hasattr(bar, 'active') and bar.active:
                bar.complete(False)  # Stop without showing final state
        
        # Clear display
        self.display.clear()
        # Summary will be handled by iteration report
        
    def get_elapsed_time(self) -> float:
        """Get total elapsed time."""
        if self.start_time is None:
            return 0.0
        return time.time() - self.start_time
        
    def get_current_search_time(self) -> float:
        """Get elapsed time for current model search."""
        if self.current_search_start is None:
            return 0.0
        return time.time() - self.current_search_start