"""Core progress tracking interface and base implementation."""

import time
from abc import ABC, abstractmethod
from typing import Optional, Dict, Any, List


class ProgressBar(ABC):
    """Abstract base class for progress bars."""
    
    @abstractmethod
    def start(self, total: int = 100, message: str = "") -> None:
        """Start progress tracking."""
        pass
    
    @abstractmethod
    def update(self, current: int, **kwargs) -> None:
        """Update progress."""
        pass
    
    @abstractmethod
    def complete(self, success: bool = True) -> None:
        """Complete progress tracking."""
        pass


class UnifiedProgress:
    """Unified progress tracking for all model checking operations.
    
    This class provides a consistent interface for progress tracking
    across initial model checking and iteration phases.
    """
    
    def __init__(self, 
                 total_models: int = 1,
                 iteration_timeout: Optional[float] = None,
                 display: Optional['ProgressDisplay'] = None):
        """Initialize unified progress tracker.
        
        Args:
            total_models: Total number of models to find
            iteration_timeout: Timeout per iteration in seconds
            display: Custom display handler (defaults to TerminalDisplay)
        """
        self.total_models = total_models
        self.iteration_timeout = iteration_timeout or 60.0
        
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
        
    def start_model_search(self, model_number: int) -> None:
        """Start searching for a specific model."""
        # Don't create a new progress bar if we already have one for this model
        if self.current_model == model_number and self.model_progress_bars and \
           hasattr(self.model_progress_bars[-1], 'model_number') and \
           self.model_progress_bars[-1].model_number == model_number:
            return  # Already searching for this model
            
        self.current_model = model_number
        self.current_search_start = time.time()
        self.current_search_skipped = 0  # Reset skipped count for new search
        
        # Only start overall timing on first model
        if self.start_time is None:
            self.start_time = time.time()
        
        # Stop any previous progress bar that might still be animating
        if self.model_progress_bars:
            last_bar = self.model_progress_bars[-1]
            if hasattr(last_bar, 'active') and last_bar.active:
                last_bar.complete(False)  # Force stop
        
        # Create animated progress bar for this model
        from .animated import TimeBasedProgress
        progress_bar = TimeBasedProgress(
            timeout=self.iteration_timeout,
            model_number=model_number,
            total_models=self.total_models,
            display=self.display
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
        # Just clear display - progress bars should already be completed
        # by the iterator when models are found or timeout occurs
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