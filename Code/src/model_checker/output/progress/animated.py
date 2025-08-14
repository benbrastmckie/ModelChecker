"""Animated progress bars with time-based completion."""

import time
import threading
from typing import Optional
from .core import ProgressBar
from .display import ProgressDisplay


class AnimatedProgressBar(ProgressBar):
    """Base class for animated progress bars."""
    
    def __init__(self, display: Optional[ProgressDisplay] = None):
        # Lazy import to avoid circular dependency
        if display is None:
            from .display import TerminalDisplay
            display = TerminalDisplay()
        self.display = display
        self.active = False
        self.thread = None
        
    def _animate(self):
        """Animation loop - to be implemented by subclasses."""
        raise NotImplementedError


class TimeBasedProgress(AnimatedProgressBar):
    """Progress bar that fills over a specified timeout duration.
    
    The bar animates to fill completely over the timeout period,
    but completes immediately when a model is found.
    """
    
    def __init__(self, 
                 timeout: float,
                 model_number: int,
                 total_models: int,
                 display: Optional[ProgressDisplay] = None):
        super().__init__(display)
        self.timeout = timeout
        self.model_number = model_number
        self.total_models = total_models
        self.start_time = None
        self.found = False
        self.checked_count = 0
        self.skipped_count = 0
        
    def start(self, total: int = 100, message: str = "") -> None:
        """Start the animated progress bar."""
        self.start_time = time.time()
        self.active = True
        self.thread = threading.Thread(target=self._animate)
        self.thread.daemon = True
        self.thread.start()
        
    def _animate(self):
        """Animate the progress bar based on elapsed time."""
        update_interval = 0.1  # Update every 100ms
        
        while self.active and not self.found:
            # Check if we should stop
            if not self.active:
                break
                
            elapsed = time.time() - self.start_time
            progress = min(1.0, elapsed / self.timeout)
            
            # Create progress message
            bar = self._create_bar(progress)
            msg = f"Finding non-isomorphic models: {bar} {self.model_number}/{self.total_models}"
            # Show only skipped count for all models
            if self.skipped_count > 0:
                msg += f" ({self.skipped_count} skipped)"
            msg += f" {elapsed:.1f}s"
            
            self.display.update(msg)
            time.sleep(update_interval)
            
    def _create_bar(self, progress: float, width: int = 20) -> str:
        """Create visual progress bar."""
        filled = int(width * progress)
        return "[" + "█" * filled + "░" * (width - filled) + "]"
        
    def update(self, current: int, **kwargs) -> None:
        """Update progress (called when model is checked)."""
        # Updates handled by update_checked/update_skipped
        pass
        
    def update_checked(self, count: int) -> None:
        """Update checked model count."""
        self.checked_count = count
        
    def update_skipped(self, count: int) -> None:
        """Update skipped model count."""
        self.skipped_count = count
        
    def complete(self, success: bool = True) -> None:
        """Complete the progress bar."""
        # Set flags first to stop animation
        self.found = success
        self.active = False
        
        # Wait for thread to finish
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=0.5)
            
        # Clear any partial line from animation
        self.display.clear()
            
        # Show final state
        elapsed = time.time() - self.start_time
        
        # Only show final state if model was found
        # For timeouts, we just clear the line and don't show anything
        if success:
            # Fill bar completely
            bar = "[" + "█" * 20 + "]"
            msg = f"Finding non-isomorphic models: {bar} {self.model_number}/{self.total_models}"
            if self.skipped_count > 0:
                msg += f" ({self.skipped_count} skipped)"
            msg += f" {elapsed:.1f}s"
            
            self.display.update(msg)
            self.display.complete()