"""Animated progress bars with time-based completion.

This module provides animated progress bar implementations that
update in real-time using background threads. The main implementation
is TimeBasedProgress, which fills over a specified timeout duration.
"""

import os
import time
import threading
from typing import Optional
from .core import ProgressBar
from .display import ProgressDisplay

# Color constants for progress bars
PROGRESS_COLOR = '\033[38;5;208m'  # Orange/amber (256-color)
PROGRESS_COLOR_FALLBACK = '\033[33m'  # Yellow (16-color fallback)
COLOR_RESET = '\033[0m'


class AnimatedProgressBar(ProgressBar):
    """Base class for animated progress bars.
    
    This class provides the threading infrastructure for animated
    progress bars. Subclasses should implement the _animate method
    to define their animation behavior.
    
    Attributes:
        display: Display handler for progress output
        active: Whether animation is currently running
        thread: Background thread for animation
    """
    
    def __init__(self, display: Optional[ProgressDisplay] = None):
        """Initialize animated progress bar.
        
        Args:
            display: Custom display handler (defaults to TerminalDisplay)
        """
        # Lazy import to avoid circular dependency
        if display is None:
            from .display import TerminalDisplay
            display = TerminalDisplay()
        self.display = display
        self.active = False
        self.thread = None
        
    def _animate(self):
        """Animation loop - to be implemented by subclasses.
        
        This method runs in a background thread and should contain
        the animation logic. It should check self.active periodically
        to know when to stop.
        """
        raise NotImplementedError("Subclasses must implement _animate()")


class TimeBasedProgress(AnimatedProgressBar):
    """Progress bar that fills over a specified timeout duration.
    
    This progress bar is designed for model search operations. It gradually
    fills from empty to full over the timeout period, providing visual
    feedback about how much time remains. If a model is found before the
    timeout, the bar completes immediately.
    
    The display format is:
    "Finding non-isomorphic models: [████████████████████] 2/4 (1 skipped) 1.1s"
    
    Attributes:
        timeout: Maximum time in seconds for the search
        model_number: Current model number being searched for
        total_models: Total number of models to find
        start_time: When the search started
        found: Whether a model was found
        checked_count: Number of models checked
        skipped_count: Number of isomorphic models skipped
    """
    
    def __init__(self, 
                 timeout: float,
                 model_number: int,
                 total_models: int,
                 display: Optional[ProgressDisplay] = None,
                 start_time: Optional[float] = None):
        """Initialize time-based progress bar.
        
        Args:
            timeout: Search timeout in seconds
            model_number: Current model number (1-based)
            total_models: Total models to find
            display: Custom display handler
            start_time: Optional start time for timing synchronization
        """
        super().__init__(display)
        self.timeout = timeout
        self.model_number = model_number
        self.total_models = total_models
        self.provided_start_time = start_time  # Store provided start time
        self.start_time = None
        self.found = False
        self.checked_count = 0
        self.skipped_count = 0
        self.use_color = self._supports_color()
        
    def start(self, total: int = 100, message: str = "") -> None:
        """Start the animated progress bar."""
        # Use provided start time or current time
        self.start_time = self.provided_start_time or time.time()
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
            
    def _supports_color(self) -> bool:
        """Check if terminal supports color output."""
        # Check common environment variables
        if os.environ.get('NO_COLOR'):
            return False
        
        # Check TERM environment variable
        term = os.environ.get('TERM', '').lower()
        if term in ['dumb', 'unknown', '']:
            return False
        
        # Check if output is to a terminal
        if not hasattr(self.display.stream, 'isatty'):
            return False
        
        if not self.display.stream.isatty():
            return False
        
        return True
    
    def _generate_bar(self, progress: float) -> str:
        """Generate progress bar string with proper width handling and color."""
        bar_width = 20  # Standard width for all progress bars
        filled = int(bar_width * progress)
        remaining = bar_width - filled
        
        if self.use_color:
            # Create colored progress bar
            filled_bar = f"{PROGRESS_COLOR}{'█' * filled}{COLOR_RESET}"
            empty_bar = '░' * remaining
            return f"[{filled_bar}{empty_bar}]"
        else:
            # Non-colored version
            return f"[{'█' * filled}{'░' * remaining}]"
    
    def _create_bar(self, progress: float, width: int = 20) -> str:
        """Create visual progress bar (legacy method, calls _generate_bar)."""
        return self._generate_bar(progress)
        
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
            # Fill bar completely with color if supported
            if self.use_color:
                bar = f"[{PROGRESS_COLOR}{'█' * 20}{COLOR_RESET}]"
            else:
                bar = "[" + "█" * 20 + "]"
            
            msg = f"Finding non-isomorphic models: {bar} {self.model_number}/{self.total_models}"
            if self.skipped_count > 0:
                msg += f" ({self.skipped_count} skipped)"
            msg += f" {elapsed:.1f}s"
            
            self.display.update(msg)
            self.display.complete()