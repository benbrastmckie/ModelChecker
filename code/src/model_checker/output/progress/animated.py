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

    State Machine
    -------------
    The progress bar has the following states and transitions:

        IDLE ──start()──> ANIMATING ──freeze_at_current()──> FROZEN ──complete()──> DONE
                              │                                          ▲
                              └──────────complete() (legacy)─────────────┘

    States:
        IDLE:      Initial state, bar not started (active=False, thread=None)
        ANIMATING: Animation thread running, updating display (active=True, _frozen=False)
        FROZEN:    Animation stopped, fill/elapsed captured (active=False, _frozen=True)
        DONE:      Final state displayed (complete() called with success=True)

    Timing Synchronization Contract
    -------------------------------
    The freeze-then-complete pattern ensures visual consistency between the
    progress bar fill fraction and the displayed elapsed time:

    1. When model is found: call freeze_at_current()
       - Captures both fill_fraction and _frozen_elapsed at the same moment
       - Stops animation thread without printing final state
       - Allows caller to print other output (headers, etc.)

    2. After printing headers: call complete(success=True)
       - Uses frozen values, NOT current time
       - Ensures displayed "Xs" matches the bar fill percentage

    Without this pattern (legacy behavior), complete() would calculate elapsed
    at display time while using fill_fraction from an earlier moment, causing
    a mismatch where the bar appears 30% full but shows "0.7s" (the complete() time).

    Class Constants:
        ANIMATION_INTERVAL_SEC: Time between animation frame updates (0.1s)
        THREAD_JOIN_TIMEOUT_SEC: Maximum time to wait for thread termination (0.5s)
        BAR_WIDTH: Width of the progress bar in characters (20)

    Attributes:
        timeout: Maximum time in seconds for the search
        model_number: Current model number being searched for
        total_models: Total number of models to find
        start_time: When the search started
        found: Whether a model was found
        checked_count: Number of models checked
        skipped_count: Number of isomorphic models skipped
        fill_fraction: Current fill level (0.0 to 1.0), captured at freeze time
        _frozen: Whether freeze_at_current() was called
        _frozen_elapsed: Elapsed time captured at freeze time
    """

    # Class constants for timing behavior
    ANIMATION_INTERVAL_SEC: float = 0.1  # Update animation every 100ms
    THREAD_JOIN_TIMEOUT_SEC: float = 0.5  # Max wait for thread termination
    BAR_WIDTH: int = 20  # Standard width for progress bar display

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
        self.fill_fraction = 1.0  # Default to full fill, updated by freeze_at_current()
        self._frozen = False  # True if freeze_at_current() was called
        self._frozen_elapsed = 0.0  # Elapsed time at freeze, used in complete()
        
    def start(self, total: int = 100, message: str = "") -> None:
        """Start the animated progress bar."""
        # Use provided start time or current time
        self.start_time = self.provided_start_time or time.time()
        self.active = True
        self.thread = threading.Thread(target=self._animate)
        self.thread.daemon = True
        self.thread.start()
        
    def _animate(self) -> None:
        """Animate the progress bar based on elapsed time."""
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
            time.sleep(self.ANIMATION_INTERVAL_SEC)
            
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
        """Generate progress bar string with proper width handling and color.

        Args:
            progress: Fill fraction from 0.0 (empty) to 1.0 (full)

        Returns:
            Formatted progress bar string like "[████████░░░░░░░░░░░░]"
        """
        filled = int(self.BAR_WIDTH * progress)
        remaining = self.BAR_WIDTH - filled

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

    def freeze_at_current(self) -> float:
        """Freeze the progress bar at its current fill level and elapsed time.

        This method captures both the current elapsed time and fill fraction,
        then stops the animation thread without printing the final bar state.
        Use this when a model is found and you want to preserve the actual
        fill level and elapsed time rather than showing values from complete() time.

        The frozen values are used by complete() to ensure the displayed elapsed
        time matches the fill fraction (both captured at the same moment).

        Returns:
            float: The frozen fill fraction (0.0 to 1.0)
        """
        # Mark as explicitly frozen
        self._frozen = True

        # Calculate and store both elapsed time and fill fraction
        if self.start_time is None:
            self._frozen_elapsed = 0.0
            self.fill_fraction = 0.0
        else:
            self._frozen_elapsed = time.time() - self.start_time
            self.fill_fraction = min(1.0, self._frozen_elapsed / self.timeout)

        # Stop the animation loop
        self.active = False

        # Wait for animation thread to finish with timeout
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=self.THREAD_JOIN_TIMEOUT_SEC)

        return self.fill_fraction

    def complete(self, success: bool = True) -> None:
        """Complete the progress bar.

        This method can be called after manually stopping the animation thread.
        It handles the case where active=False and thread is already joined.

        Uses the stored fill_fraction and _frozen_elapsed (set by freeze_at_current())
        to display the bar at its actual fill level and elapsed time when the model
        was found, rather than showing values calculated at complete() time.

        This ensures visual consistency: the fill fraction and elapsed time both
        reflect the moment when freeze_at_current() was called.
        """
        # Set flags first to stop animation
        self.found = success
        self.active = False

        # Wait for thread to finish (handles already-stopped case gracefully)
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=self.THREAD_JOIN_TIMEOUT_SEC)

        # Clear any partial line from animation
        self.display.clear()

        # Only show final state if model was found
        # For timeouts, we just clear the line and don't show anything
        if success:
            # Use frozen values if freeze_at_current() was called,
            # otherwise calculate fresh (legacy behavior)
            if self._frozen:
                # Use frozen fill fraction and elapsed time for consistent display
                bar = self._generate_bar(self.fill_fraction)
                elapsed = self._frozen_elapsed
            else:
                # Legacy behavior: fill to 100% when complete() called directly
                bar = self._generate_bar(1.0)
                if self.start_time is None:
                    elapsed = 0.0
                else:
                    elapsed = time.time() - self.start_time

            msg = f"Finding non-isomorphic models: {bar} {self.model_number}/{self.total_models}"
            if self.skipped_count > 0:
                msg += f" ({self.skipped_count} skipped)"
            msg += f" {elapsed:.1f}s"

            self.display.update(msg)
            self.display.complete()