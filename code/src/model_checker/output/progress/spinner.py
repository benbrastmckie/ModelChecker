"""Simple animated spinner for long-running operations.

This module provides a lightweight spinner animation that can be used
for operations where progress cannot be measured (e.g., initial model
checking, theory comparisons).
"""

import sys
import time
import threading
from typing import Optional, IO


class Spinner:
    """Displays an animated progress spinner while a task runs.
    
    This is a simple spinner that shows rotating characters to indicate
    that work is in progress. Unlike progress bars, it doesn't show
    completion percentage, making it suitable for operations where
    progress cannot be measured.
    
    Example:
        >>> spinner = Spinner("Checking model")
        >>> spinner.start()
        >>> # Do long-running work
        >>> spinner.stop()
    
    Attributes:
        message: Text displayed before the spinner
        stream: Output stream for display
        progress_chars: Characters used for animation
        current: Current position in progress_chars
        _active: Whether spinner is currently running
        _thread: Background thread for animation
    """
    
    def __init__(self, message: str = "Running model-checker", stream: Optional[IO] = None):
        """Initialize progress spinner with custom message.
        
        Args:
            message: Text to display before the spinner
            stream: Output stream (defaults to stdout)
        """
        self.message = message
        self.stream = stream or sys.stdout
        self.progress_chars = ["-", "\\", "|", "/"]
        self.current = 0
        self._active = False
        self._thread = None
        
    def start(self) -> None:
        """Start the spinner animation in a separate thread.
        
        If the spinner is already running, this method does nothing.
        The spinner runs in a daemon thread to avoid blocking program exit.
        """
        if self._active:
            return
            
        self._active = True
        self._thread = threading.Thread(target=self._spin)
        self._thread.daemon = True
        self._thread.start()
        
    def stop(self) -> None:
        """Stop the spinner animation and clear the line.
        
        This method stops the animation thread and clears the spinner
        from the display. If the spinner is not running, this method
        does nothing.
        """
        if not self._active:
            return
            
        self._active = False
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=1.0)
            
        # Clear the spinner line
        self.stream.write("\r" + " " * 50 + "\r")
        self.stream.flush()
        
    def _spin(self) -> None:
        """Animated spinner loop, runs in a separate thread.
        
        This method continuously updates the spinner display until
        _active is set to False. It cycles through progress_chars
        to create the spinning animation.
        """
        while self._active:
            self.stream.write(f"\r{self.message}: {self.progress_chars[self.current]}")
            self.stream.flush()
            self.current = (self.current + 1) % len(self.progress_chars)
            time.sleep(0.1)