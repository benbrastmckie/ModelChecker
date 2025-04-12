"""Progress tracking utilities for model checking operations.

This module provides tools for tracking progress of potentially long-running
operations like model checking and theory comparisons.
"""

import sys
import time
import threading


class Spinner:
    """Displays an animated progress spinner while a task runs."""
    
    def __init__(self, message="Running model-checker", stream=sys.stdout):
        """Initialize progress spinner with custom message.
        
        Args:
            message: Text to display before the spinner
            stream: Output stream (defaults to stdout)
        """
        self.message = message
        self.stream = stream
        self.progress_chars = ["-", "\\", "|", "/"]
        self.current = 0
        self._active = False
        self._thread = None
        
    def start(self):
        """Start the spinner animation in a separate thread."""
        if self._active:
            return
            
        self._active = True
        self._thread = threading.Thread(target=self._spin)
        self._thread.daemon = True
        self._thread.start()
        
    def stop(self):
        """Stop the spinner animation and clear the line."""
        if not self._active:
            return
            
        self._active = False
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=1.0)
            
        # Clear the spinner line
        self.stream.write("\r" + " " * 50 + "\r")
        self.stream.flush()
        
    def _spin(self):
        """Animated spinner loop, runs in a separate thread."""
        while self._active:
            self.stream.write(f"\r{self.message}: {self.progress_chars[self.current]}")
            self.stream.flush()
            self.current = (self.current + 1) % len(self.progress_chars)
            time.sleep(0.1)