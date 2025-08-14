"""Display handlers for progress output."""

import sys
import os
from abc import ABC, abstractmethod


class ProgressDisplay(ABC):
    """Abstract base class for progress display handlers."""
    
    @abstractmethod
    def update(self, message: str) -> None:
        """Update the progress display."""
        pass
        
    @abstractmethod
    def complete(self) -> None:
        """Complete the current progress line."""
        pass
        
    @abstractmethod
    def clear(self) -> None:
        """Clear the progress display."""
        pass


class TerminalDisplay(ProgressDisplay):
    """Terminal-based progress display with line clearing."""
    
    def __init__(self, stream=sys.stdout):
        self.stream = stream
        self.last_length = 0
        self.enabled = True  # Always enabled for testing
        # self.enabled = stream.isatty()  # Only show progress in terminal
        
    def update(self, message: str) -> None:
        """Update progress with carriage return and padding."""
        if not self.enabled:
            return
            
        # Get terminal width for proper padding
        try:
            terminal_width = os.get_terminal_size().columns
        except:
            terminal_width = 80
            
        # Ensure message fits
        if len(message) > terminal_width - 1:
            message = message[:terminal_width - 4] + "..."
            
        # Pad to clear previous content
        padded = message.ljust(self.last_length)
        self.last_length = len(message)
        
        # Write with carriage return
        self.stream.write(f"\r{padded}")
        self.stream.flush()
        
    def complete(self) -> None:
        """Move to next line after progress completes."""
        if not self.enabled:
            return
            
        self.stream.write("\n")
        self.stream.flush()
        self.last_length = 0
        
    def clear(self) -> None:
        """Clear the current line."""
        if not self.enabled:
            return
            
        if self.last_length > 0:
            self.stream.write("\r" + " " * self.last_length + "\r")
            self.stream.flush()
            self.last_length = 0


class BatchDisplay(ProgressDisplay):
    """Non-interactive display for batch mode (no carriage returns)."""
    
    def __init__(self, stream=sys.stdout):
        self.stream = stream
        
    def update(self, message: str) -> None:
        """Update progress (batch mode just prints)."""
        # In batch mode, we might want to skip progress entirely
        # or print periodic updates
        pass
        
    def complete(self) -> None:
        """Complete progress (no-op in batch mode)."""
        pass
        
    def clear(self) -> None:
        """Clear display (no-op in batch mode)."""
        pass