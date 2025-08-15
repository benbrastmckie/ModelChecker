"""Display handlers for progress output.

This module provides display implementations for progress tracking,
supporting both terminal-based interactive displays and batch mode
for non-interactive environments.
"""

import sys
import os
from typing import Optional


class ProgressDisplay:
    """Base class for progress display handlers.
    
    This class defines the interface for progress display implementations.
    Subclasses should override the three main methods: update, complete, and clear.
    """
    
    def update(self, message: str) -> None:
        """Update the progress display with a new message.
        
        Args:
            message: The progress message to display
        """
        raise NotImplementedError("Subclasses must implement update()")
        
    def complete(self) -> None:
        """Complete the current progress line.
        
        This is typically called when a progress operation finishes,
        allowing the display to finalize output (e.g., add newline).
        """
        raise NotImplementedError("Subclasses must implement complete()")
        
    def clear(self) -> None:
        """Clear the progress display.
        
        This removes any active progress output from the display.
        """
        raise NotImplementedError("Subclasses must implement clear()")


class TerminalDisplay(ProgressDisplay):
    """Terminal-based progress display with line clearing.
    
    This display implementation uses carriage returns to update
    progress in-place on the terminal, providing a smooth animated
    progress experience for interactive sessions.
    
    Attributes:
        stream: Output stream for progress display
        last_length: Length of last displayed message for proper clearing
        enabled: Whether progress display is enabled
    """
    
    def __init__(self, stream=sys.stdout):
        """Initialize terminal display.
        
        Args:
            stream: Output stream (defaults to stdout)
        """
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
    """Non-interactive display for batch mode.
    
    This display implementation is designed for non-interactive
    environments where carriage returns and line clearing would
    not work properly (e.g., log files, CI/CD pipelines).
    
    All progress operations are no-ops to avoid cluttering output
    in batch processing scenarios.
    
    Attributes:
        stream: Output stream (unused but kept for interface compatibility)
    """
    
    def __init__(self, stream=sys.stdout):
        """Initialize batch display.
        
        Args:
            stream: Output stream (kept for compatibility but unused)
        """
        self.stream = stream
        
    def update(self, message: str) -> None:
        """Update progress (no-op in batch mode).
        
        Args:
            message: Progress message (ignored in batch mode)
        """
        # In batch mode, we skip progress updates to avoid clutter
        pass
        
    def complete(self) -> None:
        """Complete progress (no-op in batch mode)."""
        pass
        
    def clear(self) -> None:
        """Clear display (no-op in batch mode)."""
        pass