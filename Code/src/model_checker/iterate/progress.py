"""Progress tracking for model iteration."""

import sys
import time
from typing import Optional


class IterationProgress:
    """Progress bar for model iteration."""
    
    def __init__(self, total: int, desc: str = "Finding models"):
        self.total = total
        self.current = 0
        self.desc = desc
        self.start_time = time.time()
        self.enabled = True  # Always show for testing  # sys.stdout.isatty()  # Only show in terminal
    
    def update(self, found: int, checked: int):
        """Update progress display."""
        if not self.enabled:
            return
        
        self.current = found
        elapsed = time.time() - self.start_time
        
        # Calculate progress
        progress = found / self.total
        bar_length = 30
        filled = int(bar_length * progress)
        bar = "█" * filled + "░" * (bar_length - filled)
        
        # Format message
        msg = f"\r{self.desc}: [{bar}] {found}/{self.total} "
        msg += f"(checked {checked}) {elapsed:.1f}s"
        
        # Write to stdout
        sys.stdout.write(msg)
        sys.stdout.flush()
    
    def finish(self, message: Optional[str] = None):
        """Complete the progress display."""
        if not self.enabled:
            return
        
        if message:
            sys.stdout.write(f"\r{message}\n")
        else:
            sys.stdout.write("\n")
        sys.stdout.flush()