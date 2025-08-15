"""Tests for animated progress bars."""

import os
import time
import pytest
from model_checker.output.progress.animated import TimeBasedProgress
from model_checker.output.progress.display import ProgressDisplay


class MockDisplay(ProgressDisplay):
    """Mock display for testing."""
    
    def __init__(self):
        self.messages = []
        self.completed = False
        self.cleared = False
        # Mock stream for color detection
        self.stream = self
        
    def update(self, message: str) -> None:
        self.messages.append(message)
        
    def complete(self) -> None:
        self.completed = True
        
    def clear(self) -> None:
        self.cleared = True
        # Don't clear messages in test mock so we can verify what was displayed
        
    def isatty(self) -> bool:
        """Mock isatty for testing."""
        return False  # Tests run in non-TTY environment


class TestTimeBasedProgress:
    """Test time-based progress animation."""
    
    def test_progress_animation(self):
        """Test that progress animates over time."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=0.5,  # 500ms timeout
            model_number=1,
            total_models=1,
            display=display
        )
        
        progress.start()
        # Give animation time to produce at least a few frames
        # Animation updates every 100ms, so 0.35s should give 3+ updates
        time.sleep(0.35)  
        progress.complete(success=True)
        
        # Check that multiple updates occurred during animation
        # We should have at least 3 animation frames plus the final message
        assert len(display.messages) >= 3
        assert display.completed
        
        # Check final message
        assert "Finding non-isomorphic models:" in display.messages[-1]
        assert "1/1" in display.messages[-1]
        
    def test_immediate_completion(self):
        """Test that finding a model immediately completes the bar."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=5.0,  # Long timeout
            model_number=2,
            total_models=3,
            display=display
        )
        
        progress.start()
        time.sleep(0.1)  # Very short time
        progress.complete(success=True)
        
        # Should show full bar despite short time
        final_msg = display.messages[-1]
        assert "[████████████████████]" in final_msg
        assert "2/3" in final_msg
        
    def test_timeout_completion(self):
        """Test progress bar when search times out."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=0.2,  # 200ms timeout
            model_number=1,
            total_models=2,
            display=display
        )
        
        progress.start()
        time.sleep(0.3)  # Exceed timeout
        progress.complete(success=False)
        
        # Should clear display on timeout (no final message)
        assert display.cleared
        # We had animation frames before clearing
        assert len(display.messages) > 0
        
    def test_count_tracking(self):
        """Test tracking of checked and skipped counts."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=1.0,
            model_number=2,
            total_models=4,
            display=display
        )
        
        progress.start()
        
        # Simulate some checks and skips
        progress.update_checked(10)
        progress.update_skipped(3)
        time.sleep(0.2)
        progress.update_checked(15)
        progress.update_skipped(5)
        
        progress.complete(success=True)
        
        # Final message should show counts for this search
        final_msg = display.messages[-1]
        assert "2/4" in final_msg
        assert "5 skipped" in final_msg  # Should show current search skipped count
        
    def test_progress_bar_visual(self):
        """Test visual progress bar creation."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=1.0,
            model_number=1,
            total_models=1,
            display=display
        )
        
        # Test bar creation
        assert progress._create_bar(0.0) == "[░░░░░░░░░░░░░░░░░░░░]"
        assert progress._create_bar(0.25) == "[█████░░░░░░░░░░░░░░░]"
        assert progress._create_bar(0.5) == "[██████████░░░░░░░░░░]"
        assert progress._create_bar(0.75) == "[███████████████░░░░░]"
        assert progress._create_bar(1.0) == "[████████████████████]"
        
    def test_thread_cleanup(self):
        """Test that animation thread is properly cleaned up."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=1.0,
            model_number=1,
            total_models=1,
            display=display
        )
        
        progress.start()
        assert progress.active
        assert progress.thread is not None
        assert progress.thread.is_alive()
        
        progress.complete(success=True)
        time.sleep(0.6)  # Give thread time to stop
        
        assert not progress.active
        assert not progress.thread.is_alive()
        
    def test_color_support_detection(self):
        """Test terminal color support detection."""
        # Test with non-TTY display (should not use color)
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=1.0,
            model_number=1, 
            total_models=1,
            display=display
        )
        assert not progress.use_color
        
        # Test with NO_COLOR environment variable
        old_no_color = os.environ.get('NO_COLOR')
        try:
            os.environ['NO_COLOR'] = '1'
            progress2 = TimeBasedProgress(
                timeout=1.0,
                model_number=1,
                total_models=1,
                display=display
            )
            assert not progress2.use_color
        finally:
            if old_no_color is None:
                os.environ.pop('NO_COLOR', None)
            else:
                os.environ['NO_COLOR'] = old_no_color
                
    def test_color_progress_bar(self):
        """Test colored vs non-colored progress bars."""
        display = MockDisplay()
        
        # Test non-colored bar (isatty returns False)
        progress = TimeBasedProgress(
            timeout=1.0,
            model_number=1,
            total_models=1,
            display=display
        )
        bar = progress._generate_bar(0.5)
        assert bar == "[██████████░░░░░░░░░░]"
        assert '\033[' not in bar  # No color codes
        
        # Test colored bar by mocking isatty
        display.isatty = lambda: True
        progress_color = TimeBasedProgress(
            timeout=1.0,
            model_number=1,
            total_models=1,
            display=display
        )
        progress_color.use_color = True  # Force color for test
        bar_color = progress_color._generate_bar(0.5)
        assert '\033[38;5;208m' in bar_color  # Orange color code
        assert '\033[0m' in bar_color  # Reset code
        
    def test_custom_start_time(self):
        """Test progress bar with custom start time for timing sync."""
        display = MockDisplay()
        custom_start = time.time() - 2.0  # 2 seconds ago
        
        progress = TimeBasedProgress(
            timeout=5.0,
            model_number=2,
            total_models=3,
            display=display,
            start_time=custom_start
        )
        
        # Start should use the provided time
        progress.start()
        assert progress.start_time == custom_start
        
        # Let it run briefly
        time.sleep(0.2)
        progress.complete(success=True)
        
        # Check that elapsed time accounts for custom start
        # Should show at least 2 seconds elapsed
        final_msg = display.messages[-1]
        assert "2." in final_msg or "3." in final_msg or "4." in final_msg  # 2.x, 3.x, or 4.x seconds