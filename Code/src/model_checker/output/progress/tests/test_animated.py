"""Tests for animated progress bars."""

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
        
    def update(self, message: str) -> None:
        self.messages.append(message)
        
    def complete(self) -> None:
        self.completed = True
        
    def clear(self) -> None:
        self.cleared = True
        self.messages.clear()


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
        time.sleep(0.3)  # Let it animate
        progress.complete(success=True)
        
        # Check that multiple updates occurred
        assert len(display.messages) > 2
        assert display.completed
        
        # Check final message
        assert "FOUND" in display.messages[-1]
        assert "Model 1/1" in display.messages[-1]
        
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
        assert "FOUND" in final_msg
        
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
        
        # Should show NOT FOUND
        final_msg = display.messages[-1]
        assert "NOT FOUND" in final_msg
        
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
        assert "Model 2/4" in final_msg
        assert "checked" in final_msg
        assert "skipped" in final_msg
        
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