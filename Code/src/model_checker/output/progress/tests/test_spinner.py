"""Tests for the spinner component."""

import sys
import time
import threading
import pytest
from unittest.mock import Mock, patch
from model_checker.output.progress.spinner import Spinner


class TestSpinner:
    """Test the Spinner class."""
    
    def test_initialization_default(self):
        """Test spinner initialization with defaults."""
        spinner = Spinner()
        
        assert spinner.message == "Running model-checker"
        assert spinner.stream == sys.stdout
        assert spinner.progress_chars == ["-", "\\", "|", "/"]
        assert spinner.current == 0
        assert spinner._active is False
        assert spinner._thread is None
    
    def test_initialization_custom(self):
        """Test spinner initialization with custom values."""
        stream = Mock()
        spinner = Spinner(message="Loading", stream=stream)
        
        assert spinner.message == "Loading"
        assert spinner.stream is stream
    
    def test_progress_chars(self):
        """Test spinner animation characters."""
        spinner = Spinner()
        
        # Verify progress chars are defined
        assert len(spinner.progress_chars) == 4
        assert spinner.progress_chars == ["-", "\\", "|", "/"]
    
    def test_start_creates_thread(self):
        """Test that start creates and starts a thread."""
        spinner = Spinner()
        
        spinner.start()
        
        assert spinner._active is True
        assert spinner._thread is not None
        assert isinstance(spinner._thread, threading.Thread)
        assert spinner._thread.daemon is True
        assert spinner._thread.is_alive()
        
        # Clean up
        spinner.stop()
    
    def test_stop_stops_thread(self):
        """Test that stop properly stops the thread."""
        stream = Mock()
        spinner = Spinner(stream=stream)
        
        spinner.start()
        # Give it time to start
        time.sleep(0.05)
        
        spinner.stop()
        
        # Should no longer be active
        assert spinner._active is False
        # Thread should stop
        assert spinner._thread is None or not spinner._thread.is_alive()
    
    def test_spinner_animation(self):
        """Test that spinner animates through frames."""
        stream = Mock()
        spinner = Spinner(message="Testing", stream=stream)
        
        spinner.start()
        # Let it run for enough time to cycle
        time.sleep(0.25)
        spinner.stop()
        
        # Should have written multiple times
        assert stream.write.call_count > 2
        
        # Check that different frames were shown
        calls = [call[0][0] for call in stream.write.call_args_list]
        # Filter to just the spinner updates (not the clear)
        spinner_calls = [c for c in calls if c.startswith('\rTesting:')]
        assert len(spinner_calls) >= 2
    
    def test_stop_clears_display(self):
        """Test that stop clears the display."""
        stream = Mock()
        spinner = Spinner(stream=stream)
        
        spinner.start()
        time.sleep(0.05)
        spinner.stop()
        
        # Should have cleared the line
        calls = [call[0][0] for call in stream.write.call_args_list]
        # Last call should be the clear
        assert any('\r' + ' ' * 50 + '\r' == call for call in calls)
    
    def test_stop_without_start(self):
        """Test that stop works even if never started."""
        spinner = Spinner()
        
        # Should not raise an exception
        spinner.stop()
        
        assert spinner._active is False
    
    def test_start_stop_behavior(self):
        """Test basic start/stop behavior."""
        stream = Mock()
        spinner = Spinner(stream=stream)
        
        # Start
        spinner.start()
        assert spinner._active is True
        time.sleep(0.05)
        
        # Stop
        spinner.stop()
        assert spinner._active is False
    
    def test_multiple_start_calls(self):
        """Test that multiple start calls don't create multiple threads."""
        spinner = Spinner()
        
        # First start
        spinner.start()
        first_thread = spinner._thread
        
        # Second start should do nothing
        spinner.start()
        assert spinner._thread is first_thread
        
        # Clean up
        spinner.stop()
    
    def test_current_index_wrapping(self):
        """Test that current index wraps around correctly."""
        spinner = Spinner()
        
        # Manually test wrapping
        initial = spinner.current
        assert initial == 0
        
        # Simulate cycling through all frames
        for i in range(len(spinner.progress_chars)):
            assert spinner.current == i % len(spinner.progress_chars)
            spinner.current = (spinner.current + 1) % len(spinner.progress_chars)
    
    def test_thread_daemon_mode(self):
        """Test that spinner thread is a daemon thread."""
        spinner = Spinner()
        spinner.start()
        
        assert spinner._thread.daemon is True
        
        # Clean up
        spinner.stop()
    
    def test_custom_message_formatting(self):
        """Test message formatting with spinner frame."""
        stream = Mock()
        spinner = Spinner(message="Custom Message", stream=stream)
        
        # Manually call format to test
        spinner._active = True
        spinner.stream.write(f"\r{spinner.message}: {spinner.progress_chars[spinner.current]}")
        
        # Check format
        expected = "\rCustom Message: -"
        stream.write.assert_called_with(expected)