"""Tests for progress display adapters."""

import os
import sys
import pytest
from unittest.mock import Mock, patch
from model_checker.output.progress.display import ProgressDisplay, TerminalDisplay, BatchDisplay


class TestProgressDisplay:
    """Test the base ProgressDisplay interface."""
    
    def test_abstract_methods(self):
        """Test that ProgressDisplay defines abstract interface."""
        # ProgressDisplay can be instantiated but methods raise NotImplementedError
        display = ProgressDisplay()
        
        with pytest.raises(NotImplementedError):
            display.update("test")
            
        with pytest.raises(NotImplementedError):
            display.complete()
            
        with pytest.raises(NotImplementedError):
            display.clear()
    
    def test_interface_methods(self):
        """Test that interface methods are defined."""
        # Create a concrete implementation
        class ConcreteDisplay(ProgressDisplay):
            def update(self, message): pass
            def complete(self): pass
            def clear(self): pass
        
        display = ConcreteDisplay()
        assert hasattr(display, 'update')
        assert hasattr(display, 'complete')
        assert hasattr(display, 'clear')


class TestTerminalDisplay:
    """Test terminal display adapter."""
    
    def test_initialization_with_stream(self):
        """Test initialization with custom stream."""
        stream = Mock()
        display = TerminalDisplay(stream)
        assert display.stream is stream
    
    def test_initialization_default_stream(self):
        """Test initialization with default stdout."""
        display = TerminalDisplay()
        assert display.stream is sys.stdout
    
    def test_enabled_always_true(self):
        """Test that display is always enabled (for testing)."""
        stream = Mock()
        display = TerminalDisplay(stream)
        assert display.enabled is True
    
    def test_stream_assignment(self):
        """Test that custom stream is properly assigned."""
        stream = Mock()
        display = TerminalDisplay(stream)
        assert display.stream is stream
    
    def test_last_length_tracking(self):
        """Test that last message length is tracked."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        assert display.last_length == 0
        display.update("Test message")
        assert display.last_length == len("Test message")
    
    def test_disabled_update_noop(self):
        """Test that disabled display doesn't write."""
        stream = Mock()
        display = TerminalDisplay(stream)
        display.enabled = False
        
        display.update("Test")
        stream.write.assert_not_called()
    
    def test_update_with_carriage_return(self):
        """Test update message handling."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        display.update("Progress: 50%")
        
        # Should write message with carriage return
        stream.write.assert_called_once_with('\rProgress: 50%')
        stream.flush.assert_called_once()
    
    def test_complete(self):
        """Test completion writes newline."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        display.complete()
        
        stream.write.assert_called_once_with('\n')
        stream.flush.assert_called_once()
    
    def test_clear(self):
        """Test clear writes carriage return and spaces."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        # First write something to establish length
        display.update("Test message")
        stream.reset_mock()
        
        display.clear()
        
        # Should clear with spaces matching last message length
        expected = '\r' + ' ' * len("Test message") + '\r'
        stream.write.assert_called_once_with(expected)
        stream.flush.assert_called()
    
    def test_clear_without_previous_message(self):
        """Test clear when no previous message."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        display.clear()
        
        # Should not write anything if last_length is 0
        stream.write.assert_not_called()
    
    def test_terminal_width_handling(self):
        """Test terminal width detection and message truncation."""
        stream = Mock()
        display = TerminalDisplay(stream)
        
        # Test with very long message
        with patch('os.get_terminal_size') as mock_size:
            mock_size.return_value.columns = 20
            display.update("This is a very long message that should be truncated")
            
            # Message should be truncated
            call_arg = stream.write.call_args[0][0]
            assert len(call_arg) <= 21  # \r + 20 chars max


class TestBatchDisplay:
    """Test batch mode display adapter."""
    
    def test_initialization(self):
        """Test batch display initialization."""
        display = BatchDisplay()
        assert hasattr(display, 'stream')
        assert display.stream is sys.stdout
        
        # With custom stream
        custom_stream = Mock()
        display2 = BatchDisplay(custom_stream)
        assert display2.stream is custom_stream
    
    def test_update_is_noop(self):
        """Test that update is a no-op in batch mode."""
        stream = Mock()
        display = BatchDisplay(stream)
        
        display.update("Message 1")
        display.update("Message 2")
        
        # Should not write anything
        stream.write.assert_not_called()
    
    def test_complete_is_noop(self):
        """Test that complete is a no-op."""
        stream = Mock()
        display = BatchDisplay(stream)
        
        display.complete()
        
        # Should not write anything
        stream.write.assert_not_called()
    
    def test_clear_is_noop(self):
        """Test that clear is a no-op in batch mode."""
        stream = Mock()
        display = BatchDisplay(stream)
        
        display.clear()
        
        # Should not write anything
        stream.write.assert_not_called()
    
    def test_all_methods_are_noops(self):
        """Test that all methods do nothing in batch mode."""
        stream = Mock()
        display = BatchDisplay(stream)
        
        # Call all methods
        display.update("test")
        display.complete()
        display.clear()
        
        # Nothing should be written
        stream.write.assert_not_called()
        stream.flush.assert_not_called()