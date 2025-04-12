"""Tests for the progress tracking utilities."""

import time
import unittest
import io
from threading import Thread

from model_checker.builder.progress import Spinner

class TestSpinner(unittest.TestCase):
    """Test the Spinner class for progress tracking."""
    
    def test_spinner_initialization(self):
        """Test that spinner initializes with correct values."""
        spinner = Spinner(message="Testing")
        self.assertEqual(spinner.message, "Testing")
        self.assertEqual(spinner.current, 0)
        self.assertFalse(spinner._active)
        self.assertIsNone(spinner._thread)
        
    def test_spinner_start_stop(self):
        """Test that spinner starts and stops correctly."""
        spinner = Spinner()
        
        # Start spinner
        spinner.start()
        self.assertTrue(spinner._active)
        self.assertIsNotNone(spinner._thread)
        self.assertTrue(spinner._thread.is_alive())
        
        # Stop spinner
        spinner.stop()
        self.assertFalse(spinner._active)
        
        # Give the thread time to stop
        time.sleep(0.2)
        self.assertFalse(spinner._thread.is_alive())
        
    def test_spinner_output(self):
        """Test that spinner produces expected output."""
        output = io.StringIO()
        spinner = Spinner(message="Testing", stream=output)
        
        # Start spinner for a short time
        spinner.start()
        time.sleep(0.25)  # Should produce at least 2 updates
        spinner.stop()
        
        # Check output
        result = output.getvalue()
        self.assertTrue(result.startswith("\rTesting:"))
        self.assertGreater(len(result), len("\rTesting: -"))
        
if __name__ == "__main__":
    unittest.main()