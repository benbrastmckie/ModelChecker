"""Tests for the input provider abstraction."""

import unittest
from unittest.mock import Mock, patch

from model_checker.output.input_provider import (
    InputProvider, ConsoleInputProvider, MockInputProvider
)


class TestInputProvider(unittest.TestCase):
    """Test the input provider base class and interface."""
    
    def test_base_class_requires_implementation(self):
        """Test that InputProvider is abstract and requires implementation."""
        provider = InputProvider()
        
        with self.assertRaises(NotImplementedError):
            provider.get_input("prompt")
            
    def test_interface_contract(self):
        """Test that the interface defines the expected method."""
        provider = InputProvider()
        
        # Should have get_input method
        self.assertTrue(hasattr(provider, 'get_input'))
        
        # Method should accept prompt string
        import inspect
        sig = inspect.signature(provider.get_input)
        self.assertIn('prompt', sig.parameters)


class TestConsoleInputProvider(unittest.TestCase):
    """Test the console input provider implementation."""
    
    @patch('builtins.input')
    def test_get_input_calls_builtin_input(self, mock_input):
        """Test that ConsoleInputProvider uses builtin input()."""
        mock_input.return_value = "user response"
        
        provider = ConsoleInputProvider()
        result = provider.get_input("Enter value: ")
        
        mock_input.assert_called_once_with("Enter value: ")
        self.assertEqual(result, "user response")
        
    @patch('builtins.input')
    def test_get_input_preserves_prompt_exactly(self, mock_input):
        """Test that prompt is passed through unchanged."""
        mock_input.return_value = "test"
        
        provider = ConsoleInputProvider()
        provider.get_input("Save all examples (a) or run in sequence (s)? ")
        
        mock_input.assert_called_with("Save all examples (a) or run in sequence (s)? ")
        
    @patch('builtins.input')
    def test_handles_keyboard_interrupt(self, mock_input):
        """Test that KeyboardInterrupt is propagated."""
        mock_input.side_effect = KeyboardInterrupt()
        
        provider = ConsoleInputProvider()
        
        with self.assertRaises(KeyboardInterrupt):
            provider.get_input("prompt")


class TestMockInputProvider(unittest.TestCase):
    """Test the mock input provider for testing."""
    
    def test_returns_predefined_responses(self):
        """Test that MockInputProvider returns predefined responses."""
        responses = ["first", "second", "third"]
        provider = MockInputProvider(responses)
        
        self.assertEqual(provider.get_input("prompt1"), "first")
        self.assertEqual(provider.get_input("prompt2"), "second")
        self.assertEqual(provider.get_input("prompt3"), "third")
        
    def test_raises_when_responses_exhausted(self):
        """Test that provider raises when out of responses."""
        provider = MockInputProvider(["only one"])
        
        provider.get_input("first call")
        
        with self.assertRaises(IndexError) as ctx:
            provider.get_input("second call")
            
        self.assertIn("No more mock responses", str(ctx.exception))
        
    def test_tracks_prompts_received(self):
        """Test that mock provider tracks prompts for assertions."""
        provider = MockInputProvider(["yes", "no"])
        
        provider.get_input("Save file?")
        provider.get_input("Continue?")
        
        self.assertEqual(provider.prompts_received, ["Save file?", "Continue?"])
        
    def test_single_response_convenience(self):
        """Test that a single string can be provided."""
        provider = MockInputProvider("single response")
        
        self.assertEqual(provider.get_input("any prompt"), "single response")
        
    def test_reset_functionality(self):
        """Test that mock can be reset for reuse."""
        provider = MockInputProvider(["first", "second"])
        
        provider.get_input("prompt")
        self.assertEqual(provider.current_index, 1)
        
        provider.reset()
        self.assertEqual(provider.current_index, 0)
        self.assertEqual(provider.prompts_received, [])
        
        # Can use responses again
        self.assertEqual(provider.get_input("new prompt"), "first")


if __name__ == '__main__':
    unittest.main()