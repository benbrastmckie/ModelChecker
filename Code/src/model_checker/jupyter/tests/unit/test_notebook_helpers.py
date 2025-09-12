"""Unit tests for jupyter notebook_helpers module."""

import unittest
import sys
from io import StringIO
from unittest.mock import MagicMock, patch
from model_checker.jupyter.notebook_helpers import print_model, print_all


class TestPrintModel(unittest.TestCase):
    """Test print_model function."""
    
    def test_print_model_direct_output(self):
        """Test print_model outputs directly to stdout."""
        mock_model = MagicMock()
        mock_output = StringIO()
        
        # Mock the print_input_sentences method
        mock_model.print_input_sentences = MagicMock()
        
        with patch('sys.stdout', mock_output):
            result = print_model(mock_model, capture=False)
        
        # Should call print_input_sentences with sys.stdout
        mock_model.print_input_sentences.assert_called_once()
        self.assertIsNone(result)
    
    def test_print_model_capture_output(self):
        """Test print_model captures output as string."""
        mock_model = MagicMock()
        test_output = "Model: test\nValues: x=1, y=2"
        
        # Mock the print_input_sentences to write to the StringIO
        def mock_print(output):
            output.write(test_output)
        
        mock_model.print_input_sentences = MagicMock(side_effect=mock_print)
        
        result = print_model(mock_model, capture=True)
        
        self.assertEqual(result, test_output)
        mock_model.print_input_sentences.assert_called_once()
    
    def test_print_model_with_empty_output(self):
        """Test print_model with empty output."""
        mock_model = MagicMock()
        
        # Mock to write nothing
        mock_model.print_input_sentences = MagicMock()
        
        result = print_model(mock_model, capture=True)
        
        self.assertEqual(result, "")
    
    def test_print_model_capture_multiline(self):
        """Test print_model captures multiline output."""
        mock_model = MagicMock()
        test_output = "Line 1\nLine 2\nLine 3"
        
        def mock_print(output):
            output.write(test_output)
        
        mock_model.print_input_sentences = MagicMock(side_effect=mock_print)
        
        result = print_model(mock_model, capture=True)
        
        self.assertEqual(result, test_output)


class TestPrintAll(unittest.TestCase):
    """Test print_all function."""
    
    def test_print_all_direct_output(self):
        """Test print_all outputs directly to stdout."""
        mock_model = MagicMock()
        mock_output = StringIO()
        
        # Mock the print_all method
        mock_model.print_all = MagicMock()
        
        with patch('sys.stdout', mock_output):
            result = print_all(mock_model, capture=False)
        
        # Should call print_all with sys.stdout
        mock_model.print_all.assert_called_once()
        self.assertIsNone(result)
    
    def test_print_all_capture_output(self):
        """Test print_all captures output as string."""
        mock_model = MagicMock()
        test_output = "Input: p -> q\nConstraints: ...\nModel: ..."
        
        # Mock the print_all to write to the StringIO
        def mock_print(output):
            output.write(test_output)
        
        mock_model.print_all = MagicMock(side_effect=mock_print)
        
        result = print_all(mock_model, capture=True)
        
        self.assertEqual(result, test_output)
        mock_model.print_all.assert_called_once()
    
    def test_print_all_with_complex_model(self):
        """Test print_all with complex model structure."""
        mock_model = MagicMock()
        test_output = """
========================================
EXAMPLE TEST: there is a countermodel.

Atomic States: 3
Semantic Theory: Test

Premises:
1. A
2. B

Conclusions:
3. C

Model found!
========================================
"""
        
        def mock_print(output):
            output.write(test_output)
        
        mock_model.print_all = MagicMock(side_effect=mock_print)
        
        result = print_all(mock_model, capture=True)
        
        self.assertEqual(result, test_output)
    
    def test_print_all_handles_exception(self):
        """Test print_all handles exceptions gracefully."""
        mock_model = MagicMock()
        
        # Mock to raise an exception
        mock_model.print_all = MagicMock(side_effect=Exception("Test error"))
        
        # The function doesn't handle exceptions, it propagates them
        with self.assertRaises(Exception):
            print_all(mock_model, capture=True)


class TestIntegration(unittest.TestCase):
    """Test integration between print_model and print_all."""
    
    def test_both_functions_work_with_same_model(self):
        """Test both functions work with the same model object."""
        mock_model = MagicMock()
        
        # Set up different outputs for each method
        def mock_print_input(output):
            output.write("Input sentences output")
        
        def mock_print_all(output):
            output.write("All output")
        
        mock_model.print_input_sentences = MagicMock(side_effect=mock_print_input)
        mock_model.print_all = MagicMock(side_effect=mock_print_all)
        
        # Test print_model
        model_result = print_model(mock_model, capture=True)
        self.assertEqual(model_result, "Input sentences output")
        
        # Test print_all
        all_result = print_all(mock_model, capture=True)
        self.assertEqual(all_result, "All output")
    
    def test_capture_flag_consistency(self):
        """Test capture flag works consistently."""
        mock_model = MagicMock()
        
        # Test capture=False returns None for both
        self.assertIsNone(print_model(mock_model, capture=False))
        self.assertIsNone(print_all(mock_model, capture=False))
        
        # Test capture=True returns string for both
        mock_model.print_input_sentences = MagicMock(
            side_effect=lambda o: o.write("test")
        )
        mock_model.print_all = MagicMock(
            side_effect=lambda o: o.write("test")
        )
        
        self.assertIsInstance(print_model(mock_model, capture=True), str)
        self.assertIsInstance(print_all(mock_model, capture=True), str)


if __name__ == '__main__':
    unittest.main()