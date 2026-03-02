"""Unit tests for NotebookFormatter integration."""

import unittest
import tempfile
import json
from pathlib import Path
from unittest.mock import MagicMock, patch

from model_checker.output.formatters.notebook import NotebookFormatter


class TestNotebookFormatter(unittest.TestCase):
    """Test NotebookFormatter integration with output system."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.formatter = NotebookFormatter()
        
        # Create mock module variables
        self.module_vars = {
            'semantic_theories': {
                'test_theory': {
                    'semantics': MagicMock(),
                    'proposition': MagicMock(),
                    'model_structure': MagicMock()
                }
            },
            'example_range': {
                'Example1': (['p'], 'p'),
                'Example2': (['p', 'q'], 'p ∧ q')
            }
        }
        
        # Create source path
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            self.source_path = f.name
            f.write("# Test examples file\n")
    
    def tearDown(self):
        """Clean up test fixtures."""
        Path(self.source_path).unlink(missing_ok=True)
    
    def test_formatter_initialization(self):
        """Test NotebookFormatter initializes correctly."""
        self.assertIsNotNone(self.formatter.generator)
        self.assertIsNone(self.formatter._module_vars)
        self.assertIsNone(self.formatter._source_path)
        self.assertEqual(self.formatter._collected_examples, [])
    
    def test_set_context(self):
        """Test setting module context."""
        self.formatter.set_context(self.module_vars, self.source_path)
        
        self.assertEqual(self.formatter._module_vars, self.module_vars)
        self.assertEqual(self.formatter._source_path, self.source_path)
    
    def test_format_example_collects_data(self):
        """Test that format_example collects data for batch processing."""
        example_data = {
            'example': 'Test',
            'theory': 'test_theory',
            'has_model': True,
            'premises': ['p'],
            'conclusions': ['q']
        }
        model_output = "Model found: ..."
        
        result = self.formatter.format_example(example_data, model_output)
        
        # Should return empty string for individual examples
        self.assertEqual(result, "")
        
        # Should have collected the example
        self.assertEqual(len(self.formatter._collected_examples), 1)
        self.assertEqual(self.formatter._collected_examples[0]['data'], example_data)
        self.assertEqual(self.formatter._collected_examples[0]['output'], model_output)
    
    def test_get_file_extension(self):
        """Test that formatter returns correct file extension."""
        self.assertEqual(self.formatter.get_file_extension(), 'ipynb')
    
    def test_format_batch_requires_context(self):
        """Test that format_batch raises error without context."""
        with self.assertRaises(ValueError) as context:
            self.formatter.format_batch([])
        
        self.assertIn("Context not set", str(context.exception))
    
    @patch('model_checker.output.formatters.notebook.StreamingNotebookGenerator')
    def test_format_batch_generates_notebook(self, mock_generator_class):
        """Test that format_batch generates notebook with context."""
        # Set up mock generator
        mock_generator = MagicMock()
        mock_generator_class.return_value = mock_generator
        
        # Create new formatter with mocked generator
        formatter = NotebookFormatter()
        formatter.set_context(self.module_vars, self.source_path)
        
        # Collect some examples
        formatter.format_example({'example': 'Test1'}, 'Output1')
        formatter.format_example({'example': 'Test2'}, 'Output2')
        
        # Generate batch output
        with patch('builtins.open', create=True) as mock_open:
            mock_open.return_value.__enter__.return_value.read.return_value = '{"cells": []}'
            
            result = formatter.format_batch([])
        
        # Should have called generate_notebook_stream
        mock_generator.generate_notebook_stream.assert_called_once()
        
        # Should return notebook content
        self.assertIn('"cells"', result)
        
        # Should reset collected examples
        self.assertEqual(formatter._collected_examples, [])
    
    def test_format_for_streaming(self):
        """Test direct streaming generation."""
        # Create mock generator
        mock_generator = MagicMock()
        self.formatter.generator = mock_generator
        
        self.formatter.set_context(self.module_vars, self.source_path)
        
        output_path = '/tmp/test_notebook.ipynb'
        self.formatter.format_for_streaming(output_path)
        
        # Should have called generate_notebook_stream with correct args
        mock_generator.generate_notebook_stream.assert_called_once_with(
            self.module_vars,
            self.source_path,
            output_path
        )
    
    def test_format_for_streaming_requires_context(self):
        """Test that format_for_streaming raises error without context."""
        with self.assertRaises(ValueError) as context:
            self.formatter.format_for_streaming('/tmp/test.ipynb')
        
        self.assertIn("Context not set", str(context.exception))


if __name__ == '__main__':
    unittest.main()