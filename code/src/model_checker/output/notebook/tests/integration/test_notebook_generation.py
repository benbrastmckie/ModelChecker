"""Integration tests for notebook generation workflow."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch
from model_checker.output.notebook.streaming_generator import StreamingNotebookGenerator


class TestNotebookGeneration(unittest.TestCase):
    """Test end-to-end notebook generation workflow."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.generator = StreamingNotebookGenerator()
        
        # Create mock module variables
        self.mock_module_vars = {
            'semantic_theories': {
                'logos': {
                    'semantics': MagicMock(),
                    'proposition': MagicMock(),
                    'model_structure': MagicMock()
                }
            }
        }
        
        # Create a temporary examples file
        self.temp_examples = tempfile.NamedTemporaryFile(
            mode='w', suffix='_examples.py', delete=False
        )
        self.temp_examples.write("""
examples = [
    ("Test Example 1", ["p", "q"], "p ∧ q"),
    ("Test Example 2", ["r"], "¬r")
]
""")
        self.temp_examples.close()
    
    def tearDown(self):
        """Clean up test fixtures."""
        Path(self.temp_examples.name).unlink(missing_ok=True)
    
    @patch('model_checker.output.notebook.streaming_generator.Path.exists')
    @patch('model_checker.notebook.streaming_generator.json.load')
    def test_generate_notebook_stream_creates_file(self, mock_json_load, mock_exists):
        """Test that generate_notebook_stream creates a notebook file."""
        # Mock template existence and loading
        mock_exists.return_value = True
        mock_json_load.return_value = {
            'setup_cells': [
                {
                    'cell_type': 'markdown',
                    'source': ['# Test Notebook']
                }
            ]
        }
        
        # Add examples to module vars
        module_vars_with_examples = dict(self.mock_module_vars)
        module_vars_with_examples['examples'] = [
            ("Test Example", ["p"], "p ∧ q")
        ]
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            output_path = f.name
        
        try:
            # Generate notebook
            self.generator.generate_notebook_stream(
                module_vars_with_examples,
                self.temp_examples.name,
                output_path
            )
            
            # Verify file was created
            self.assertTrue(Path(output_path).exists())
            
            # Verify it's valid JSON
            with open(output_path, 'r') as f:
                notebook_data = json.load(f)
            
            # Check basic structure
            self.assertIn('cells', notebook_data)
            self.assertIn('metadata', notebook_data)
            
        finally:
            Path(output_path).unlink(missing_ok=True)
    
    @patch('model_checker.output.notebook.streaming_generator.Path.exists')
    def test_generate_notebook_raises_on_missing_template(self, mock_exists):
        """Test that generation raises error when template is missing."""
        # Mock template not existing
        mock_exists.return_value = False
        
        # Add examples to module vars
        module_vars_with_examples = dict(self.mock_module_vars)
        module_vars_with_examples['example_range'] = {
            "Test": (["p"], "p")
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            output_path = f.name
        
        try:
            # Should raise FileNotFoundError
            with self.assertRaises(FileNotFoundError) as context:
                self.generator.generate_notebook_stream(
                    module_vars_with_examples,
                    self.temp_examples.name,
                    output_path
                )
            
            self.assertIn("No template found", str(context.exception))
            
        finally:
            Path(output_path).unlink(missing_ok=True)
    
    def test_generate_notebook_raises_on_no_theories(self):
        """Test that generation raises error when no theories provided."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            output_path = f.name
        
        try:
            # Empty module vars
            empty_vars = {'semantic_theories': {}}
            
            with self.assertRaises(ValueError) as context:
                self.generator.generate_notebook_stream(
                    empty_vars,
                    self.temp_examples.name,
                    output_path
                )
            
            self.assertIn("No semantic theories", str(context.exception))
            
        finally:
            Path(output_path).unlink(missing_ok=True)
    
    @patch('model_checker.output.notebook.streaming_generator.Path.exists')
    @patch('model_checker.notebook.streaming_generator.json.load')
    def test_template_placeholder_substitution(self, mock_json_load, mock_exists):
        """Test that template placeholders are properly substituted."""
        # Mock template with placeholders
        mock_exists.return_value = True
        mock_json_load.return_value = {
            'setup_cells': [
                {
                    'cell_type': 'markdown',
                    'source': ['# {{THEORY_NAME}} Examples\n', 'Date: {{DATE}}']
                }
            ]
        }
        
        # Add examples to module vars
        module_vars_with_examples = dict(self.mock_module_vars)
        module_vars_with_examples['example_range'] = {
            "Test": (["p"], "p")
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            output_path = f.name
        
        try:
            # Generate notebook
            self.generator.generate_notebook_stream(
                module_vars_with_examples,
                self.temp_examples.name,
                output_path
            )
            
            # Read generated notebook
            with open(output_path, 'r') as f:
                notebook_data = json.load(f)
            
            # Check that placeholders were replaced
            first_cell = notebook_data['cells'][0]
            self.assertNotIn('{{THEORY_NAME}}', ''.join(first_cell['source']))
            self.assertNotIn('{{DATE}}', ''.join(first_cell['source']))
            
            # Should contain actual theory name
            self.assertIn('Logos', ''.join(first_cell['source']))
            
        finally:
            Path(output_path).unlink(missing_ok=True)
    
    def test_template_loading_for_different_theories(self):
        """Test that different theories load different templates."""
        # Test with different theory configurations
        theories = [
            ('logos', 'LogosTemplate'),
            ('exclusion', 'ExclusionTemplate'),
            ('imposition', 'ImpositionTemplate')
        ]
        
        for theory_name, expected_template in theories:
            # Mock module vars for this theory
            module_vars = {
                'semantic_theories': {
                    theory_name: {
                        'semantics': MagicMock(),
                        'proposition': MagicMock()
                    }
                }
            }
            
            # Verify template loader gets correct template
            from model_checker.output.notebook.template_loader import TemplateLoader
            loader = TemplateLoader()
            template_class = loader.get_template_class(theory_name)
            self.assertEqual(template_class.__name__, expected_template)


if __name__ == '__main__':
    unittest.main()