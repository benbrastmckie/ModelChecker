"""Unit tests for NotebookWriter class."""

import json
import tempfile
import unittest
from pathlib import Path
from model_checker.output.notebook.notebook_writer import NotebookWriter


class TestNotebookWriter(unittest.TestCase):
    """Test the NotebookWriter class functionality."""
    
    def test_notebook_writer_creates_valid_json(self):
        """Test that NotebookWriter produces valid notebook JSON."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            temp_path = f.name
        
        try:
            # Use NotebookWriter to create a notebook
            with NotebookWriter(temp_path) as writer:
                # Add a markdown cell
                writer.write_cell({
                    'cell_type': 'markdown',
                    'source': ['# Test Notebook\n', 'This is a test.']
                })
                
                # Add a code cell
                writer.write_cell({
                    'cell_type': 'code',
                    'source': ['print("Hello, World!")']
                })
            
            # Verify the file was created and is valid JSON
            with open(temp_path, 'r') as f:
                notebook_data = json.load(f)
            
            # Check notebook structure
            self.assertIn('cells', notebook_data)
            self.assertIn('metadata', notebook_data)
            self.assertIn('nbformat', notebook_data)
            self.assertIn('nbformat_minor', notebook_data)
            
            # Check cells were added correctly
            self.assertEqual(len(notebook_data['cells']), 2)
            self.assertEqual(notebook_data['cells'][0]['cell_type'], 'markdown')
            self.assertEqual(notebook_data['cells'][1]['cell_type'], 'code')
            
            # Check content
            self.assertEqual(notebook_data['cells'][0]['source'], ['# Test Notebook\n', 'This is a test.'])
            self.assertEqual(notebook_data['cells'][1]['source'], ['print("Hello, World!")'])
            
        finally:
            # Clean up
            Path(temp_path).unlink(missing_ok=True)
    
    def test_notebook_writer_context_manager(self):
        """Test that NotebookWriter context manager properly opens/closes file."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            temp_path = f.name
        
        try:
            # Test that context manager works
            with NotebookWriter(temp_path) as writer:
                self.assertIsNotNone(writer)
                writer.write_cell({
                    'cell_type': 'markdown',
                    'source': ['# Test']
                })
            
            # Verify file exists and is not empty
            self.assertTrue(Path(temp_path).exists())
            self.assertGreater(Path(temp_path).stat().st_size, 0)
            
        finally:
            Path(temp_path).unlink(missing_ok=True)
    
    def test_notebook_writer_handles_empty_cells(self):
        """Test that NotebookWriter handles empty cells correctly."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            temp_path = f.name
        
        try:
            with NotebookWriter(temp_path) as writer:
                # Add empty cells
                writer.write_cell({
                    'cell_type': 'code',
                    'source': []
                })
                writer.write_cell({
                    'cell_type': 'markdown',
                    'source': []
                })
            
            # Verify cells were added with empty source
            with open(temp_path, 'r') as f:
                notebook_data = json.load(f)
            
            self.assertEqual(len(notebook_data['cells']), 2)
            self.assertEqual(notebook_data['cells'][0]['source'], [])
            self.assertEqual(notebook_data['cells'][1]['source'], [])
            
        finally:
            Path(temp_path).unlink(missing_ok=True)
    
    def test_notebook_writer_metadata_structure(self):
        """Test that NotebookWriter creates proper metadata structure."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.ipynb', delete=False) as f:
            temp_path = f.name
        
        try:
            with NotebookWriter(temp_path) as writer:
                writer.write_cell({
                    'cell_type': 'code',
                    'source': ['x = 1']
                })
            
            with open(temp_path, 'r') as f:
                notebook_data = json.load(f)
            
            # Check metadata structure
            self.assertIn('metadata', notebook_data)
            self.assertIn('kernelspec', notebook_data['metadata'])
            self.assertIn('language_info', notebook_data['metadata'])
            
            # Check kernel spec
            kernelspec = notebook_data['metadata']['kernelspec']
            self.assertEqual(kernelspec['display_name'], 'Python 3 (ipykernel)')
            self.assertEqual(kernelspec['language'], 'python')
            self.assertEqual(kernelspec['name'], 'python3')
            
            # Check language info
            lang_info = notebook_data['metadata']['language_info']
            self.assertEqual(lang_info['name'], 'python')
            
        finally:
            Path(temp_path).unlink(missing_ok=True)


if __name__ == '__main__':
    unittest.main()