"""Unit tests for output helper functions."""

import unittest
import os
import json
import tempfile
import shutil
from unittest.mock import Mock, patch, MagicMock, mock_open
from datetime import datetime
from model_checker.output.helpers import (
    create_timestamped_directory, save_file, save_json,
    combine_markdown_sections, extract_model_data,
    ensure_directory_exists, get_file_extension
)
from model_checker.output.errors import OutputIOError, OutputDirectoryError
from model_checker.output.constants import OUTPUT_DIR_PREFIX, OUTPUT_DIR_TIMESTAMP_FORMAT


class TestCreateTimestampedDirectory(unittest.TestCase):
    """Test create_timestamped_directory function."""
    
    def setUp(self):
        """Set up test directory."""
        self.test_dir = tempfile.mkdtemp()
    
    def tearDown(self):
        """Clean up test directory."""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    @patch('model_checker.output.helpers.datetime')
    def test_create_with_defaults(self, mock_datetime):
        """Test creating directory with default parameters."""
        mock_datetime.now.return_value.strftime.return_value = "20250110_120000"
        
        result = create_timestamped_directory(self.test_dir)
        
        expected_dir = os.path.join(self.test_dir, f"{OUTPUT_DIR_PREFIX}20250110_120000")
        self.assertEqual(result, expected_dir)
        self.assertTrue(os.path.exists(expected_dir))
    
    @patch('model_checker.output.helpers.datetime')
    def test_create_with_custom_prefix(self, mock_datetime):
        """Test creating directory with custom prefix."""
        mock_datetime.now.return_value.strftime.return_value = "20250110_120000"
        
        result = create_timestamped_directory(self.test_dir, prefix="custom_")
        
        expected_dir = os.path.join(self.test_dir, "custom_20250110_120000")
        self.assertEqual(result, expected_dir)
        self.assertTrue(os.path.exists(expected_dir))
    
    @patch('model_checker.output.helpers.os.makedirs')
    def test_create_raises_on_os_error(self, mock_makedirs):
        """Test that OSError is converted to OutputDirectoryError."""
        mock_makedirs.side_effect = OSError("Permission denied")
        
        with self.assertRaises(OutputDirectoryError) as context:
            create_timestamped_directory(self.test_dir)
        
        self.assertIn("Permission denied", str(context.exception))
    
    @patch('model_checker.output.helpers.datetime')
    def test_create_handles_existing_directory(self, mock_datetime):
        """Test that existing directory is handled gracefully."""
        mock_datetime.now.return_value.strftime.return_value = "20250110_120000"
        
        # Create directory first
        expected_dir = os.path.join(self.test_dir, f"{OUTPUT_DIR_PREFIX}20250110_120000")
        os.makedirs(expected_dir)
        
        # Should not raise error due to exist_ok=True
        result = create_timestamped_directory(self.test_dir)
        self.assertEqual(result, expected_dir)


class TestSaveFile(unittest.TestCase):
    """Test save_file function."""
    
    def setUp(self):
        """Set up test directory."""
        self.test_dir = tempfile.mkdtemp()
        self.test_file = os.path.join(self.test_dir, "test.txt")
    
    def tearDown(self):
        """Clean up test directory."""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_save_simple_file(self):
        """Test saving a simple text file."""
        content = "Hello, World!"
        save_file(self.test_file, content)
        
        with open(self.test_file, 'r') as f:
            saved_content = f.read()
        
        self.assertEqual(saved_content, content)
    
    def test_save_creates_directory(self):
        """Test that save_file creates parent directory if needed."""
        nested_file = os.path.join(self.test_dir, "subdir", "nested", "file.txt")
        content = "Nested content"
        
        save_file(nested_file, content)
        
        self.assertTrue(os.path.exists(nested_file))
        with open(nested_file, 'r') as f:
            self.assertEqual(f.read(), content)
    
    def test_save_with_append_mode(self):
        """Test saving with append mode."""
        save_file(self.test_file, "First line\n")
        save_file(self.test_file, "Second line\n", mode='a')
        
        with open(self.test_file, 'r') as f:
            content = f.read()
        
        self.assertEqual(content, "First line\nSecond line\n")
    
    def test_save_with_different_encoding(self):
        """Test saving with different encoding."""
        content = "Special chars: é à ñ"
        save_file(self.test_file, content, encoding='utf-8')
        
        with open(self.test_file, 'r', encoding='utf-8') as f:
            saved_content = f.read()
        
        self.assertEqual(saved_content, content)
    
    @patch('model_checker.output.helpers.open', side_effect=OSError("Permission denied"))
    def test_save_raises_output_io_error(self, mock_open):
        """Test that OSError is converted to OutputIOError."""
        with self.assertRaises(OutputIOError) as context:
            save_file(self.test_file, "content")
        
        self.assertIn("Permission denied", str(context.exception))
        self.assertIn(self.test_file, str(context.exception))
    
    def test_save_empty_content(self):
        """Test saving empty content."""
        save_file(self.test_file, "")
        
        self.assertTrue(os.path.exists(self.test_file))
        with open(self.test_file, 'r') as f:
            self.assertEqual(f.read(), "")


class TestSaveJson(unittest.TestCase):
    """Test save_json function."""
    
    def setUp(self):
        """Set up test directory."""
        self.test_dir = tempfile.mkdtemp()
        self.test_file = os.path.join(self.test_dir, "test.json")
    
    def tearDown(self):
        """Clean up test directory."""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_save_simple_json(self):
        """Test saving simple JSON data."""
        data = {"key": "value", "number": 42}
        save_json(self.test_file, data)
        
        with open(self.test_file, 'r') as f:
            loaded_data = json.load(f)
        
        self.assertEqual(loaded_data, data)
    
    def test_save_complex_json(self):
        """Test saving complex JSON data."""
        data = {
            "list": [1, 2, 3],
            "nested": {"a": 1, "b": 2},
            "null": None,
            "bool": True
        }
        save_json(self.test_file, data)
        
        with open(self.test_file, 'r') as f:
            loaded_data = json.load(f)
        
        self.assertEqual(loaded_data, data)
    
    def test_save_with_custom_indent(self):
        """Test saving with custom indentation."""
        data = {"key": "value"}
        save_json(self.test_file, data, indent=2)
        
        with open(self.test_file, 'r') as f:
            content = f.read()
        
        # Should have 2-space indentation
        self.assertIn('  "key"', content)
    
    def test_save_with_ensure_ascii(self):
        """Test saving with ensure_ascii option."""
        data = {"text": "Hello 世界"}
        save_json(self.test_file, data, ensure_ascii=True)
        
        with open(self.test_file, 'r') as f:
            content = f.read()
        
        # Non-ASCII should be escaped
        self.assertIn('\\u4e16\\u754c', content)
    
    def test_save_non_serializable_raises_error(self):
        """Test that non-serializable data raises OutputIOError."""
        data = {"object": object()}  # object() is not JSON serializable
        
        with self.assertRaises(OutputIOError) as context:
            save_json(self.test_file, data)
        
        self.assertIn("JSON serialization error", str(context.exception))
    
    @patch('model_checker.output.helpers.save_file')
    def test_save_json_uses_save_file(self, mock_save_file):
        """Test that save_json uses save_file internally."""
        data = {"key": "value"}
        save_json(self.test_file, data)
        
        mock_save_file.assert_called_once()
        args = mock_save_file.call_args[0]
        self.assertEqual(args[0], self.test_file)
        self.assertIn('"key"', args[1])


class TestCombineMarkdownSections(unittest.TestCase):
    """Test combine_markdown_sections function."""
    
    def test_combine_simple_sections(self):
        """Test combining simple markdown sections."""
        sections = ["# Header 1", "## Header 2", "Some content"]
        result = combine_markdown_sections(sections)
        
        expected = "# Header 1\n\n---\n\n## Header 2\n\n---\n\nSome content"
        self.assertEqual(result, expected)
    
    def test_combine_with_custom_separator(self):
        """Test combining with custom separator."""
        sections = ["Section 1", "Section 2"]
        result = combine_markdown_sections(sections, separator="\n***\n")
        
        expected = "Section 1\n***\nSection 2"
        self.assertEqual(result, expected)
    
    def test_filters_empty_sections(self):
        """Test that empty sections are filtered out."""
        sections = ["Content", "", "  ", None, "More content"]
        result = combine_markdown_sections(sections)
        
        expected = "Content\n\n---\n\nMore content"
        self.assertEqual(result, expected)
    
    def test_empty_list_returns_empty_string(self):
        """Test that empty list returns empty string."""
        result = combine_markdown_sections([])
        self.assertEqual(result, "")
    
    def test_all_empty_sections_returns_empty_string(self):
        """Test that all empty sections returns empty string."""
        sections = ["", "  ", None]
        result = combine_markdown_sections(sections)
        self.assertEqual(result, "")
    
    def test_preserves_whitespace_in_content(self):
        """Test that whitespace within content is preserved."""
        sections = ["  Indented content", "Line 1\nLine 2"]
        result = combine_markdown_sections(sections)
        
        self.assertIn("  Indented content", result)
        self.assertIn("Line 1\nLine 2", result)


class TestExtractModelData(unittest.TestCase):
    """Test extract_model_data function."""
    
    def test_extract_from_model_not_found(self):
        """Test extraction when model is not found."""
        model = Mock()
        model.z3_model_status = False
        
        result = extract_model_data(model, "example1", "theory1")
        
        self.assertEqual(result["example"], "example1")
        self.assertEqual(result["theory"], "theory1")
        self.assertFalse(result["has_model"])
        self.assertIsNone(result["evaluation_world"])
        self.assertEqual(result["states"], {"possible": [], "impossible": [], "worlds": []})
        self.assertEqual(result["relations"], {})
        self.assertEqual(result["propositions"], {})
    
    def test_extract_from_model_found(self):
        """Test extraction when model is found."""
        model = Mock()
        model.z3_model_status = True
        model.extract_states = Mock(return_value={
            "possible": [1, 2],
            "impossible": [3],
            "worlds": [1, 2, 3]
        })
        model.extract_evaluation_world = Mock(return_value=1)
        model.extract_propositions = Mock(return_value={"p": True, "q": False})
        model.extract_relations = Mock(return_value={"R": [(1, 2)]})
        
        result = extract_model_data(model, "example1", "theory1")
        
        self.assertEqual(result["example"], "example1")
        self.assertEqual(result["theory"], "theory1")
        self.assertTrue(result["has_model"])
        self.assertEqual(result["evaluation_world"], 1)
        self.assertEqual(result["states"]["possible"], [1, 2])
        self.assertEqual(result["propositions"], {"p": True, "q": False})
        self.assertEqual(result["relations"], {"R": [(1, 2)]})
    
    def test_extract_missing_methods(self):
        """Test extraction when model lacks extraction methods."""
        model = Mock(spec=['z3_model_status'])
        model.z3_model_status = True
        
        result = extract_model_data(model, "example1", "theory1")
        
        self.assertTrue(result["has_model"])
        self.assertEqual(result["states"], {"possible": [], "impossible": [], "worlds": []})
        self.assertIsNone(result["evaluation_world"])
        self.assertEqual(result["propositions"], {})
        self.assertEqual(result["relations"], {})
    
    def test_extract_partial_methods(self):
        """Test extraction when model has some but not all methods."""
        model = Mock(spec=['z3_model_status', 'extract_states', 'extract_evaluation_world'])
        model.z3_model_status = True
        model.extract_states = Mock(return_value={"possible": [1], "impossible": [], "worlds": [1]})
        model.extract_evaluation_world = Mock(return_value=1)
        
        result = extract_model_data(model, "example1", "theory1")
        
        self.assertTrue(result["has_model"])
        self.assertEqual(result["states"]["possible"], [1])
        self.assertEqual(result["evaluation_world"], 1)
        self.assertEqual(result["propositions"], {})  # Missing method
        self.assertEqual(result["relations"], {})     # Missing method
    
    def test_extract_with_none_values(self):
        """Test extraction when methods return None."""
        model = Mock()
        model.z3_model_status = True
        model.extract_states = Mock(return_value=None)
        model.extract_evaluation_world = Mock(return_value=None)
        model.extract_propositions = Mock(return_value=None)
        model.extract_relations = Mock(return_value=None)
        
        result = extract_model_data(model, "example1", "theory1")
        
        # Should handle None gracefully
        self.assertTrue(result["has_model"])
        self.assertIsNone(result["states"])
        self.assertIsNone(result["evaluation_world"])
        self.assertIsNone(result["propositions"])
        self.assertIsNone(result["relations"])


class TestEnsureDirectoryExists(unittest.TestCase):
    """Test ensure_directory_exists function."""
    
    def setUp(self):
        """Set up test directory."""
        self.test_dir = tempfile.mkdtemp()
    
    def tearDown(self):
        """Clean up test directory."""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_ensure_new_directory(self):
        """Test ensuring a new directory exists."""
        new_dir = os.path.join(self.test_dir, "new_directory")
        
        ensure_directory_exists(new_dir)
        
        self.assertTrue(os.path.exists(new_dir))
        self.assertTrue(os.path.isdir(new_dir))
    
    def test_ensure_existing_directory(self):
        """Test ensuring an existing directory exists."""
        existing_dir = os.path.join(self.test_dir, "existing")
        os.makedirs(existing_dir)
        
        # Should not raise error
        ensure_directory_exists(existing_dir)
        
        self.assertTrue(os.path.exists(existing_dir))
    
    def test_ensure_nested_directory(self):
        """Test ensuring nested directories are created."""
        nested_dir = os.path.join(self.test_dir, "a", "b", "c", "d")
        
        ensure_directory_exists(nested_dir)
        
        self.assertTrue(os.path.exists(nested_dir))
    
    @patch('model_checker.output.helpers.os.makedirs')
    def test_ensure_raises_on_os_error(self, mock_makedirs):
        """Test that OSError is converted to OutputDirectoryError."""
        mock_makedirs.side_effect = OSError("Permission denied")
        
        with self.assertRaises(OutputDirectoryError) as context:
            ensure_directory_exists("/some/path")
        
        self.assertIn("Permission denied", str(context.exception))
        self.assertIn("/some/path", str(context.exception))


class TestGetFileExtension(unittest.TestCase):
    """Test get_file_extension function."""
    
    @patch('model_checker.output.constants.EXTENSIONS', {
        'markdown': 'md',
        'json': 'json',
        'notebook': 'ipynb'
    })
    def test_get_known_extensions(self):
        """Test getting known file extensions."""
        self.assertEqual(get_file_extension('markdown'), 'md')
        self.assertEqual(get_file_extension('json'), 'json')
        self.assertEqual(get_file_extension('notebook'), 'ipynb')
    
    @patch('model_checker.output.constants.EXTENSIONS', {
        'markdown': 'md',
        'json': 'json'
    })
    def test_get_unknown_extension(self):
        """Test getting unknown format returns format name."""
        self.assertEqual(get_file_extension('unknown'), 'unknown')
        self.assertEqual(get_file_extension('pdf'), 'pdf')
    
    @patch('model_checker.output.constants.EXTENSIONS', {})
    def test_get_extension_empty_map(self):
        """Test with empty extensions map."""
        self.assertEqual(get_file_extension('anything'), 'anything')


if __name__ == '__main__':
    unittest.main()