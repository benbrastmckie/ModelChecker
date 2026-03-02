"""Unit tests for output error classes."""

import unittest
from model_checker.output.errors import (
    OutputError, OutputDirectoryError, OutputFormatError,
    OutputIOError, OutputStrategyError, NotebookGenerationError
)


class TestOutputError(unittest.TestCase):
    """Test base OutputError class."""
    
    def test_init_with_message_only(self):
        """Test initialization with message only."""
        error = OutputError("Test error message")
        
        self.assertEqual(str(error), "Test error message")
        self.assertEqual(error.context, {})
    
    def test_init_with_context(self):
        """Test initialization with message and context."""
        context = {'key': 'value', 'number': 42}
        error = OutputError("Test error", context)
        
        self.assertEqual(str(error), "Test error")
        self.assertEqual(error.context, context)
    
    def test_init_with_none_context(self):
        """Test initialization with None context."""
        error = OutputError("Test error", None)
        
        self.assertEqual(error.context, {})


class TestOutputDirectoryError(unittest.TestCase):
    """Test OutputDirectoryError class."""
    
    def test_init_basic(self):
        """Test basic initialization."""
        error = OutputDirectoryError("/path/to/dir", "Directory not found")
        
        expected_msg = "Output directory error for '/path/to/dir': Directory not found"
        self.assertIn(expected_msg, str(error))
        self.assertEqual(error.context['directory'], "/path/to/dir")
        self.assertEqual(error.context['reason'], "Directory not found")
        self.assertIsNone(error.context['suggestion'])
    
    def test_init_with_custom_suggestion(self):
        """Test initialization with custom suggestion."""
        error = OutputDirectoryError(
            "/path/to/dir", 
            "Cannot create", 
            "Try a different location"
        )
        
        self.assertIn("Try a different location", str(error))
        self.assertEqual(error.context['suggestion'], "Try a different location")
    
    def test_auto_suggestion_for_permission_error(self):
        """Test automatic suggestion for permission errors."""
        error = OutputDirectoryError("/path/to/dir", "Permission denied")
        
        self.assertIn("Check write permissions", str(error))
        self.assertIn("--output-dir flag", str(error))
    
    def test_auto_suggestion_for_exists_error(self):
        """Test automatic suggestion for exists errors."""
        error = OutputDirectoryError("/path/to/dir", "Directory already exists")
        
        self.assertIn("Use a different directory", str(error))
        self.assertIn("remove existing files", str(error))
    
    def test_auto_suggestion_for_space_error(self):
        """Test automatic suggestion for disk space errors."""
        error = OutputDirectoryError("/path/to/dir", "No space left on device")
        
        self.assertIn("Free up disk space", str(error))
        self.assertIn("different location", str(error))
    
    def test_no_auto_suggestion_for_other_errors(self):
        """Test no automatic suggestion for unrecognized errors."""
        error = OutputDirectoryError("/path/to/dir", "Unknown error")
        
        msg = str(error)
        self.assertIn("Unknown error", msg)
        # Should not have suggestion line
        self.assertNotIn("Suggestion:", msg.split('\n')[0])


class TestOutputFormatError(unittest.TestCase):
    """Test OutputFormatError class."""
    
    def test_init_basic(self):
        """Test basic initialization."""
        error = OutputFormatError("markdown", "Invalid syntax")
        
        expected_msg = "Format generation error for 'markdown': Invalid syntax"
        self.assertIn(expected_msg, str(error))
        self.assertEqual(error.context['format'], "markdown")
        self.assertEqual(error.context['reason'], "Invalid syntax")
    
    def test_init_with_custom_suggestion(self):
        """Test initialization with custom suggestion."""
        error = OutputFormatError(
            "json",
            "Encoding failed",
            "Check for non-UTF8 characters"
        )
        
        self.assertIn("Check for non-UTF8 characters", str(error))
        self.assertEqual(error.context['suggestion'], "Check for non-UTF8 characters")
    
    def test_auto_suggestion_for_json_serialization(self):
        """Test automatic suggestion for JSON serialization errors."""
        error = OutputFormatError("json", "Object not serializable")
        
        self.assertIn("Ensure all data is JSON-serializable", str(error))
        self.assertIn("no custom objects", str(error))
    
    def test_auto_suggestion_for_markdown(self):
        """Test automatic suggestion for markdown errors."""
        error = OutputFormatError("markdown", "Rendering failed")
        
        self.assertIn("Check for invalid markdown syntax", str(error))
        self.assertIn("ANSI codes", str(error))
    
    def test_auto_suggestion_for_notebook(self):
        """Test automatic suggestion for notebook errors."""
        error = OutputFormatError("notebook", "Template error")
        
        self.assertIn("Verify notebook template exists", str(error))
        self.assertIn("valid JSON", str(error))
    
    def test_no_auto_suggestion_for_unknown_format(self):
        """Test no automatic suggestion for unknown formats."""
        error = OutputFormatError("pdf", "Generation failed")
        
        msg = str(error)
        self.assertIn("Generation failed", msg)
        # First line should not have suggestion
        self.assertNotIn("Suggestion:", msg.split('\n')[0])


class TestOutputIOError(unittest.TestCase):
    """Test OutputIOError class."""
    
    def test_init_basic(self):
        """Test basic initialization."""
        error = OutputIOError("output.txt", "File locked")
        
        expected_msg = "Failed to write 'output.txt': File locked"
        self.assertIn(expected_msg, str(error))
        self.assertEqual(error.context['filename'], "output.txt")
        self.assertEqual(error.context['reason'], "File locked")
    
    def test_init_with_custom_suggestion(self):
        """Test initialization with custom suggestion."""
        error = OutputIOError(
            "output.json",
            "Write failed",
            "Close the file in other programs"
        )
        
        self.assertIn("Close the file in other programs", str(error))
        self.assertEqual(error.context['suggestion'], "Close the file in other programs")
    
    def test_auto_suggestion_for_permission_error(self):
        """Test automatic suggestion for permission errors."""
        error = OutputIOError("output.md", "Permission denied")
        
        self.assertIn("Check file permissions", str(error))
        self.assertIn("output directory", str(error))
    
    def test_auto_suggestion_for_exists_error(self):
        """Test automatic suggestion for exists errors."""
        error = OutputIOError("output.json", "Directory does not exist")
        
        self.assertIn("Ensure output directory exists", str(error))
        self.assertIn("writable", str(error))
    
    def test_auto_suggestion_for_space_error(self):
        """Test automatic suggestion for disk space errors."""
        error = OutputIOError("large_output.md", "No space left")
        
        self.assertIn("Free up disk space", str(error))
        self.assertIn("choose different output location", str(error))
    
    def test_no_auto_suggestion_for_other_errors(self):
        """Test no automatic suggestion for unrecognized errors."""
        error = OutputIOError("output.txt", "Network error")
        
        msg = str(error)
        self.assertIn("Network error", msg)
        # First line should not have suggestion
        self.assertNotIn("Suggestion:", msg.split('\n')[0])


class TestOutputStrategyError(unittest.TestCase):
    """Test OutputStrategyError class."""
    
    def test_init(self):
        """Test initialization."""
        error = OutputStrategyError("interactive", "User cancelled")
        
        expected_msg = "Strategy 'interactive' failed: User cancelled"
        self.assertEqual(str(error), expected_msg)
        self.assertEqual(error.context['strategy'], "interactive")
        self.assertEqual(error.context['reason'], "User cancelled")
    
    def test_different_strategies(self):
        """Test with different strategy names."""
        strategies = ["batch", "sequential", "parallel"]
        
        for strategy in strategies:
            error = OutputStrategyError(strategy, "Test reason")
            self.assertIn(f"Strategy '{strategy}' failed", str(error))
            self.assertEqual(error.context['strategy'], strategy)


class TestNotebookGenerationError(unittest.TestCase):
    """Test NotebookGenerationError class."""
    
    def test_init(self):
        """Test initialization."""
        error = NotebookGenerationError("example_1", "Template not found")
        
        expected_msg = "Failed to generate notebook for 'example_1': Template not found"
        self.assertEqual(str(error), expected_msg)
        self.assertEqual(error.context['example'], "example_1")
        self.assertEqual(error.context['reason'], "Template not found")
    
    def test_different_examples(self):
        """Test with different example names."""
        examples = ["test_case", "complex_model", "simple_logic"]
        
        for example in examples:
            error = NotebookGenerationError(example, "Conversion failed")
            self.assertIn(f"Failed to generate notebook for '{example}'", str(error))
            self.assertEqual(error.context['example'], example)
    
    def test_inheritance_from_output_error(self):
        """Test that all errors inherit from OutputError."""
        errors = [
            OutputDirectoryError("/path", "reason"),
            OutputFormatError("json", "reason"),
            OutputIOError("file.txt", "reason"),
            OutputStrategyError("batch", "reason"),
            NotebookGenerationError("example", "reason")
        ]
        
        for error in errors:
            self.assertIsInstance(error, OutputError)
            self.assertIsInstance(error.context, dict)


class TestErrorStringRepresentations(unittest.TestCase):
    """Test string representations of all error classes."""
    
    def test_multiline_error_messages(self):
        """Test that multiline error messages format correctly."""
        error = OutputDirectoryError(
            "/very/long/path/to/directory",
            "Permission denied for user",
            "Run with sudo or change permissions"
        )
        
        lines = str(error).split('\n')
        self.assertGreater(len(lines), 1)
        self.assertIn("Output directory error", lines[0])
        self.assertIn("Suggestion:", lines[1])
    
    def test_error_context_preservation(self):
        """Test that context is preserved through inheritance."""
        base_error = OutputError("Base message", {'base_key': 'base_value'})
        
        dir_error = OutputDirectoryError("/path", "reason")
        dir_error.context.update({'inherited': True})
        
        self.assertIn('directory', dir_error.context)
        self.assertIn('inherited', dir_error.context)
        self.assertEqual(dir_error.context['inherited'], True)


if __name__ == '__main__':
    unittest.main()