"""Simple unit tests for TemplateLoader class."""

import unittest
from unittest.mock import MagicMock
from model_checker.output.notebook.template_loader import TemplateLoader


class TestTemplateLoaderSimple(unittest.TestCase):
    """Test the TemplateLoader class functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.loader = TemplateLoader()
    
    def test_get_template_for_logos_semantics(self):
        """Test getting template for LogosSemantics class."""
        mock_class = MagicMock()
        mock_class.__name__ = 'LogosSemantics'
        
        template = self.loader.get_template_for_class(mock_class)
        self.assertIsNotNone(template)
        # Should return LogosNotebookTemplate instance
        self.assertEqual(template.__class__.__name__, 'LogosNotebookTemplate')
    
    def test_get_template_for_witness_semantics(self):
        """Test getting template for WitnessSemantics (Exclusion)."""
        mock_class = MagicMock()
        mock_class.__name__ = 'WitnessSemantics'
        
        template = self.loader.get_template_for_class(mock_class)
        self.assertIsNotNone(template)
        # Should return ExclusionNotebookTemplate instance
        self.assertEqual(template.__class__.__name__, 'ExclusionNotebookTemplate')
    
    def test_get_template_for_imposition_semantics(self):
        """Test getting template for ImpositionSemantics."""
        mock_class = MagicMock()
        mock_class.__name__ = 'ImpositionSemantics'
        
        template = self.loader.get_template_for_class(mock_class)
        self.assertIsNotNone(template)
        # Should return ImpositionNotebookTemplate instance
        self.assertEqual(template.__class__.__name__, 'ImpositionNotebookTemplate')
    
    def test_get_template_for_unknown_semantics(self):
        """Test getting template for unknown semantics returns fallback."""
        mock_class = MagicMock()
        mock_class.__name__ = 'UnknownSemantics'
        
        template = self.loader.get_template_for_class(mock_class)
        self.assertIsNotNone(template)
        # Should return DirectNotebookTemplate as fallback
        self.assertEqual(template.__class__.__name__, 'DirectNotebookTemplate')
    
    def test_template_loader_returns_instances(self):
        """Test that template loader returns template instances not classes."""
        mock_class = MagicMock()
        mock_class.__name__ = 'LogosSemantics'
        
        template = self.loader.get_template_for_class(mock_class)
        # Check it's an instance, not a class
        self.assertIsInstance(template, object)
        self.assertNotIsInstance(template, type)


if __name__ == '__main__':
    unittest.main()