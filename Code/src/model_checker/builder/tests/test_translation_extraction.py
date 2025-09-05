"""Tests for extracted translation module functionality."""

import unittest
from unittest.mock import Mock

# Test the new translation module before it exists (TDD)
try:
    from model_checker.builder.translation import OperatorTranslation
except ImportError:
    # Module doesn't exist yet - that's expected in TDD
    OperatorTranslation = None

from model_checker.builder.module import BuildModule


class TestTranslationExtraction(unittest.TestCase):
    """Test that translation functionality works after extraction."""
    
    @unittest.skipIf(OperatorTranslation is None, "OperatorTranslation not yet implemented")
    def test_translation_exists(self):
        """Test that OperatorTranslation class exists."""
        self.assertIsNotNone(OperatorTranslation)
    
    @unittest.skipIf(OperatorTranslation is None, "OperatorTranslation not yet implemented")
    def test_translation_initialization(self):
        """Test OperatorTranslation can be initialized."""
        translation = OperatorTranslation()
        self.assertIsNotNone(translation)
    
    @unittest.skipIf(OperatorTranslation is None, "OperatorTranslation not yet implemented")
    def test_translate_method(self):
        """Test translate method exists and works."""
        translation = OperatorTranslation()
        
        # Test method exists
        self.assertTrue(hasattr(translation, 'translate'))
        
        # Test basic translation
        example_case = [
            ["p \\wedge q", "r \\vee s"],  # premises
            ["p \\rightarrow q"],  # conclusions
            {"N": 2}  # settings
        ]
        
        dictionary = {
            "\\wedge": "∧",
            "\\vee": "∨", 
            "\\rightarrow": "→"
        }
        
        result = translation.translate(example_case, dictionary)
        
        # Verify translation worked
        self.assertEqual(result[0], ["p ∧ q", "r ∨ s"])
        self.assertEqual(result[1], ["p → q"])
        self.assertEqual(result[2], {"N": 2})
    
    @unittest.skipIf(OperatorTranslation is None, "OperatorTranslation not yet implemented")
    def test_translate_example_method(self):
        """Test translate_example method exists and works."""
        translation = OperatorTranslation()
        
        # Test method exists
        self.assertTrue(hasattr(translation, 'translate_example'))
        
        # Test translation for multiple theories
        example_case = [["p \\wedge q"], ["r"], {"N": 2}]
        
        semantic_theories = {
            "Theory1": {
                "dictionary": {"\\wedge": "∧"}
            },
            "Theory2": {
                "dictionary": {"\\wedge": "&"}
            },
            "Theory3": {
                # No dictionary
            }
        }
        
        result = translation.translate_example(example_case, semantic_theories)
        
        # Verify result structure
        self.assertIsInstance(result, list)
        self.assertEqual(len(result), 3)
        
        # Check each theory's translation
        theory1_result = result[0]
        self.assertEqual(theory1_result[0], "Theory1")
        self.assertEqual(theory1_result[2][0], ["p ∧ q"])
        
        theory2_result = result[1]
        self.assertEqual(theory2_result[0], "Theory2")
        self.assertEqual(theory2_result[2][0], ["p & q"])
        
        theory3_result = result[2]
        self.assertEqual(theory3_result[0], "Theory3")
        self.assertEqual(theory3_result[2][0], ["p \\wedge q"])  # Unchanged
    
    def test_build_module_delegates_to_translation(self):
        """Test BuildModule delegates to translation after refactoring."""
        # This tests that BuildModule properly delegates after we implement translation
        
        mock_module = Mock()
        mock_flags = Mock()
        
        # After refactoring, translate methods should still work
        build_module = BuildModule.__new__(BuildModule)
        build_module.module = mock_module
        build_module.module_flags = mock_flags
        
        # Check translation methods exist
        self.assertTrue(hasattr(build_module, 'translate'))
        self.assertTrue(hasattr(build_module, 'translate_example'))


if __name__ == '__main__':
    unittest.main()