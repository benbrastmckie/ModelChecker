"""Unit tests for the utils formatting module."""

import unittest
from model_checker.utils.formatting import (
    pretty_set_print, not_implemented_string, flatten
)


class TestPrettySetPrint(unittest.TestCase):
    """Test pretty_set_print function."""
    
    def test_empty_set(self):
        """Test formatting empty set."""
        result = pretty_set_print(set())
        self.assertEqual(result, "{}")
    
    def test_empty_frozenset(self):
        """Test formatting empty frozenset."""
        result = pretty_set_print(frozenset())
        self.assertEqual(result, "{}")
    
    def test_single_element_set(self):
        """Test formatting set with single element."""
        result = pretty_set_print({'a'})
        self.assertEqual(result, "{a}")
    
    def test_multiple_elements_sorted(self):
        """Test formatting set with multiple elements are sorted."""
        result = pretty_set_print({'c', 'a', 'b'})
        self.assertEqual(result, "{a, b, c}")
    
    def test_numeric_elements(self):
        """Test formatting set with numeric elements."""
        result = pretty_set_print({3, 1, 2})
        self.assertEqual(result, "{1, 2, 3}")
    
    def test_mixed_types(self):
        """Test formatting set with mixed types."""
        result = pretty_set_print({1, 'a', 2.5})
        # Should convert all to strings and sort
        self.assertIn('1', result)
        self.assertIn('a', result)
        self.assertIn('2.5', result)
        self.assertTrue(result.startswith('{'))
        self.assertTrue(result.endswith('}'))
    
    def test_frozenset_input(self):
        """Test formatting frozenset input."""
        result = pretty_set_print(frozenset(['x', 'y', 'z']))
        self.assertEqual(result, "{x, y, z}")


class TestNotImplementedString(unittest.TestCase):
    """Test not_implemented_string function."""
    
    def test_proposition_defaults_message(self):
        """Test message for PropositionDefaults class."""
        result = not_implemented_string("PropositionDefaults")
        self.assertIn("User should implement subclass(es)", result)
        self.assertIn("PropositionDefaults", result)
        self.assertIn("propositions", result)
        self.assertIn("letter", result)
    
    def test_operator_defaults_message(self):
        """Test message for OperatorDefaults class."""
        result = not_implemented_string("OperatorDefaults")
        self.assertIn("User should implement subclass(es)", result)
        self.assertIn("OperatorDefaults", result)
        self.assertIn("operators", result)
        self.assertIn("logical language", result)
    
    def test_generic_class_message(self):
        """Test message for generic class name."""
        result = not_implemented_string("SomeClass")
        self.assertIn("Cannot instantiate SomeClass directly", result)
        self.assertIn("subclass", result)
    
    def test_empty_class_name(self):
        """Test message with empty class name."""
        result = not_implemented_string("")
        self.assertIn("Cannot instantiate  directly", result)


class TestFlatten(unittest.TestCase):
    """Test flatten function."""
    
    def test_empty_list(self):
        """Test flattening empty list."""
        result = flatten([])
        self.assertEqual(result, [])
    
    def test_flat_list(self):
        """Test flattening already flat list."""
        result = flatten([1, 2, 3])
        self.assertEqual(result, [1, 2, 3])
    
    def test_single_level_nested(self):
        """Test flattening single level nested list."""
        result = flatten([1, [2, 3], 4])
        self.assertEqual(result, [1, 2, 3, 4])
    
    def test_multiple_levels_nested(self):
        """Test flattening multiple levels of nesting."""
        result = flatten([1, [2, [3, [4, 5]]]])
        self.assertEqual(result, [1, 2, 3, 4, 5])
    
    def test_mixed_types(self):
        """Test flattening list with mixed types."""
        result = flatten(['a', [1, ['b', 2]], 'c'])
        self.assertEqual(result, ['a', 1, 'b', 2, 'c'])
    
    def test_empty_nested_lists(self):
        """Test flattening with empty nested lists."""
        result = flatten([1, [], [2, []], [3]])
        self.assertEqual(result, [1, 2, 3])
    
    def test_deeply_nested(self):
        """Test flattening deeply nested structure."""
        result = flatten([[[[[[1]]]]]])
        self.assertEqual(result, [1])
    
    def test_none_values(self):
        """Test flattening list containing None values."""
        result = flatten([None, [None, 1], [2, None]])
        self.assertEqual(result, [None, None, 1, 2, None])
    
    def test_string_elements(self):
        """Test that strings are not flattened."""
        result = flatten(['hello', ['world']])
        self.assertEqual(result, ['hello', 'world'])


if __name__ == '__main__':
    unittest.main()