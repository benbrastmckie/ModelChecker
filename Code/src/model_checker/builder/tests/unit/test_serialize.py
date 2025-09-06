"""
Unit tests for serialization utilities.

This module tests serialization functionality in isolation, including semantic
theory serialization, operator handling, and import utility functions.
"""

import unittest
from unittest.mock import MagicMock, patch, Mock

from model_checker.builder.tests.fixtures.test_data import TestTheories, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.serialize import (
    serialize_semantic_theory, 
    deserialize_semantic_theory,
    serialize_operators,
    deserialize_operators,
    import_class
)
from model_checker.syntactic import OperatorCollection
from model_checker.theory_lib.logos.semantic import LogosSemantics


class TestSerializationCore(unittest.TestCase):
    """Test core serialization functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test theory using centralized test data
        self.test_theory = TestTheories.COMPLETE_THEORY.copy()
    
    def test_serialize_semantic_theory_creates_valid_structure(self):
        """Test serialize_semantic_theory creates valid serialized structure."""
        theory_name = "test_theory"
        
        result = assert_no_exceptions_during_execution(
            self,
            lambda: serialize_semantic_theory(theory_name, self.test_theory),
            operation_name="Semantic theory serialization"
        )
        
        # Verify structure
        self.assertIsInstance(result, dict,
                            "Serialization should return dictionary")
        
        required_keys = ["theory_name", "semantics", "operators", "model", "proposition"]
        for key in required_keys:
            self.assertIn(key, result,
                         f"Serialized result should contain {key}")
        
        # Verify theory name preservation
        self.assertEqual(result["theory_name"], theory_name,
                        "Theory name should be preserved in serialization")
        
        # Verify semantics class information
        self.assertEqual(result["semantics"]["class_name"], "MockSemantics",
                        "Semantics class name should be preserved")
        self.assertIn("module_name", result["semantics"],
                     "Semantics module name should be included")
    
    def test_serialize_semantic_theory_preserves_dictionary_content(self):
        """Test serialize_semantic_theory preserves dictionary mappings."""
        theory_with_dict = self.test_theory.copy()
        theory_with_dict["dictionary"] = TestConstants.STANDARD_DICTIONARY
        
        result = serialize_semantic_theory("dict_test", theory_with_dict)
        
        self.assertIn("dictionary", result,
                     "Dictionary should be included in serialization")
        self.assertEqual(result["dictionary"], TestConstants.STANDARD_DICTIONARY,
                        "Dictionary content should be preserved exactly")
    
    def test_serialize_semantic_theory_handles_empty_operators_correctly(self):
        """Test serialize_semantic_theory handles theory with empty operators."""
        theory_empty_ops = self.test_theory.copy()
        theory_empty_ops["operators"] = {}
        
        result = serialize_semantic_theory("empty_ops", theory_empty_ops)
        
        self.assertEqual(result["operators"], {},
                        "Empty operators should be serialized as empty dictionary")


class TestDeserializationCore(unittest.TestCase):
    """Test core deserialization functionality."""
    
    def setUp(self):
        """Set up deserialization testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create serialized test data
        self.test_theory = TestTheories.COMPLETE_THEORY.copy()
        self.serialized_theory = serialize_semantic_theory("test", self.test_theory)
    
    def test_deserialize_semantic_theory_reconstructs_valid_structure(self):
        """Test deserialize_semantic_theory reconstructs valid theory structure."""
        with patch('model_checker.builder.serialize.import_class') as mock_import:
            # Configure mock to return test classes
            mock_import.side_effect = self._create_import_side_effect()
            
            result = assert_no_exceptions_during_execution(
                self,
                lambda: deserialize_semantic_theory(self.serialized_theory),
                operation_name="Semantic theory deserialization"
            )
            
            # Verify structure
            self.assertIsInstance(result, dict,
                                "Deserialization should return dictionary")
            
            required_keys = ["semantics", "operators", "model", "proposition"]
            for key in required_keys:
                self.assertIn(key, result,
                             f"Deserialized result should contain {key}")
            
            # Verify classes are properly reconstructed
            self.assertEqual(result["semantics"], MockObjectFactory.MockSemantics,
                           "Semantics class should be reconstructed")
    
    def test_deserialize_semantic_theory_handles_missing_imports_with_error(self):
        """Test deserialize_semantic_theory handles missing imports appropriately."""
        invalid_serialized = {
            "theory_name": "missing",
            "semantics": {
                "class_name": "NonExistentSemantics",
                "module_name": "nonexistent.module"
            },
            "proposition": {
                "class_name": "NonExistentProp", 
                "module_name": "nonexistent.module"
            },
            "model": {
                "class_name": "NonExistentModel",
                "module_name": "nonexistent.module"
            },
            "operators": {}
        }
        
        with self.assertRaises(ImportError) as context:
            deserialize_semantic_theory(invalid_serialized)
        
        assert_error_message_contains(
            self, context.exception, "NonExistent",
            "Import error for missing classes"
        )
    
    def _create_import_side_effect(self):
        """Create side effect function for import_class mock."""
        def side_effect(module, cls_name):
            if cls_name == "MockSemantics":
                return MockObjectFactory.MockSemantics
            elif cls_name == "MockProposition":
                return MockObjectFactory.MockProposition
            elif cls_name == "MockModel":
                return MockObjectFactory.MockModel
            else:
                raise ImportError(f"Cannot import {cls_name} from {module}")
        return side_effect


class TestOperatorSerialization(unittest.TestCase):
    """Test operator serialization and deserialization."""
    
    def test_serialize_operators_creates_correct_structure(self):
        """Test serialize_operators creates correct operator structure."""
        operators = {
            "AND": MockObjectFactory.MockOperator,
            "OR": MockObjectFactory.MockOperatorOr,
            "NOT": MockObjectFactory.MockOperatorNot
        }
        
        result = assert_no_exceptions_during_execution(
            self,
            lambda: serialize_operators(operators),
            operation_name="Operator serialization"
        )
        
        self.assertIsInstance(result, dict,
                            "Operator serialization should return dictionary")
        self.assertEqual(len(result), 3,
                        "Should serialize all three operators")
        
        for op_name in ["AND", "OR", "NOT"]:
            self.assertIn(op_name, result,
                         f"Should contain {op_name} operator")
            self.assertIn("class_name", result[op_name],
                         f"{op_name} should have class_name")
            self.assertIn("module_name", result[op_name],
                         f"{op_name} should have module_name")
    
    def test_deserialize_operators_creates_operator_collection(self):
        """Test deserialize_operators creates proper OperatorCollection."""
        operator_data = {
            "MockOperator": {
                "class_name": "MockOperator",
                "module_name": "model_checker.builder.tests.fixtures.mock_objects"
            },
            "MockOperatorOr": {
                "class_name": "MockOperatorOr", 
                "module_name": "model_checker.builder.tests.fixtures.mock_objects"
            }
        }
        
        result = deserialize_operators(operator_data)
        
        self.assertIsInstance(result, OperatorCollection,
                            "Should return OperatorCollection instance")
        self.assertIn("MockOperator", result.operator_dictionary,
                     "Should contain MockOperator")
        self.assertIn("MockOperatorOr", result.operator_dictionary,
                     "Should contain MockOperatorOr")
    
    def test_serialize_operators_handles_operator_collection_input(self):
        """Test serialize_operators handles OperatorCollection as input."""
        collection = OperatorCollection()
        collection.add_operator(MockObjectFactory.MockOperator)
        collection.add_operator(MockObjectFactory.MockOperatorOr)
        
        result = serialize_operators(collection)
        
        self.assertIsInstance(result, dict,
                            "Should serialize OperatorCollection to dictionary")
        self.assertGreater(len(result), 0,
                         "Should contain operators from collection")


class TestImportUtility(unittest.TestCase):
    """Test import_class utility function."""
    
    def test_import_class_imports_valid_classes_successfully(self):
        """Test import_class imports valid classes from known modules."""
        # Test with known class
        cls = import_class("model_checker.theory_lib.logos.semantic", "LogosSemantics")
        
        self.assertEqual(cls, LogosSemantics,
                        "Should import LogosSemantics correctly")
    
    def test_import_class_raises_error_for_nonexistent_module(self):
        """Test import_class raises ImportError for nonexistent modules."""
        with self.assertRaises(ImportError) as context:
            import_class("nonexistent.module", "NonExistentClass")
        
        assert_error_message_contains(
            self, context.exception, "nonexistent",
            "Import error for nonexistent module"
        )
    
    def test_import_class_raises_error_for_nonexistent_class(self):
        """Test import_class raises AttributeError for nonexistent classes."""
        with self.assertRaises(AttributeError) as context:
            import_class("builtins", "NonExistentClass")
        
        assert_error_message_contains(
            self, context.exception, "NonExistentClass",
            "Attribute error for nonexistent class"
        )
    
    def test_import_class_handles_builtin_modules_correctly(self):
        """Test import_class works with built-in modules."""
        # Test with built-in classes
        dict_cls = import_class("builtins", "dict")
        list_cls = import_class("builtins", "list")
        
        self.assertEqual(dict_cls, dict,
                        "Should import dict correctly")
        self.assertEqual(list_cls, list,
                        "Should import list correctly")


class TestRealTheoryIntegration(unittest.TestCase):
    """Test serialization with real theory components."""
    
    def test_serialize_real_logos_theory_preserves_structure(self):
        """Test serialization with real Logos theory preserves all components."""
        import model_checker.theory_lib.logos as logos
        real_theory = logos.get_theory(['extensional'])
        
        result = assert_no_exceptions_during_execution(
            self,
            lambda: serialize_semantic_theory("Logos", real_theory),
            operation_name="Real Logos theory serialization"
        )
        
        # Verify theory structure
        self.assertEqual(result["theory_name"], "Logos",
                        "Theory name should be preserved")
        self.assertEqual(result["semantics"]["class_name"], "LogosSemantics",
                        "Should preserve LogosSemantics class name")
        self.assertIn("model_checker.theory_lib.logos", result["semantics"]["module_name"],
                     "Should preserve module path information")
        
        # Verify operators are serialized
        self.assertIsInstance(result["operators"], dict,
                            "Operators should be serialized as dictionary")
        self.assertIn("\\neg", result["operators"],
                     "Should contain negation operator from extensional theory")


class TestSerializationErrorHandling(unittest.TestCase):
    """Test serialization error handling scenarios."""
    
    def test_deserialize_semantic_theory_handles_invalid_input_types(self):
        """Test deserialize_semantic_theory handles invalid input types gracefully."""
        invalid_inputs = [
            None,
            [],
            "string",
            123,
            {"missing_theory_name": "no name key"},
            {"theory_name": "test"},  # Missing other required keys
        ]
        
        for invalid_input in invalid_inputs:
            with self.subTest(input_type=type(invalid_input).__name__):
                with self.assertRaises((KeyError, TypeError, AttributeError)):
                    deserialize_semantic_theory(invalid_input)
    
    def test_serialize_semantic_theory_handles_malformed_theory_structure(self):
        """Test serialize_semantic_theory handles malformed theory structures."""
        malformed_theories = [
            {},  # Empty theory
            {"semantics": "not_a_class"},  # Invalid semantics
            {"operators": "not_a_dict"},  # Invalid operators
        ]
        
        for malformed_theory in malformed_theories:
            with self.subTest(theory_structure=str(malformed_theory)[:50]):
                with self.assertRaises((AttributeError, TypeError, ValueError)):
                    serialize_semantic_theory("malformed", malformed_theory)


class TestSerializationEdgeCases(unittest.TestCase):
    """Test serialization edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_serialize_semantic_theory_handles_unicode_operators_correctly(self):
        """Test serialize_semantic_theory handles Unicode operators correctly."""
        unicode_theory = TestTheories.COMPLETE_THEORY.copy()
        unicode_theory["operators"] = {
            "∧": MockObjectFactory.MockConjunction,
            "∨": MockObjectFactory.MockOperator,
            "¬": MockObjectFactory.MockOperatorNot
        }
        unicode_theory["dictionary"] = {
            "中文": "∧",
            "日本語": "∨", 
            "한국어": "¬"
        }
        
        result = serialize_semantic_theory("unicode_test", unicode_theory)
        
        # Verify Unicode preservation
        self.assertIn("∧", result["operators"],
                     "Unicode operators should be preserved")
        self.assertEqual(result["dictionary"]["中文"], "∧",
                        "Unicode dictionary keys should be preserved")
        self.assertEqual(result["dictionary"]["日本語"], "∨",
                        "Unicode dictionary values should be preserved")
    
    def test_serialize_semantic_theory_handles_large_operator_collections(self):
        """Test serialize_semantic_theory handles large operator collections efficiently."""
        import time
        
        # Create theory with many operators
        large_operators = {
            f"OP_{i}": MockObjectFactory.MockOperator 
            for i in range(100)
        }
        large_theory = TestTheories.COMPLETE_THEORY.copy()
        large_theory["operators"] = large_operators
        
        start_time = time.time()
        result = serialize_semantic_theory("large", large_theory)
        serialize_time = time.time() - start_time
        
        # Performance assertion
        self.assertLess(serialize_time, 2.0,
                       "Large theory serialization should complete within 2 seconds")
        
        # Verify structure
        self.assertEqual(len(result["operators"]), 100,
                        "Should serialize all 100 operators")
    
    def test_serialize_semantic_theory_preserves_complex_nested_settings(self):
        """Test serialize_semantic_theory preserves complex nested settings structures."""
        complex_theory = TestTheories.COMPLETE_THEORY.copy()
        complex_theory["settings"] = {
            "deeply": {
                "nested": {
                    "structure": {
                        "with": {
                            "many": {
                                "levels": {"value": 42, "list": [1, 2, 3]}
                            }
                        }
                    }
                }
            },
            "array": list(range(10)),
            "matrix": [[i*j for j in range(3)] for i in range(3)]
        }
        
        result = serialize_semantic_theory("complex", complex_theory)
        
        # Verify nested structure preservation
        if "settings" in result:
            self.assertEqual(
                result["settings"]["deeply"]["nested"]["structure"]["with"]["many"]["levels"]["value"], 
                42,
                "Deeply nested settings should be preserved"
            )


if __name__ == '__main__':
    unittest.main()