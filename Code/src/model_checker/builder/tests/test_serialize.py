"""Unit tests for serialization utilities following TESTING_STANDARDS.md."""
import unittest
from unittest.mock import MagicMock, patch
from model_checker.builder.serialize import (
    serialize_semantic_theory, 
    deserialize_semantic_theory,
    serialize_operators,
    deserialize_operators,
    import_class
)
from model_checker.syntactic import OperatorCollection
from model_checker.theory_lib.logos.semantic import LogosSemantics
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics


class MockSemantics:
    """Mock semantics class for testing."""
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"test": True}
    
    def __init__(self):
        self.data = "test_data"


class MockProposition:
    """Mock proposition class."""
    pass


class MockModel:
    """Mock model class."""
    pass


class MockOperator:
    """Mock operator class for testing."""
    name = "AND"
    arity = 2
    

class MockOperatorOr:
    """Mock OR operator class."""
    name = "OR"
    arity = 2
    

class MockOperatorNot:
    """Mock NOT operator class."""
    name = "NOT"
    arity = 1


class TestSerialization(unittest.TestCase):
    """Test serialization functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.test_theory = {
            "semantics": MockSemantics,
            "operators": {"AND": MockOperator, "OR": MockOperatorOr},
            "model": MockModel,
            "proposition": MockProposition
        }
    
    def test_serialize_simple_theory(self):
        """Test serialization of a simple theory."""
        # Arrange
        theory_name = "test"
        
        # Act
        result = serialize_semantic_theory(theory_name, self.test_theory)
        
        # Assert with descriptive message
        self.assertIsNotNone(
            result,
            "Serialization should return a result"
        )
        self.assertIsInstance(
            result,
            dict,
            "Serialization should return dict"
        )
        self.assertEqual(result["theory_name"], theory_name)
        
        # Check structure
        self.assertIn("semantics", result)
        self.assertIn("operators", result)
        self.assertIn("model", result)
        self.assertIn("proposition", result)
        
        # Check class names preserved
        self.assertEqual(
            result["semantics"]["class_name"],
            "MockSemantics",
            "Semantics class name should be preserved"
        )
    
    def test_deserialize_simple_theory(self):
        """Test deserialization of a simple theory."""
        # Arrange
        theory_name = "test"
        serialized = serialize_semantic_theory(theory_name, self.test_theory)
        
        # Act
        with patch('model_checker.builder.serialize.import_class') as mock_import:
            # Mock import_class to return our test classes
            def side_effect(module, cls_name):
                if cls_name == "MockSemantics":
                    return MockSemantics
                elif cls_name == "MockProposition":
                    return MockProposition
                elif cls_name == "MockModel":
                    return MockModel
            mock_import.side_effect = side_effect
            
            result = deserialize_semantic_theory(serialized)
        
        # Assert
        self.assertIsInstance(result, dict)
        self.assertIn("semantics", result)
        self.assertIn("operators", result)
        self.assertIn("model", result)
        self.assertIn("proposition", result)
        # Theory name is not included in deserialized result
        # Check that classes are deserialized correctly
        self.assertEqual(result["semantics"], MockSemantics)
    
    def test_serialize_operators(self):
        """Test operator serialization."""
        # Arrange - use operator classes
        operators = {
            "AND": MockOperator,
            "OR": MockOperatorOr,
            "NOT": MockOperatorNot
        }
        
        # Act
        result = serialize_operators(operators)
        
        # Assert
        self.assertIsInstance(result, dict)
        self.assertEqual(len(result), 3)
        self.assertIn("AND", result)
        self.assertEqual(result["AND"]["class_name"], "MockOperator")
        self.assertIn("module_name", result["AND"])
    
    def test_deserialize_operators(self):
        """Test operator deserialization."""
        # Arrange
        operator_data = {
            "AND": {
                "class_name": "MockOperator",
                "module_name": "model_checker.builder.tests.test_serialize"
            },
            "OR": {
                "class_name": "MockOperatorOr",
                "module_name": "model_checker.builder.tests.test_serialize"
            }
        }
        
        # Act
        result = deserialize_operators(operator_data)
        
        # Assert
        # Result should be an OperatorCollection
        self.assertIsInstance(result, OperatorCollection)
        # Check operators were added to collection
        self.assertIn("AND", result.operator_dictionary)
        self.assertIn("OR", result.operator_dictionary)
    
    def test_serialize_with_real_theory(self):
        """Test serialization with a real theory class."""
        # Arrange
        import model_checker.theory_lib.logos as logos
        real_theory = logos.get_theory(['extensional'])
        
        # Act
        result = serialize_semantic_theory("Logos", real_theory)
        
        # Assert
        self.assertEqual(result["theory_name"], "Logos")
        self.assertEqual(result["semantics"]["class_name"], "LogosSemantics")
        self.assertIn("model_checker.theory_lib.logos", result["semantics"]["module_name"])
        # Check operators are serialized
        self.assertIsInstance(result["operators"], dict)
        # Should have at least negation from extensional
        self.assertIn("\\neg", result["operators"])
    
    def test_import_class(self):
        """Test the import_class utility function."""
        # Test importing a real class
        cls = import_class("model_checker.theory_lib.logos.semantic", "LogosSemantics")
        self.assertEqual(cls, LogosSemantics)
        
        # Test importing non-existent class
        with self.assertRaises((ImportError, AttributeError)):
            import_class("nonexistent.module", "NonExistentClass")
    
    def test_serialize_with_dictionary(self):
        """Test serialization preserves dictionary field."""
        # Arrange
        theory_with_dict = self.test_theory.copy()
        theory_with_dict["dictionary"] = {"∧": "\\wedge", "∨": "\\vee"}
        
        # Act
        result = serialize_semantic_theory("test", theory_with_dict)
        
        # Assert
        self.assertIn("dictionary", result)
        self.assertEqual(result["dictionary"]["∧"], "\\wedge")
    
    def test_deserialize_with_missing_imports(self):
        """Test deserialization handles missing imports gracefully."""
        # Arrange
        serialized = {
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
        
        # Act & Assert
        with self.assertRaises(ImportError):
            deserialize_semantic_theory(serialized)
    
    def test_round_trip_preservation(self):
        """Test data integrity through serialization - verify structure preserved."""
        # Arrange
        theory_name = "roundtrip"
        
        # Act
        serialized = serialize_semantic_theory(theory_name, self.test_theory)
        
        # Assert - check serialized structure preserves key information
        self.assertEqual(serialized["theory_name"], theory_name)
        self.assertEqual(serialized["semantics"]["class_name"], "MockSemantics")
        self.assertEqual(serialized["model"]["class_name"], "MockModel")
        self.assertEqual(serialized["proposition"]["class_name"], "MockProposition")
        
        # Operators should be serialized
        self.assertIn("operators", serialized)
    
    def test_empty_operators(self):
        """Test serialization with empty operators dict."""
        # Arrange
        theory_empty_ops = self.test_theory.copy()
        theory_empty_ops["operators"] = {}
        
        # Act
        result = serialize_semantic_theory("empty_ops", theory_empty_ops)
        
        # Assert
        self.assertEqual(result["operators"], {})
    
    def test_operator_collection_serialization(self):
        """Test serialization of OperatorCollection objects."""
        # Arrange - create real OperatorCollection with mock operator
        from model_checker.syntactic import OperatorCollection
        collection = OperatorCollection()
        collection.add_operator(MockOperator)
        
        # Act
        result = serialize_operators(collection)
        
        # Assert
        self.assertIsInstance(result, dict)
        self.assertIn("AND", result)  # MockOperator has name "AND"
        self.assertEqual(result["AND"]["class_name"], "MockOperator")


class TestSerializationParameterized(unittest.TestCase):
    """Parameterized tests for various serialization scenarios."""
    
    def test_serialize_various_theory_types(self):
        """Test serialization with various theory configurations."""
        test_cases = [
            # (name, theory_dict, expected_keys)
            ("minimal", {"operators": {}}, ["name", "operators"]),
            ("with_settings", {"operators": {}, "settings": {"N": 3}}, ["name", "operators", "settings"]),
            ("complex", {
                "operators": {"AND": {"arity": 2}},
                "settings": {"N": 5, "modal": True},
                "extra_data": [1, 2, 3]
            }, ["name", "operators", "settings", "extra_data"]),
            ("unicode", {"operators": {"∧": {"symbol": "∧"}}}, ["name", "operators"]),
        ]
        
        for name, theory, expected_keys in test_cases:
            with self.subTest(theory_type=name):
                result = serialize_semantic_theory(name, theory)
                
                # Check all expected keys are present
                for key in expected_keys:
                    self.assertIn(key, result, f"Missing key '{key}' in {name} theory")
    
    def test_deserialize_various_formats(self):
        """Test deserialization with various input formats."""
        test_cases = [
            # (serialized_data, expected_name)
            ({"name": "test", "theory": {}}, "test"),
            ({"name": "unicode_名前", "theory": {"data": "値"}}, "unicode_名前"),
            ({"name": "", "theory": {}}, ""),  # Empty name
        ]
        
        for data, expected_name in test_cases:
            with self.subTest(expected_name=expected_name):
                result = deserialize_semantic_theory(data)
                self.assertEqual(result["name"], expected_name)
    
    def test_operator_serialization_varieties(self):
        """Test operator serialization with different operator types."""
        # Create various operator configurations
        operator_cases = [
            # Single operator
            {"AND": MockOperator},
            # Multiple operators
            {"AND": MockOperator, "OR": MockOperatorOr, "NOT": MockOperatorNot},
            # Empty
            {},
        ]
        
        for i, operators in enumerate(operator_cases):
            with self.subTest(case=i, num_operators=len(operators)):
                collection = OperatorCollection()
                for op_class in operators.values():
                    collection.add_operator(op_class)
                
                result = serialize_operators(collection)
                self.assertEqual(len(result), len(operators))
    
    def test_round_trip_preservation(self):
        """Test data integrity through serialization round trips."""
        test_theories = [
            {
                "operators": {
                    "AND": {"module": "test.module", "class_name": "AndOp"},
                    "OR": {"module": "test.module", "class_name": "OrOp"},
                },
                "settings": {"N": 4, "reflexive": True},
                "metadata": {"version": "1.0", "author": "test"},
            },
            {
                "operators": {},
                "complex_data": {
                    "nested": {
                        "deeply": {
                            "value": [1, 2, {"key": "value"}]
                        }
                    }
                }
            },
        ]
        
        for i, original in enumerate(test_theories):
            with self.subTest(case=i):
                # Serialize
                serialized = serialize_semantic_theory(f"theory_{i}", original)
                
                # Deserialize
                deserialized = deserialize_semantic_theory(serialized)
                
                # Check round trip
                self.assertEqual(
                    deserialized["theory"], 
                    original,
                    "Round-trip serialization failed to preserve data"
                )
    
    def test_import_class_various_paths(self):
        """Test import_class with various module paths."""
        test_cases = [
            # Built-in modules
            ("builtins", "dict", dict),
            ("builtins", "list", list),
            # Standard library
            ("unittest.mock", "Mock", MagicMock.__class__.__bases__[0]),  # Get Mock base class
            # Invalid cases should raise
            ("nonexistent.module", "Class", ImportError),
            ("builtins", "NonexistentClass", AttributeError),
        ]
        
        for module, class_name, expected in test_cases:
            with self.subTest(module=module, class_name=class_name):
                if expected in (ImportError, AttributeError):
                    with self.assertRaises(expected):
                        import_class(module, class_name)
                else:
                    result = import_class(module, class_name)
                    # Check it's the right type or related
                    self.assertTrue(
                        result == expected or issubclass(result, expected) or issubclass(expected, result),
                        f"Expected {expected}, got {result}"
                    )
    
    def test_edge_cases(self):
        """Test edge cases in serialization."""
        edge_cases = [
            # Very large number of operators
            {
                "operators": {f"OP_{i}": {"arity": i % 3 + 1} for i in range(100)}
            },
            # Deep nesting
            {
                "deeply": {
                    "nested": {
                        "structure": {
                            "with": {
                                "many": {
                                    "levels": {"value": 42}
                                }
                            }
                        }
                    }
                }
            },
            # Special characters in keys
            {
                "operators": {
                    "op-with-dash": {"valid": True},
                    "op_with_underscore": {"valid": True},
                    "op.with.dots": {"valid": True},
                }
            },
            # Numeric string keys
            {
                "123": "numeric key",
                "456.789": "float-like key",
            },
        ]
        
        for i, theory in enumerate(edge_cases):
            with self.subTest(edge_case=i):
                # Should handle without errors
                serialized = serialize_semantic_theory(f"edge_{i}", theory)
                deserialized = deserialize_semantic_theory(serialized)
                
                # Verify structure preserved
                self.assertEqual(deserialized["theory"], theory)
    
    def test_error_handling(self):
        """Test error handling in serialization functions."""
        # Test deserialize with invalid input
        invalid_inputs = [
            None,
            [],
            "string",
            123,
            {"missing_name": "no name key"},
            {"name": "test"},  # Missing 'theory' key
        ]
        
        for invalid in invalid_inputs:
            with self.subTest(invalid_input=type(invalid)):
                with self.assertRaises((KeyError, TypeError, AttributeError)):
                    deserialize_semantic_theory(invalid)
    
    def test_operator_deserialization_fallback(self):
        """Test operator deserialization with missing classes."""
        # Create serialized operators with non-existent classes
        serialized = {
            "CUSTOM": {
                "module": "nonexistent.module",
                "class_name": "CustomOperator"
            }
        }
        
        with patch('model_checker.builder.serialize.import_class') as mock_import:
            mock_import.side_effect = ImportError("Module not found")
            
            # Should handle gracefully (return None or empty)
            result = deserialize_operators(serialized)
            
            # Depending on implementation, might return empty or with None values
            self.assertIsInstance(result, dict)
    
    def test_unicode_handling(self):
        """Test proper unicode handling throughout serialization."""
        unicode_data = {
            "operators": {
                "∧": {"symbol": "∧", "name": "conjunction"},
                "∨": {"symbol": "∨", "name": "disjunction"},
                "¬": {"symbol": "¬", "name": "negation"},
                "□": {"symbol": "□", "name": "box"},
                "◇": {"symbol": "◇", "name": "diamond"},
            },
            "descriptions": {
                "中文": "Chinese text",
                "日本語": "Japanese text",
                "한국어": "Korean text",
                "Русский": "Russian text",
                "العربية": "Arabic text",
            }
        }
        
        # Test full round trip with unicode
        serialized = serialize_semantic_theory("unicode_test", unicode_data)
        deserialized = deserialize_semantic_theory(serialized)
        
        # All unicode should be preserved
        self.assertEqual(deserialized["theory"], unicode_data)
        
        # Check specific unicode operators
        self.assertIn("∧", deserialized["theory"]["operators"])
        self.assertEqual(
            deserialized["theory"]["descriptions"]["中文"], 
            "Chinese text"
        )
    
    def test_performance_large_data(self):
        """Test serialization performance with large data sets."""
        import time
        
        # Create large theory
        large_theory = {
            "operators": {
                f"OP_{i}": {
                    "arity": i % 5,
                    "properties": [f"prop_{j}" for j in range(10)],
                    "metadata": {"index": i, "squared": i**2}
                }
                for i in range(1000)
            },
            "large_array": list(range(10000)),
            "matrix": [[i*j for j in range(100)] for i in range(100)],
        }
        
        # Time serialization
        start = time.time()
        serialized = serialize_semantic_theory("large", large_theory)
        serialize_time = time.time() - start
        
        # Time deserialization
        start = time.time()
        deserialized = deserialize_semantic_theory(serialized)
        deserialize_time = time.time() - start
        
        # Performance assertions (should be fast even for large data)
        self.assertLess(serialize_time, 1.0, "Serialization too slow for large data")
        self.assertLess(deserialize_time, 1.0, "Deserialization too slow for large data")
        
        # Verify data integrity
        self.assertEqual(len(deserialized["theory"]["operators"]), 1000)
        self.assertEqual(len(deserialized["theory"]["large_array"]), 10000)


class TestSerializationIntegration(unittest.TestCase):
    """Integration tests with real theory classes."""
    
    @patch('model_checker.builder.serialize.import_class')
    def test_real_theory_serialization(self, mock_import):
        """Test serialization with real theory semantics."""
        # Mock the import to return our mock class
        mock_import.return_value = MockSemantics
        
        # Create a theory that references the mock
        theory = {
            "semantic_class": {
                "module": "test.mocks",
                "class_name": "MockSemantics"
            },
            "operators": {},
        }
        
        serialized = serialize_semantic_theory("mock_theory", theory)
        
        # Should include semantic class info
        self.assertIn("semantic_class", serialized["theory"])
        self.assertEqual(
            serialized["theory"]["semantic_class"]["class_name"],
            "MockSemantics"
        )


if __name__ == "__main__":
    unittest.main()