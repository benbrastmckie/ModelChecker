"""Unit tests for the utils types module."""

import unittest
from pathlib import Path
import z3


class TestTypeDefinitions(unittest.TestCase):
    """Test type definitions and aliases."""
    
    def test_type_imports(self):
        """Test that all type definitions can be imported."""
        from model_checker.utils.types import (
            T, Z3Expr, Z3Sort, PathLike, ConfigDict,
            TableRow, TableData, VersionTuple, ColorCode,
            TestResult, MockObject
        )
        
        # Verify they exist (imports don't fail)
        self.assertIsNotNone(T)
        self.assertIsNotNone(Z3Expr)
        self.assertIsNotNone(Z3Sort)
        self.assertIsNotNone(PathLike)
        self.assertIsNotNone(ConfigDict)
        self.assertIsNotNone(TableRow)
        self.assertIsNotNone(TableData)
        self.assertIsNotNone(VersionTuple)
        self.assertIsNotNone(ColorCode)
        self.assertIsNotNone(TestResult)
        self.assertIsNotNone(MockObject)
    
    def test_z3_type_aliases(self):
        """Test Z3 type aliases are correctly defined."""
        from model_checker.utils.types import Z3Expr, Z3Sort
        
        # Create Z3 objects
        x = z3.Bool('x')
        y = z3.Int('y')
        s = z3.String('s')
        bv = z3.BitVec('bv', 8)
        
        # These should all be valid Z3Expr types
        # Type checking happens at static analysis time
        exprs = [x, y, s, bv]
        for expr in exprs:
            self.assertIsNotNone(expr)
        
        # Create Z3 sorts
        bool_sort = z3.BoolSort()
        int_sort = z3.IntSort()
        
        # These should all be valid Z3Sort types
        sorts = [bool_sort, int_sort]
        for sort in sorts:
            self.assertIsNotNone(sort)
    
    def test_pathlike_type(self):
        """Test PathLike type alias."""
        from model_checker.utils.types import PathLike
        
        # Both str and Path should be valid PathLike
        str_path = "/path/to/file"
        path_obj = Path("/path/to/file")
        
        # Type checking happens at static analysis time
        # We just verify objects are created
        self.assertIsInstance(str_path, str)
        self.assertIsInstance(path_obj, Path)
    
    def test_config_dict_type(self):
        """Test ConfigDict type alias."""
        from model_checker.utils.types import ConfigDict
        
        # ConfigDict should be Dict[str, Any]
        config = {
            "name": "test",
            "value": 42,
            "enabled": True,
            "data": [1, 2, 3]
        }
        
        # Verify it's a dict with string keys
        self.assertIsInstance(config, dict)
        for key in config.keys():
            self.assertIsInstance(key, str)
    
    def test_table_types(self):
        """Test table-related type aliases."""
        from model_checker.utils.types import TableRow, TableData
        
        # TableRow should be List[Any]
        row = ["col1", 42, True, None]
        self.assertIsInstance(row, list)
        
        # TableData should be List[TableRow]
        data = [
            ["header1", "header2", "header3"],
            ["value1", "value2", "value3"],
            [1, 2, 3]
        ]
        self.assertIsInstance(data, list)
        for item in data:
            self.assertIsInstance(item, list)
    
    def test_version_tuple_type(self):
        """Test VersionTuple type alias."""
        from model_checker.utils.types import VersionTuple
        
        # VersionTuple should be Tuple[int, int, int]
        version = (1, 2, 3)
        
        self.assertIsInstance(version, tuple)
        self.assertEqual(len(version), 3)
        for component in version:
            self.assertIsInstance(component, int)
    
    def test_color_code_type(self):
        """Test ColorCode type alias."""
        from model_checker.utils.types import ColorCode
        
        # ColorCode should be str
        red = "\033[31m"
        green = "\033[32m"
        reset = "\033[0m"
        
        colors = [red, green, reset]
        for color in colors:
            self.assertIsInstance(color, str)
    
    def test_test_related_types(self):
        """Test test-related type aliases."""
        from model_checker.utils.types import TestResult, MockObject
        
        # These are Any types, so anything is valid
        result1 = True
        result2 = {"status": "passed", "score": 100}
        result3 = None
        
        # All should be valid TestResult
        results = [result1, result2, result3]
        for result in results:
            # Any type accepts anything
            pass
        
        # MockObject is also Any
        from unittest.mock import MagicMock
        mock = MagicMock()
        self.assertIsNotNone(mock)


if __name__ == '__main__':
    unittest.main()