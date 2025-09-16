"""Tests for JSON serialization in the output module."""

import json
import os
import tempfile
import shutil
import pytest
from model_checker.output.formatters import JSONFormatter


class TestJSONSerialization:
    """Test JSON serialization functionality."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        self.formatter = JSONFormatter()
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    def test_save_models_json_structure(self):
        """Test JSON formatting has correct structure."""
        # Create test model data
        model1 = {
            "example": "test1",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s1",
            "states": {
                "possible": ["s0", "s1", "s2"],
                "impossible": ["s3"],
                "worlds": ["s1", "s2"]
            },
            "relations": {"R": {"s1": ["s1", "s2"], "s2": ["s1"]}},
            "propositions": {"p": {"s1": True, "s2": False}}
        }
        
        # Format as JSON
        json_str = self.formatter.format_example(model1, "Test output")
        
        # Parse and verify structure
        data = json.loads(json_str)
        
        assert data['example'] == 'test1'
        assert data['theory'] == 'logos'
        assert data['has_model'] is True
        assert data['output'] == 'Test output'
        assert 'states' in data
        assert 'relations' in data
        
    def test_json_formatting(self):
        """Test JSON is properly formatted."""
        model = {
            "example": "format_test",
            "special_chars": "Test with \"quotes\" and \nnewlines",
            "unicode": "Test with unicode: λ φ ∧ ∨"
        }
        
        json_str = self.formatter.format_example(model, "")
        data = json.loads(json_str)
        
        # Check proper escaping and formatting
        assert data['special_chars'] == 'Test with "quotes" and \nnewlines'
        assert data['unicode'] == 'Test with unicode: λ φ ∧ ∨'
        
    def test_empty_models_json(self):
        """Test JSON formatting with empty data."""
        # Empty model
        model = {}
        json_str = self.formatter.format_example(model, "")
        data = json.loads(json_str)
        
        # Should be valid JSON even if empty
        assert isinstance(data, dict)
        
    def test_json_encoding(self):
        """Test JSON encoding options."""
        model = {
            "example": "encoding_test",
            "complex_data": {
                "nested": {
                    "arrays": [1, 2, [3, 4]],
                    "objects": {"a": 1, "b": {"c": 2}}
                }
            }
        }
        
        json_str = self.formatter.format_example(model, "")
        
        # Check file is valid JSON
        data = json.loads(json_str)  # Should not raise
        
        # Check structure preserved
        nested = data['complex_data']['nested']
        assert nested['arrays'] == [1, 2, [3, 4]]
        assert nested['objects']['b']['c'] == 2
    
    def test_batch_formatting(self):
        """Test batch formatting of multiple examples."""
        # Create individual JSON strings
        example1 = json.dumps({"example": "test1", "value": 1})
        example2 = json.dumps({"example": "test2", "value": 2})
        
        # Format as batch
        batch_json = self.formatter.format_batch([example1, example2])
        
        # Parse and verify
        data = json.loads(batch_json)
        assert 'models' in data
        assert 'metadata' in data
        assert len(data['models']) == 2
        assert data['models'][0]['example'] == 'test1'
        assert data['models'][1]['value'] == 2
    
    def test_json_formatter_indentation(self):
        """Test JSON formatter respects indentation setting."""
        formatter_custom = JSONFormatter(indent=2)
        
        model = {"example": "indent_test", "nested": {"value": 42}}
        json_str = formatter_custom.format_example(model, "")
        
        # Check indentation in output
        lines = json_str.split('\n')
        # Second level should have 2 spaces
        nested_line = [l for l in lines if '"nested"' in l][0]
        assert nested_line.startswith('  ')  # 2 spaces
    
    def test_ensure_ascii_option(self):
        """Test ensure_ascii option for JSON formatting."""
        formatter_ascii = JSONFormatter(ensure_ascii=True)
        
        model = {"example": "ascii_test", "unicode": "λ"}
        json_str = formatter_ascii.format_example(model, "")
        
        # Unicode should be escaped
        assert 'λ' not in json_str
        assert '\\u' in json_str
        
        # But should decode properly
        data = json.loads(json_str)
        assert data['unicode'] == 'λ'