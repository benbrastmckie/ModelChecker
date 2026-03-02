"""Unit tests for jupyter adapters module."""

import unittest
from unittest.mock import MagicMock, patch
from model_checker.jupyter.adapters import (
    TheoryAdapter, 
    get_theory_adapter,
    DefaultTheoryAdapter,
    ExclusionTheoryAdapter,
    ImpositionTheoryAdapter,
    BimodalTheoryAdapter
)


class TestTheoryAdapter(unittest.TestCase):
    """Test TheoryAdapter base class."""
    
    def test_initialization(self):
        """Test adapter initialization."""
        adapter = TheoryAdapter("test_theory")
        self.assertEqual(adapter.theory_name, "test_theory")
    
    def test_model_to_graph_not_implemented(self):
        """Test model_to_graph raises NotImplementedError."""
        adapter = TheoryAdapter("test")
        with self.assertRaises(NotImplementedError):
            adapter.model_to_graph(MagicMock())
    
    def test_format_formula_not_implemented(self):
        """Test format_formula raises NotImplementedError."""
        adapter = TheoryAdapter("test")
        with self.assertRaises(NotImplementedError):
            adapter.format_formula("p -> q")
    
    def test_format_model_not_implemented(self):
        """Test format_model raises NotImplementedError."""
        adapter = TheoryAdapter("test")
        with self.assertRaises(NotImplementedError):
            adapter.format_model(MagicMock())


class TestGetTheoryAdapter(unittest.TestCase):
    """Test get_theory_adapter factory function."""
    
    def test_get_logos_adapter(self):
        """Test getting logos adapter returns DefaultTheoryAdapter."""
        adapter = get_theory_adapter("logos")
        self.assertIsInstance(adapter, DefaultTheoryAdapter)
        self.assertEqual(adapter.theory_name, "logos")
    
    def test_get_exclusion_adapter(self):
        """Test getting exclusion adapter."""
        adapter = get_theory_adapter("exclusion")
        self.assertIsInstance(adapter, ExclusionTheoryAdapter)
        self.assertEqual(adapter.theory_name, "exclusion")
    
    def test_get_imposition_adapter(self):
        """Test getting imposition adapter."""
        adapter = get_theory_adapter("imposition")
        self.assertIsInstance(adapter, ImpositionTheoryAdapter)
        self.assertEqual(adapter.theory_name, "imposition")
    
    def test_get_bimodal_adapter(self):
        """Test getting bimodal adapter."""
        adapter = get_theory_adapter("bimodal")
        self.assertIsInstance(adapter, BimodalTheoryAdapter)
        self.assertEqual(adapter.theory_name, "bimodal")
    
    def test_get_unknown_adapter_returns_default(self):
        """Test unknown theory returns DefaultTheoryAdapter."""
        adapter = get_theory_adapter("unknown_theory")
        self.assertIsInstance(adapter, DefaultTheoryAdapter)
        self.assertEqual(adapter.theory_name, "unknown_theory")


class TestDefaultTheoryAdapter(unittest.TestCase):
    """Test DefaultTheoryAdapter class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.adapter = DefaultTheoryAdapter("default")
    
    def test_model_to_graph(self):
        """Test model to graph conversion."""
        # Mock model structure
        mock_model = MagicMock()
        mock_model.z3_world_states = [MagicMock(), MagicMock()]
        mock_model.N = 3
        mock_model.main_point = {"world": MagicMock()}
        mock_model.semantics.bitvec_to_substates = MagicMock(return_value="state_str")
        
        # Test conversion - should return a graph object
        result = self.adapter.model_to_graph(mock_model)
        
        # Verify a graph is returned (will be networkx DiGraph)
        self.assertIsNotNone(result)
    
    def test_format_formula(self):
        """Test formula formatting."""
        with patch('model_checker.jupyter.unicode.normalize_formula') as mock_normalize:
            with patch('model_checker.jupyter.utils.sanitize_formula') as mock_sanitize:
                mock_normalize.return_value = "normalized"
                mock_sanitize.return_value = "sanitized"
                
                result = self.adapter.format_formula("p -> q")
                
                mock_normalize.assert_called_once_with("p -> q", format_type="unicode")
                mock_sanitize.assert_called_once_with("normalized")
                self.assertEqual(result, "sanitized")
    
    def test_format_model(self):
        """Test model formatting."""
        mock_model = MagicMock()
        mock_model.model_structure.N = 3
        mock_model.model_structure.main_point = {"world": "w1"}
        mock_model.example_settings = {"N": 3, "max_time": 5}
        
        result = self.adapter.format_model(mock_model)
        
        self.assertIn("<h4>Default Theory Model</h4>", result)
        self.assertIn("Atomic States:", result)


class TestExclusionTheoryAdapter(unittest.TestCase):
    """Test ExclusionTheoryAdapter class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.adapter = ExclusionTheoryAdapter("exclusion")
    
    def test_model_to_graph_uses_default(self):
        """Test model_to_graph delegates to DefaultTheoryAdapter."""
        mock_model = MagicMock()
        
        with patch.object(DefaultTheoryAdapter, 'model_to_graph') as mock_method:
            mock_method.return_value = "graph"
            result = self.adapter.model_to_graph(mock_model)
            self.assertEqual(result, "graph")
    
    def test_format_formula(self):
        """Test formula formatting for exclusion theory."""
        with patch('model_checker.jupyter.unicode.normalize_formula') as mock_normalize:
            with patch('model_checker.jupyter.utils.sanitize_formula') as mock_sanitize:
                mock_normalize.return_value = "normalized"
                mock_sanitize.return_value = "sanitized"
                
                result = self.adapter.format_formula("p ⊓ q")
                
                self.assertEqual(result, "sanitized")
    
    def test_format_model(self):
        """Test model formatting for exclusion theory."""
        mock_model = MagicMock()
        mock_model.model_structure.N = 3
        mock_model.example_settings = {"N": 3}
        
        result = self.adapter.format_model(mock_model)
        
        self.assertIn("<h4>Exclusion Theory Model</h4>", result)
        self.assertIn("Atomic States:", result)


class TestImpositionTheoryAdapter(unittest.TestCase):
    """Test ImpositionTheoryAdapter class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.adapter = ImpositionTheoryAdapter("imposition")
    
    def test_inherits_properly(self):
        """Test proper inheritance from TheoryAdapter."""
        self.assertIsInstance(self.adapter, TheoryAdapter)
        self.assertEqual(self.adapter.theory_name, "imposition")
    
    def test_model_to_graph_uses_default(self):
        """Test model_to_graph delegates to DefaultTheoryAdapter."""
        mock_model = MagicMock()
        
        with patch.object(DefaultTheoryAdapter, 'model_to_graph') as mock_method:
            mock_method.return_value = "graph"
            result = self.adapter.model_to_graph(mock_model)
            self.assertEqual(result, "graph")


class TestBimodalTheoryAdapter(unittest.TestCase):
    """Test BimodalTheoryAdapter class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.adapter = BimodalTheoryAdapter("bimodal")
    
    def test_inherits_properly(self):
        """Test proper inheritance from TheoryAdapter."""
        self.assertIsInstance(self.adapter, TheoryAdapter)
        self.assertEqual(self.adapter.theory_name, "bimodal")
    
    def test_model_to_graph_uses_default(self):
        """Test model_to_graph delegates to DefaultTheoryAdapter."""
        mock_model = MagicMock()
        
        with patch.object(DefaultTheoryAdapter, 'model_to_graph') as mock_method:
            mock_method.return_value = "graph"
            result = self.adapter.model_to_graph(mock_model)
            self.assertEqual(result, "graph")


if __name__ == '__main__':
    unittest.main()