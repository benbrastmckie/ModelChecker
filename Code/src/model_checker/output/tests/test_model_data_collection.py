"""Tests for model data collection and extraction."""

import pytest
from unittest.mock import Mock, MagicMock

from model_checker.output.collectors import ModelDataCollector


class TestModelDataCollection:
    """Test extraction of model data from model structures."""
    
    def setup_method(self):
        """Create mock model structure for testing."""
        self.mock_model = Mock()
        self.collector = ModelDataCollector()
        
    def test_collect_model_data_with_model(self):
        """Test collecting data when model exists."""
        # Mock a model structure with a found model
        self.mock_model.z3_model_status = True
        
        # Mock extraction methods
        self.mock_model.extract_evaluation_world = Mock(return_value="s1")
        self.mock_model.extract_states = Mock(return_value={
            "worlds": ["s1", "s2"],
            "possible": ["s0", "s1", "s2"],
            "impossible": ["s3"]
        })
        self.mock_model.extract_relations = Mock(return_value={
            "R": {"s0": ["s1"], "s1": ["s1", "s2"]}
        })
        self.mock_model.extract_propositions = Mock(return_value={
            "p": {"s0": True, "s1": False}
        })
        
        # Collect data
        data = self.collector.collect_model_data(
            self.mock_model, 
            "example1",
            "logos"
        )
        
        # Verify structure
        assert data["example"] == "example1"
        assert data["theory"] == "logos"
        assert data["has_model"] is True
        assert data["evaluation_world"] == "s1"
        assert "states" in data
        assert "propositions" in data
        
    def test_collect_model_data_no_model(self):
        """Test collecting data when no model found."""
        # Mock no model found
        self.mock_model.z3_model_status = False
        self.mock_model.z3_model = None
        
        data = self.collector.collect_model_data(
            self.mock_model,
            "example2", 
            "bimodal"
        )
        
        assert data["example"] == "example2"
        assert data["theory"] == "bimodal"
        assert data["has_model"] is False
        assert data["evaluation_world"] is None
        assert data["states"] == {"possible": [], "impossible": [], "worlds": []}
        
    def test_collect_states(self):
        """Test state classification collection."""
        # Mock extract_states method
        self.mock_model.extract_states = Mock(return_value={
            "possible": ["s0", "s1", "s3"],
            "impossible": ["s2", "s4"],
            "worlds": ["s1", "s3"]
        })
        
        states = self.collector._collect_states(self.mock_model)
        
        assert states["possible"] == ["s0", "s1", "s3"]
        assert states["impossible"] == ["s2", "s4"]
        assert states["worlds"] == ["s1", "s3"]
        
    def test_get_evaluation_world(self):
        """Test evaluation world extraction."""
        # Mock extract_evaluation_world method
        self.mock_model.extract_evaluation_world = Mock(return_value="s2")
        
        eval_world = self.collector._get_evaluation_world(self.mock_model)
        assert eval_world == "s2"
        
        # Test model without extraction method
        del self.mock_model.extract_evaluation_world
        eval_world = self.collector._get_evaluation_world(self.mock_model)
        assert eval_world is None
        
    def test_collect_propositions(self):
        """Test proposition truth value collection."""
        # Mock extract_propositions method
        self.mock_model.extract_propositions = Mock(return_value={
            'p': {'s0': True, 's1': False, 's2': True},
            'q': {'s0': False, 's1': False, 's2': True}
        })
        
        propositions = self.collector._collect_propositions(self.mock_model)
        
        assert propositions == {
            'p': {'s0': True, 's1': False, 's2': True},
            'q': {'s0': False, 's1': False, 's2': True}
        }
        
    def test_collect_relations(self):
        """Test relation collection for different theories."""
        # Mock extract_relations method
        self.mock_model.extract_relations = Mock(return_value={
            "R": {
                "s0": ["s0", "s2"],
                "s1": ["s1"],
                "s2": ["s0", "s2"]
            }
        })
        
        relations = self.collector._collect_relations(self.mock_model)
        
        assert "R" in relations
        assert relations["R"] == {
            "s0": ["s0", "s2"],
            "s1": ["s1"],
            "s2": ["s0", "s2"]
        }