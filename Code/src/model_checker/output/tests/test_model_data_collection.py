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
        self.mock_model.z3_main_world = MagicMock()
        self.mock_model.z3_main_world.as_long.return_value = 1
        
        # Mock semantic methods
        self.mock_model.get_all_N_states = Mock(return_value=[0, 1, 2, 3])
        self.mock_model.is_possible_state = Mock(side_effect=[True, True, True, False])
        # Need more values for is_world_state since it's called multiple times
        self.mock_model.is_world_state = Mock(side_effect=[
            False, True, True, False,  # for _collect_states
            False, True, True, False,  # for _collect_propositions
            False, True, True, False,  # for _collect_relations (checking state1)
            False, True, True, False,  # for _collect_relations (checking state2 for state1=0)
            False, True, True, False,  # for _collect_relations (state2 for state1=1)
            False, True, True, False,  # for _collect_relations (state2 for state1=2)
            False, True, True, False,  # for _collect_relations (state2 for state1=3)
        ])
        
        # Mock propositions
        mock_prop = Mock()
        mock_prop.letter = 'p'
        mock_prop.is_true_at = Mock(return_value=True)
        self.mock_model.syntax.propositions = {'p': mock_prop}
        
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
        # Mock state methods
        self.mock_model.get_all_N_states = Mock(return_value=[0, 1, 2, 3, 4])
        self.mock_model.is_possible_state = Mock(
            side_effect=[True, True, False, True, False]
        )
        self.mock_model.is_world_state = Mock(
            side_effect=[False, True, False, True, False]
        )
        
        states = self.collector._collect_states(self.mock_model)
        
        assert states["possible"] == ["s0", "s1", "s3"]
        assert states["impossible"] == ["s2", "s4"]
        assert states["worlds"] == ["s1", "s3"]
        
    def test_get_evaluation_world(self):
        """Test evaluation world extraction."""
        # Mock main world
        self.mock_model.z3_model_status = True
        self.mock_model.z3_main_world = MagicMock()
        self.mock_model.z3_main_world.as_long.return_value = 2
        
        eval_world = self.collector._get_evaluation_world(self.mock_model)
        assert eval_world == "s2"
        
        # Test no model case
        self.mock_model.z3_model_status = False
        eval_world = self.collector._get_evaluation_world(self.mock_model)
        assert eval_world is None
        
    def test_collect_propositions(self):
        """Test proposition truth value collection."""
        # Mock propositions
        prop_p = Mock()
        prop_p.letter = 'p'
        prop_p.is_true_at = Mock(side_effect=[True, False, True])
        
        prop_q = Mock()
        prop_q.letter = 'q'
        prop_q.is_true_at = Mock(side_effect=[False, False, True])
        
        self.mock_model.syntax.propositions = {'p': prop_p, 'q': prop_q}
        self.mock_model.get_all_N_states = Mock(return_value=[0, 1, 2])
        self.mock_model.is_world_state = Mock(side_effect=[True, True, True])
        
        propositions = self.collector._collect_propositions(self.mock_model)
        
        assert propositions == {
            'p': {'s0': True, 's1': False, 's2': True},
            'q': {'s0': False, 's1': False, 's2': True}
        }
        
    def test_collect_relations(self):
        """Test relation collection for different theories."""
        # Mock for modal logic (R relation)
        self.mock_model.get_all_N_states = Mock(return_value=[0, 1, 2])
        self.mock_model.is_world_state = Mock(return_value=True)
        
        # Mock R relation
        self.mock_model.R = Mock()
        self.mock_model.R.related = Mock(side_effect=[
            True, False, True,  # s0 -> s0, not s0 -> s1, s0 -> s2
            False, True, False,  # not s1 -> s0, s1 -> s1, not s1 -> s2
            True, False, True    # s2 -> s0, not s2 -> s1, s2 -> s2
        ])
        
        relations = self.collector._collect_relations(self.mock_model)
        
        assert "R" in relations
        assert relations["R"] == {
            "s0": ["s0", "s2"],
            "s1": ["s1"],
            "s2": ["s0", "s2"]
        }