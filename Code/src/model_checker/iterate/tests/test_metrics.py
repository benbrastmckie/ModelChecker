"""Tests for the consolidated metrics module (progress + statistics)."""

import pytest
import time
from unittest.mock import patch
from model_checker.iterate.metrics import IterationStatistics


# IterationProgress tests removed - functionality moved to output.progress module


class TestIterationStatistics:
    """Test cases for IterationStatistics functionality."""
    
    def test_initialization(self):
        """Test statistics initialization."""
        stats = IterationStatistics()
        assert stats.model_stats == []
        assert stats.completion_time is None
    
    def test_add_model_basic(self):
        """Test adding model statistics."""
        stats = IterationStatistics()
        
        # Mock model structure
        model = type('obj', (object,), {
            'z3_world_states': [1, 2, 3],
            'z3_possible_states': [1, 2]
        })()
        
        differences = {
            'world_changes': {'added': [4], 'removed': [1]},
            'possible_changes': {'added': [], 'removed': []}
        }
        
        stats.add_model(model, differences)
        
        assert len(stats.model_stats) == 1
        assert stats.model_stats[0]['world_count'] == 3
        assert stats.model_stats[0]['possible_count'] == 2
        assert stats.model_stats[0]['difference_count'] == 2  # 1 added + 1 removed
    
    def test_count_differences(self):
        """Test difference counting logic."""
        stats = IterationStatistics()
        
        # Test various difference structures
        differences = {
            'world_changes': {'added': [1, 2], 'removed': [3]},
            'possible_changes': {'added': [4], 'removed': []},
            'atomic_changes': {
                'verification_changes': {
                    'atom_a': {'state_1': True, 'state_2': False}
                }
            }
        }
        
        count = stats._count_differences(differences)
        assert count == 5  # 2 added + 1 removed + 1 added + 0 removed + 1 dict (verification_changes)
    
    def test_get_summary(self):
        """Test summary statistics calculation."""
        stats = IterationStatistics()
        
        # Add multiple models
        model1 = type('obj', (object,), {'z3_world_states': [1, 2]})()
        model2 = type('obj', (object,), {'z3_world_states': [1, 2, 3]})()
        model3 = type('obj', (object,), {'z3_world_states': [1, 2]})()
        
        stats.add_model(model1, {})
        stats.add_model(model2, {'world_changes': {'added': [3], 'removed': []}})
        stats.add_model(model3, {'world_changes': {'added': [], 'removed': [3]}})
        
        summary = stats.get_summary()
        
        assert summary['total_models'] == 3
        assert summary['avg_worlds'] == 7/3  # (2 + 3 + 2) / 3
        assert summary['world_diversity'] == 2  # Two different counts: 2 and 3
        assert summary['avg_differences'] == 1.0  # (1 + 1) / 2
        assert summary['max_differences'] == 1
    
    def test_empty_summary(self):
        """Test summary with no models."""
        stats = IterationStatistics()
        summary = stats.get_summary()
        assert summary == {}
    
    def test_set_completion_time(self):
        """Test setting completion time."""
        stats = IterationStatistics()
        stats.set_completion_time(42.5)
        assert stats.completion_time == 42.5
    
    def test_print_summary(self, capsys):
        """Test printing summary statistics."""
        stats = IterationStatistics()
        
        # Add a model
        model = type('obj', (object,), {'z3_world_states': [1, 2]})()
        stats.add_model(model, {})
        stats.set_completion_time(1.23)
        
        stats.print_summary()
        captured = capsys.readouterr()
        
        assert "=== Iteration Statistics ===" in captured.out
        assert "Total models found: 1" in captured.out
        assert "Average worlds per model: 2.0" in captured.out
        assert "Total completion time: 1.23 seconds" in captured.out
    
    def test_print_empty_summary(self, capsys):
        """Test printing empty summary does nothing."""
        stats = IterationStatistics()
        stats.print_summary()
        captured = capsys.readouterr()
        assert captured.out == ""