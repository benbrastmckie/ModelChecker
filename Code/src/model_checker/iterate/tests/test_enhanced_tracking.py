"""Test enhanced isomorphism tracking and reporting."""

import pytest
from unittest.mock import Mock, patch
from io import StringIO
import sys

from model_checker.iterate.statistics import SearchStatistics, IterationReportGenerator
from model_checker.iterate.iterator import IteratorCore
from model_checker.builder.example import BuildExample


class TestEnhancedTracking:
    """Test enhanced isomorphism tracking features."""
    
    def test_search_statistics_creation(self):
        """Test SearchStatistics data structure."""
        stat = SearchStatistics(
            model_number=2,
            found=True,
            isomorphic_skipped=3,
            models_checked=4,
            search_duration=2.5
        )
        
        assert stat.model_number == 2
        assert stat.found is True
        assert stat.isomorphic_skipped == 3
        assert stat.models_checked == 4
        assert stat.search_duration == 2.5
        assert stat.termination_reason is None
    
    def test_search_statistics_summary_line(self):
        """Test summary line generation."""
        # Test initial model - note this is now handled differently in the report
        stat1 = SearchStatistics(1, True, 0, 1, 0.0)
        assert stat1.summary_line() == "Model 1: Initial model (given)"
        
        # Test found model with skipped
        stat2 = SearchStatistics(2, True, 3, 4, 2.5)
        assert stat2.summary_line() == "Model 2: Found after skipping 3 isomorphic models (2.50s)"
        
        # Test found model with 1 skipped (singular)
        stat3 = SearchStatistics(3, True, 1, 2, 1.2)
        assert stat3.summary_line() == "Model 3: Found after skipping 1 isomorphic model (1.20s)"
        
        # Test not found with timeout
        stat4 = SearchStatistics(4, False, 7, 45, 60.0, "timeout after 60s")
        assert stat4.summary_line() == "Model 4: Not found - timeout after 60s after checking 45 models (60.00s)"
        
        # Test not found with exhaustion
        stat5 = SearchStatistics(5, False, 2, 10, 5.5, "exhausted search space")
        assert stat5.summary_line() == "Model 5: Not found - exhausted search space after checking 10 models (5.50s)"
    
    def test_report_generation(self):
        """Test full report generation."""
        stats = [
            SearchStatistics(2, True, 3, 4, 2.1),
            SearchStatistics(3, True, 1, 2, 0.8),
            SearchStatistics(4, True, 7, 8, 4.4)
        ]
        
        generator = IterationReportGenerator()
        report = generator.generate_report(stats, 4, 8.7)
        
        # Check report structure
        assert "ITERATION REPORT" in report
        assert "    Model 1: Initial model (0.00s)" in report
        assert "    Model 2: Found after skipping 3 isomorphic models (2.10s)" in report
        assert "    Model 3: Found after skipping 1 isomorphic model (0.80s)" in report
        assert "    Model 4: Found after skipping 7 isomorphic models (4.40s)" in report
        assert "Total: 4/4 models found, 11 isomorphic models skipped, 8.70s elapsed" in report
        assert report.endswith("="*40)
    
    def test_partial_report_with_timeout(self):
        """Test report when search times out."""
        stats = [
            SearchStatistics(2, True, 3, 4, 2.1),
            SearchStatistics(3, False, 45, 150, 57.9, "timeout after 60s")
        ]
        
        generator = IterationReportGenerator()
        report = generator.generate_report(stats, 4, 60.0)
        
        assert "    Model 1: Initial model (0.00s)" in report
        assert "    Model 2: Found after skipping 3 isomorphic models (2.10s)" in report
        assert "    Model 3: Not found - timeout after 60s after checking 150 models (57.90s)" in report
        assert "Total: 2/4 models found, 3 isomorphic models skipped, 60.00s elapsed" in report
        assert report.endswith("="*40)
    
    def test_iterator_tracking(self):
        """Test that IteratorCore tracks per-search statistics."""
        # Create a mock BuildExample with required attributes
        mock_example = Mock(spec=BuildExample)
        mock_model_structure = Mock()
        mock_model_structure.z3_model_status = True
        mock_model_structure.z3_model = Mock()
        mock_model_structure.z3_world_states = []  # Mock the states
        mock_model_structure.z3_possible_states = []  # Mock the states
        mock_example.model_structure = mock_model_structure
        mock_example.settings = {"iterate": 3}
        
        # Create iterator
        iterator = IteratorCore(mock_example)
        
        # Check initial tracking attributes
        assert hasattr(iterator, 'search_stats')
        assert hasattr(iterator, 'current_search_skipped')
        assert hasattr(iterator, 'current_search_start')
        assert hasattr(iterator, 'current_search_checked')
        
        assert iterator.search_stats == []
        assert iterator.current_search_skipped == 0
        assert iterator.current_search_checked == 0
    
    # Progress functionality moved to output.progress module - test removed


if __name__ == "__main__":
    pytest.main([__file__, "-v"])