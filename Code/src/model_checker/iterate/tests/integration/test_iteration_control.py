"""Tests for the consolidated iteration control module (termination + formatting)."""

import pytest
import time
from unittest.mock import Mock, patch
from model_checker.iterate.metrics import TerminationManager, ResultFormatter, IterationStatistics


class TestTerminationManager:
    """Test cases for TerminationManager functionality."""
    
    def test_initialization(self):
        """Test termination manager initialization."""
        settings = {'max_time': 120, 'max_consecutive_invalid': 10}
        manager = TerminationManager(settings)
        
        assert manager.timeout == 120
        assert manager.max_consecutive_invalid == 10
        assert manager.start_time is None
    
    def test_start_timing(self):
        """Test starting the iteration timer."""
        manager = TerminationManager({})
        manager.start_timing()
        
        assert manager.start_time is not None
        assert isinstance(manager.start_time, float)
    
    def test_should_terminate_max_iterations(self):
        """Test termination when max iterations reached."""
        manager = TerminationManager({})
        
        should_stop, reason = manager.should_terminate(
            current_iteration=5,
            max_iterations=5,
            consecutive_invalid_count=0,
            checked_model_count=5
        )
        
        assert should_stop is True
        assert "Found all 5 requested models" in reason
    
    def test_should_terminate_timeout(self):
        """Test that global timeout check is disabled (handled per-model now)."""
        manager = TerminationManager({'max_time': 0.1})
        manager.start_timing()
        
        # Wait for what would have been a timeout
        time.sleep(0.15)
        
        should_stop, reason = manager.should_terminate(
            current_iteration=1,
            max_iterations=10,
            consecutive_invalid_count=0,
            checked_model_count=1
        )
        
        # Timeout is now handled per-model, not globally
        assert should_stop is False
        assert reason == ""
    
    def test_should_terminate_consecutive_invalid(self):
        """Test termination on too many invalid models."""
        manager = TerminationManager({'max_consecutive_invalid': 3})
        
        should_stop, reason = manager.should_terminate(
            current_iteration=1,
            max_iterations=10,
            consecutive_invalid_count=3,
            checked_model_count=5
        )
        
        assert should_stop is True
        assert "Too many consecutive invalid models (3)" in reason
    
    def test_should_terminate_lack_of_progress(self):
        """Test termination due to lack of progress."""
        manager = TerminationManager({})
        manager.start_timing()
        
        # Simulate checking many models but finding few
        should_stop, reason = manager.should_terminate(
            current_iteration=1,
            max_iterations=10,
            consecutive_invalid_count=0,
            checked_model_count=101  # Checked 101 (>100) but only found 1 (<5)
        )
        
        assert should_stop is True
        assert "Insufficient progress" in reason
    
    def test_should_not_terminate(self):
        """Test normal operation without termination."""
        manager = TerminationManager({})
        
        should_stop, reason = manager.should_terminate(
            current_iteration=2,
            max_iterations=5,
            consecutive_invalid_count=1,
            checked_model_count=3
        )
        
        assert should_stop is False
        assert reason == ""
    
    def test_get_elapsed_time(self):
        """Test elapsed time calculation."""
        manager = TerminationManager({})
        
        # Before starting
        assert manager.get_elapsed_time() == 0.0
        
        # After starting
        manager.start_timing()
        time.sleep(0.1)
        elapsed = manager.get_elapsed_time()
        
        assert elapsed > 0.1
        assert elapsed < 0.2
    
    def test_should_attempt_escape(self):
        """Test escape attempt logic."""
        manager = TerminationManager({})
        
        assert manager.should_attempt_escape(2) is False
        assert manager.should_attempt_escape(3) is True
        assert manager.should_attempt_escape(5) is True
    
    def test_get_progress_ratio(self):
        """Test progress ratio calculation."""
        manager = TerminationManager({})
        
        assert manager.get_progress_ratio(0, 10) == 0.0
        assert manager.get_progress_ratio(5, 10) == 0.5
        assert manager.get_progress_ratio(10, 10) == 1.0
        assert manager.get_progress_ratio(15, 10) == 1.0  # Capped at 1.0
        assert manager.get_progress_ratio(5, 0) == 0.0  # Handle division by zero


class TestResultFormatter:
    """Test cases for ResultFormatter functionality."""
    
    def test_format_iteration_summary(self):
        """Test formatting iteration summary."""
        formatter = ResultFormatter()
        
        # Mock structures
        model_structures = [Mock(), Mock(), Mock()]
        
        # Mock statistics
        statistics = Mock()
        statistics.get_summary.return_value = {
            'total_checked': 5,
            'success_rate': 0.6,
            'average_model_time': 0.123
        }
        
        summary = formatter.format_iteration_summary(model_structures, statistics, 2.5)
        
        assert "ITERATION SUMMARY" in summary
        assert "Models found: 3" in summary
        assert "Total time: 2.50 seconds" in summary
        assert "Models checked: 5" in summary
        assert "Success rate: 60.0%" in summary
        assert "Average time per model: 0.123s" in summary
    
    def test_format_difference_report(self):
        """Test formatting difference report."""
        formatter = ResultFormatter()
        
        differences = {
            'world_changes': {
                'added': [1, 2],
                'removed': [3]
            },
            'possible_changes': {
                'added': [4],
                'removed': [5, 6]
            }
        }
        
        report = formatter.format_difference_report(differences)
        
        assert "=== DIFFERENCES FROM PREVIOUS MODEL ===" in report
        assert "World Changes:" in report
        assert "+ State 1 (now a world)" in report
        assert "+ State 2 (now a world)" in report
        assert "- State 3 (no longer a world)" in report
        assert "Possible State Changes:" in report
        assert "+ State 4 (now possible)" in report
        assert "- State 5 (now impossible)" in report
        assert "- State 6 (now impossible)" in report
    
    def test_format_empty_difference_report(self):
        """Test formatting report with no differences."""
        formatter = ResultFormatter()
        
        report = formatter.format_difference_report({})
        
        assert "=== DIFFERENCES FROM PREVIOUS MODEL ===" in report
        assert "No significant differences detected." in report
    
    def test_format_progress_update(self):
        """Test formatting progress update."""
        formatter = ResultFormatter()
        
        update = formatter.format_progress_update(3, 5, 7, 1.5)
        
        assert "Finding 5 models:" in update
        assert "[[████████████░░░░░░░░]]" in update  # Progress bar with double brackets
        assert "3/5" in update
        assert "checked 7" in update  # No parentheses
        assert "1.5s" in update
    
    def test_create_progress_bar(self):
        """Test progress bar creation."""
        formatter = ResultFormatter()
        
        # Test various progress levels
        assert formatter._create_progress_bar(0, 10, 10) == "[░░░░░░░░░░]"
        assert formatter._create_progress_bar(5, 10, 10) == "[█████░░░░░]"
        assert formatter._create_progress_bar(10, 10, 10) == "[██████████]"
        
        # Test edge cases
        assert formatter._create_progress_bar(0, 0, 10) == "░░░░░░░░░░"  # No brackets when total is 0
        assert formatter._create_progress_bar(5, 10, 5) == "[██░░░]"  # Smaller width