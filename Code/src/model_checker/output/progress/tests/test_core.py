"""Tests for core progress functionality."""

import time
import pytest
from model_checker.output.progress import UnifiedProgress
from model_checker.output.progress.display import BatchDisplay


class TestUnifiedProgress:
    """Test unified progress tracking."""
    
    def test_single_model_progress(self):
        """Test progress for single model search."""
        # Use batch display to avoid terminal output during tests
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=1, iteration_timeout=1.0, display=display)
        
        progress.start_model_search(1)
        assert progress.current_model == 1
        
        # Simulate checks
        for _ in range(5):
            progress.model_checked()
        assert progress.models_checked == 5
        
        progress.complete_model_search(found=True)
        assert progress.models_found == 1
        
    def test_multiple_model_progress(self):
        """Test progress for multiple model iteration."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=3, iteration_timeout=1.0, display=display)
        
        # Test three model searches
        for i in range(1, 4):
            progress.start_model_search(i)
            progress.model_checked()
            progress.complete_model_search(found=True)
            
        assert progress.models_found == 3
        assert progress.models_checked == 3
        
    def test_isomorphic_tracking(self):
        """Test tracking of isomorphic models."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=2, iteration_timeout=1.0, display=display)
        
        # First model
        progress.start_model_search(1)
        progress.model_checked()
        progress.complete_model_search(found=True)
        
        # Second model with some isomorphic skips
        progress.start_model_search(2)
        progress.model_checked()
        progress.model_skipped_isomorphic()
        progress.model_checked()
        progress.model_skipped_isomorphic()
        progress.model_checked()
        progress.complete_model_search(found=True)
        
        assert progress.models_found == 2
        assert progress.models_checked == 4  # 1 + 3
        assert progress.isomorphic_skipped == 2
        
    def test_timing_tracking(self):
        """Test elapsed time tracking."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=1, iteration_timeout=1.0, display=display)
        
        # Should be 0 before start
        assert progress.get_elapsed_time() == 0.0
        assert progress.get_current_search_time() == 0.0
        
        progress.start_model_search(1)
        time.sleep(0.1)  # Small delay
        
        # Should have some elapsed time
        assert progress.get_elapsed_time() > 0.0
        assert progress.get_current_search_time() > 0.0
        
        progress.complete_model_search(found=True)
        
    def test_not_found_tracking(self):
        """Test progress when models are not found."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=3, iteration_timeout=1.0, display=display)
        
        # First model found
        progress.start_model_search(1)
        progress.model_checked()
        progress.complete_model_search(found=True)
        
        # Second model not found
        progress.start_model_search(2)
        progress.model_checked()
        progress.model_checked()
        progress.complete_model_search(found=False)
        
        # Third model found
        progress.start_model_search(3)
        progress.model_checked()
        progress.complete_model_search(found=True)
        
        assert progress.models_found == 2  # Only 2 found
        assert len(progress.model_progress_bars) == 3  # But tried 3
        
    def test_finish_cleanup(self):
        """Test that finish properly cleans up."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=2, iteration_timeout=1.0, display=display)
        
        # Start but don't complete a search
        progress.start_model_search(1)
        progress.model_checked()
        
        # Finish should clean up
        progress.finish()
        
        # Check that the progress bar was stopped
        assert len(progress.model_progress_bars) == 1
        bar = progress.model_progress_bars[0]
        assert not bar.active