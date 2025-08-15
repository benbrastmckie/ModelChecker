"""Tests for core progress functionality."""

import time
import pytest
from model_checker.output.progress import UnifiedProgress
from model_checker.output.progress.core import ProgressBar
from model_checker.output.progress.display import BatchDisplay


class TestUnifiedProgress:
    """Test unified progress tracking."""
    
    def test_single_model_progress(self):
        """Test progress for single model search."""
        # Use batch display to avoid terminal output during tests
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=1, max_time=1.0, display=display)
        
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
        progress = UnifiedProgress(total_models=3, max_time=1.0, display=display)
        
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
        progress = UnifiedProgress(total_models=2, max_time=1.0, display=display)
        
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
        progress = UnifiedProgress(total_models=1, max_time=1.0, display=display)
        
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
        progress = UnifiedProgress(total_models=3, max_time=1.0, display=display)
        
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
        progress = UnifiedProgress(total_models=2, max_time=1.0, display=display)
        
        # Start but don't complete a search
        progress.start_model_search(1)
        progress.model_checked()
        
        # Finish should clean up
        progress.finish()
        
        # Check that the progress bar was stopped
        assert len(progress.model_progress_bars) == 1
        bar = progress.model_progress_bars[0]
        assert not bar.active


class TestProgressBar:
    """Test the base ProgressBar interface."""
    
    def test_abstract_interface(self):
        """Test that ProgressBar defines abstract methods."""
        # ProgressBar can be instantiated but methods raise NotImplementedError
        bar = ProgressBar()
        
        with pytest.raises(NotImplementedError):
            bar.start()
            
        with pytest.raises(NotImplementedError):
            bar.update(50)
            
        with pytest.raises(NotImplementedError):
            bar.complete()
    
    def test_interface_methods_defined(self):
        """Test that interface methods are defined."""
        # Create a minimal concrete implementation
        class MinimalBar(ProgressBar):
            def start(self, total=100, message=""): pass
            def update(self, current, **kwargs): pass
            def complete(self, success=True): pass
        
        bar = MinimalBar()
        
        # All methods should be callable
        bar.start(100, "Test")
        bar.update(50)
        bar.complete(True)
    
    def test_concrete_implementation(self):
        """Test creating a concrete implementation."""
        class ConcreteProgressBar(ProgressBar):
            def __init__(self):
                self.started = False
                self.updated = False
                self.completed = False
                
            def start(self, total=100, message=""):
                self.started = True
                self.total = total
                self.message = message
                
            def update(self, current, **kwargs):
                self.updated = True
                self.current = current
                self.kwargs = kwargs
                
            def complete(self, success=True):
                self.completed = True
                self.success = success
        
        # Test the concrete implementation
        bar = ConcreteProgressBar()
        
        bar.start(50, "Testing")
        assert bar.started
        assert bar.total == 50
        assert bar.message == "Testing"
        
        bar.update(25, extra="data")
        assert bar.updated
        assert bar.current == 25
        assert bar.kwargs == {"extra": "data"}
        
        bar.complete(False)
        assert bar.completed
        assert bar.success is False


class TestUnifiedProgressEdgeCases:
    """Test edge cases and error conditions for UnifiedProgress."""
    
    def test_zero_models(self):
        """Test with zero models requested."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=0, max_time=1.0, display=display)
        
        # Should handle gracefully
        assert progress.total_models == 0
        progress.finish()
    
    def test_custom_start_time(self):
        """Test providing custom start time for synchronization."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=1, max_time=1.0, display=display)
        
        custom_time = time.time() - 5.0  # 5 seconds ago
        progress.start_model_search(1, start_time=custom_time)
        
        # Should use the custom start time
        assert progress.current_search_start == custom_time
        
        # Search time should reflect the custom start
        search_time = progress.get_current_search_time()
        assert search_time >= 5.0
    
    def test_multiple_starts_same_model(self):
        """Test starting search for same model multiple times."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=2, max_time=1.0, display=display)
        
        # Start model 1
        progress.start_model_search(1)
        initial_bars = len(progress.model_progress_bars)
        
        # Start model 1 again - should not create new bar
        progress.start_model_search(1)
        assert len(progress.model_progress_bars) == initial_bars
    
    def test_skipped_count_reset(self):
        """Test that skipped count resets for each search."""
        display = BatchDisplay()
        progress = UnifiedProgress(total_models=3, max_time=1.0, display=display)
        
        # Model 1 with skips
        progress.start_model_search(1)
        progress.model_skipped_isomorphic()
        progress.model_skipped_isomorphic()
        assert progress.current_search_skipped == 2
        progress.complete_model_search(found=True)
        
        # Model 2 should start fresh
        progress.start_model_search(2)
        assert progress.current_search_skipped == 0
        progress.model_skipped_isomorphic()
        assert progress.current_search_skipped == 1
    
    def test_no_display_provided(self):
        """Test default display creation."""
        # Should create TerminalDisplay by default
        progress = UnifiedProgress(total_models=1, max_time=1.0)
        assert progress.display is not None
        from model_checker.output.progress.display import TerminalDisplay
        assert isinstance(progress.display, TerminalDisplay)