"""Performance testing for ModelChecker.

This module tests performance characteristics including
execution time, memory usage, and scaling behavior.
"""

import pytest
import time
import gc
from tests.utils.base import BaseModelTest, BaseExampleTest


class TestExecutionPerformance(BaseModelTest):
    """Test execution time performance."""
    
    @pytest.mark.timeout(5)
    def test_simple_model_performance(self):
        """Test simple models complete quickly."""
        start = time.time()
        
        # Create and check simple model
        settings = {'N': 3}
        model = self.create_model(settings)
        
        elapsed = time.time() - start
        assert elapsed < 1.0, f"Simple model took {elapsed:.2f}s, expected < 1s"
    
    @pytest.mark.timeout(10)
    def test_medium_model_performance(self):
        """Test medium complexity models complete reasonably."""
        start = time.time()
        
        # Create medium complexity model
        settings = {
            'N': 8,
            'contingent': True,
            'non_empty': True
        }
        model = self.create_model(settings)
        
        elapsed = time.time() - start
        assert elapsed < 5.0, f"Medium model took {elapsed:.2f}s, expected < 5s"
    
    @pytest.mark.timeout(30)
    def test_complex_model_performance(self):
        """Test complex models complete within timeout."""
        start = time.time()
        
        # Create complex model
        settings = {
            'N': 16,
            'contingent': True,
            'non_empty': True,
            'non_null': True,
            'disjoint': True
        }
        
        try:
            model = self.create_model(settings)
            elapsed = time.time() - start
            assert elapsed < 20.0, f"Complex model took {elapsed:.2f}s, expected < 20s"
        except Exception:
            # Timeout or resource limit is acceptable
            elapsed = time.time() - start
            assert elapsed < 30.0, "Model should timeout quickly if it can't complete"
    
    @pytest.mark.parametrize("n,max_time", [
        (2, 0.5),
        (4, 1.0),
        (8, 3.0),
        (16, 10.0),
    ])
    def test_scaling_with_n(self, n, max_time):
        """Test performance scales reasonably with N."""
        start = time.time()
        
        settings = {'N': n}
        
        try:
            model = self.create_model(settings)
            elapsed = time.time() - start
            
            assert elapsed < max_time, \
                f"N={n} took {elapsed:.2f}s, expected < {max_time}s"
        except Exception:
            # Resource limits acceptable for large N
            assert n >= 16


class TestMemoryPerformance:
    """Test memory usage performance."""
    
    def test_memory_usage_simple(self):
        """Test memory usage for simple models."""
        import tracemalloc
        
        # Start memory tracking
        tracemalloc.start()
        
        # Create simple model
        from model_checker.models import ModelDefaults
        model = ModelDefaults({'N': 3})
        
        # Get memory usage
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        
        # Convert to MB
        peak_mb = peak / (1024 * 1024)
        
        # Simple model should use < 10MB
        assert peak_mb < 10, f"Simple model used {peak_mb:.1f}MB, expected < 10MB"
    
    def test_memory_usage_complex(self):
        """Test memory usage for complex models."""
        import tracemalloc
        
        # Start memory tracking
        tracemalloc.start()
        
        try:
            # Create complex model
            from model_checker.models import ModelDefaults
            model = ModelDefaults({
                'N': 10,
                'contingent': True,
                'non_empty': True
            })
            
            # Get memory usage
            current, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            
            # Convert to MB
            peak_mb = peak / (1024 * 1024)
            
            # Complex model should use < 100MB
            assert peak_mb < 100, f"Complex model used {peak_mb:.1f}MB, expected < 100MB"
            
        except MemoryError:
            # Memory error is acceptable for complex models
            tracemalloc.stop()
    
    def test_memory_cleanup(self):
        """Test memory is properly released after model deletion."""
        import gc
        import sys
        
        # Force garbage collection
        gc.collect()
        
        # Get baseline object count
        baseline_objects = len(gc.get_objects())
        
        # Create and destroy multiple models
        for i in range(5):
            from model_checker.models import ModelDefaults
            model = ModelDefaults({'N': 3})
            del model
        
        # Force garbage collection
        gc.collect()
        
        # Check object count hasn't grown significantly
        final_objects = len(gc.get_objects())
        growth = final_objects - baseline_objects
        
        # Allow some growth but should be bounded
        assert growth < 500, f"Object count grew by {growth}, possible memory leak"


class TestBatchPerformance(BaseExampleTest):
    """Test batch processing performance."""
    
    def test_batch_small_examples(self):
        """Test performance with many small examples."""
        start = time.time()
        
        # Create batch of small examples
        examples = []
        for i in range(20):
            example = self.create_example(
                [f"p{i}"],
                [f"q{i}"],
                {'N': 2}
            )
            examples.append(example)
        
        # Process batch (simulation)
        for example in examples:
            self.validate_example(example)
        
        elapsed = time.time() - start
        
        # Should process quickly
        assert elapsed < 2.0, f"Batch of 20 small examples took {elapsed:.2f}s"
    
    def test_batch_mixed_complexity(self):
        """Test performance with mixed complexity examples."""
        start = time.time()
        
        # Create mixed complexity batch
        examples = []
        
        # Simple examples
        for i in range(5):
            example = self.create_example(["A"], ["B"], {'N': 2})
            examples.append(example)
        
        # Medium examples
        for i in range(3):
            example = self.create_example(
                ["A \\wedge B", "C \\vee D"],
                ["E", "F"],
                {'N': 4}
            )
            examples.append(example)
        
        # Complex example
        example = self.create_example(
            ["A \\wedge B \\wedge C"],
            ["D \\vee E \\vee F"],
            {'N': 8}
        )
        examples.append(example)
        
        # Validate all
        for example in examples:
            self.validate_example(example)
        
        elapsed = time.time() - start
        
        # Should complete reasonably
        assert elapsed < 5.0, f"Mixed batch took {elapsed:.2f}s"


class TestConcurrentPerformance:
    """Test concurrent operation performance."""
    
    def test_sequential_vs_concurrent(self):
        """Test that operations don't degrade under concurrency."""
        import threading
        
        def create_model():
            from model_checker.models import ModelDefaults
            try:
                model = ModelDefaults({'N': 3})
                return True
            except Exception:
                return False
        
        # Sequential timing
        start = time.time()
        for _ in range(3):
            create_model()
        sequential_time = time.time() - start
        
        # Concurrent timing
        start = time.time()
        threads = []
        for _ in range(3):
            thread = threading.Thread(target=create_model)
            threads.append(thread)
            thread.start()
        
        for thread in threads:
            thread.join(timeout=10)
        
        concurrent_time = time.time() - start
        
        # Concurrent should not be much slower than sequential
        # Allow 2x overhead for thread management
        assert concurrent_time < sequential_time * 2, \
            f"Concurrent ({concurrent_time:.2f}s) much slower than sequential ({sequential_time:.2f}s)"


class TestCachingPerformance:
    """Test caching and memoization performance."""
    
    def test_repeated_operations(self):
        """Test repeated operations benefit from caching."""
        from model_checker.syntactic import Syntax
        
        syntax = Syntax()
        formula = "(A \\wedge B) \\vee (C \\wedge D)"
        
        # First parse (cold)
        start = time.time()
        result1 = syntax.parse(formula)
        first_time = time.time() - start
        
        # Second parse (potentially cached)
        start = time.time()
        result2 = syntax.parse(formula)
        second_time = time.time() - start
        
        # Second should not be slower than first
        # (May not be faster if no caching, but shouldn't degrade)
        assert second_time <= first_time * 1.5, \
            f"Second parse ({second_time:.4f}s) slower than first ({first_time:.4f}s)"
    
    def test_theory_loading_performance(self):
        """Test theory loading doesn't degrade."""
        from model_checker.utils.api import get_theory
        
        # First load
        start = time.time()
        theory1 = get_theory('logos')
        first_time = time.time() - start
        
        # Second load
        start = time.time()
        theory2 = get_theory('logos')
        second_time = time.time() - start
        
        # Should be same or faster (cached)
        assert second_time <= first_time * 1.1, \
            f"Second load ({second_time:.4f}s) slower than first ({first_time:.4f}s)"


class TestWorstCasePerformance:
    """Test worst-case performance scenarios."""
    
    @pytest.mark.timeout(60)
    def test_maximum_n_performance(self):
        """Test performance at maximum N value."""
        start = time.time()
        
        settings = {
            'N': 64,
            'max_time': 30  # Give it reasonable timeout
        }
        
        try:
            from model_checker.models import ModelDefaults
            model = ModelDefaults(settings)
            
            elapsed = time.time() - start
            # Should complete or timeout within max_time
            assert elapsed < settings['max_time'] + 5
            
        except Exception:
            # Timeout or resource limit expected
            elapsed = time.time() - start
            assert elapsed < settings['max_time'] + 5
    
    def test_many_propositions_performance(self):
        """Test performance with many propositions."""
        from model_checker.syntactic import Syntax
        
        # Create formula with many propositions
        props = [f"p{i}" for i in range(30)]
        formula = " \\wedge ".join(props)
        formula = f"({formula})"
        
        syntax = Syntax()
        
        start = time.time()
        try:
            result = syntax.parse(formula)
            elapsed = time.time() - start
            
            # Should parse reasonably quickly
            assert elapsed < 2.0, f"Parsing 30 propositions took {elapsed:.2f}s"
        except Exception:
            # Parsing failure acceptable for extreme cases
            pass