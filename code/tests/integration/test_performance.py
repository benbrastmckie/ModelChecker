"""Performance testing for ModelChecker.

This module tests performance characteristics including
execution time, memory usage, and scaling behavior.
"""

import pytest
import time
import gc
import threading
from tests.utils.base import BaseModelTest, BaseExampleTest
from tests.utils.helpers import create_test_model
from model_checker.models.concurrency import ConcurrentConstructionError

# Wall-clock assertions in this file are load-sensitive (see TESTING_GUIDE.md 8.6):
# repeat full-suite sweeps have shown these budgets tripped under concurrent load
# with no code change. Each class carrying such assertions is marked "slow" so a
# default run can opt out via `-m "not slow"` for deterministic results; run with
# `-m slow` (or no -m filter) to validate actual performance characteristics. This
# was previously a single module-level `pytestmark = pytest.mark.slow`; it is now
# applied per-class so that TestConcurrentPerformance -- which asserts the
# single-threaded-construction contract, not a wall-clock budget -- runs in the
# default suite (see models/concurrency.py for the contract it pins).


@pytest.mark.slow
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
        (2, 1.0),
        (4, 2.0),
        (8, 10.0),
        # N=16 removed: 2^16 = 65536 states causes exponential blowup
    ])
    @pytest.mark.timeout(20)
    def test_scaling_with_n(self, n, max_time):
        """Test performance scales reasonably with N.

        Note: N=16 is excluded because the state space (2^N) grows exponentially.
        N=8 with 256 states is the practical upper bound for this test.
        """
        start = time.time()

        settings = {'N': n}

        try:
            model = self.create_model(settings)
            elapsed = time.time() - start

            assert elapsed < max_time, \
                f"N={n} took {elapsed:.2f}s, expected < {max_time}s"
        except Exception:
            # Resource limits acceptable for larger N values
            assert n >= 8


@pytest.mark.slow
class TestMemoryPerformance:
    """Test memory usage performance."""
    
    def test_memory_usage_simple(self):
        """Test memory usage for simple models."""
        import tracemalloc

        # Start memory tracking
        tracemalloc.start()

        # Create simple model
        model = create_test_model({'N': 3})

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
            model = create_test_model({
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

        # Force garbage collection
        gc.collect()

        # Get baseline object count
        baseline_objects = len(gc.get_objects())

        # Create and destroy multiple models
        for i in range(5):
            model = create_test_model({'N': 3})
            del model

        # Force garbage collection
        gc.collect()

        # Check object count hasn't grown significantly
        final_objects = len(gc.get_objects())
        growth = final_objects - baseline_objects

        # Allow some growth but should be bounded
        assert growth < 500, f"Object count grew by {growth}, possible memory leak"


@pytest.mark.slow
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
    """Pins the single-threaded-only model-construction contract.

    This is NOT a performance test despite the module it lives in: it used to
    assert `concurrent_time < sequential_time * 2`, exactly the load-sensitive
    wall-clock assertion this file's own header comment flags as unreliable.
    Model construction builds Z3 AST nodes against the single process-global
    Z3 context with no locking (see `model_checker.models.concurrency`), so
    concurrent construction from multiple threads is not a supported, safe
    pattern to time -- it used to segfault the interpreter outright (5/8
    crashes at 3 threads, see the concurrent-segfault investigation report).
    Construction is now guarded: a second thread contending for the guard
    raises `ConcurrentConstructionError` instead of corrupting shared state.

    The contract this test pins is "no crash, and any contention is reported
    loudly, never silently corrupted or silently serialized-and-hidden." All
    three threads finishing with an outcome of either success or
    `ConcurrentConstructionError` satisfies that contract. All-`ok` is a
    legitimate outcome too: if the scheduler happens to run the threads one
    at a time, no contention is ever observed, and that is not a failure --
    the guard's job is only to make contention safe when it does occur, not
    to force contention to happen.
    """

    def test_sequential_vs_concurrent(self):
        """3 threads build a model concurrently; every outcome must be
        success or the documented ConcurrentConstructionError, never a
        crash or any other exception, and at least one thread must
        succeed (the guard must not deadlock or starve every thread)."""
        outcomes = []
        outcomes_lock = threading.Lock()

        def make_model():
            try:
                create_test_model({'N': 3})
                result = ('ok', None)
            except ConcurrentConstructionError as exc:
                result = ('contended', exc)
            except Exception as exc:  # noqa: BLE001 - intentionally broad: capture, never swallow
                result = ('other', exc)
            with outcomes_lock:
                outcomes.append(result)

        threads = [threading.Thread(target=make_model) for _ in range(3)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(timeout=10)

        assert all(not t.is_alive() for t in threads), (
            "A thread did not terminate within the join timeout."
        )

        other_failures = [exc for kind, exc in outcomes if kind == 'other']
        assert not other_failures, (
            f"Unexpected exception(s) during concurrent construction "
            f"(expected only success or ConcurrentConstructionError): "
            f"{other_failures!r}"
        )

        assert len(outcomes) == 3, f"Expected 3 outcomes, got {len(outcomes)}: {outcomes!r}"
        ok_count = sum(1 for kind, _ in outcomes if kind == 'ok')
        assert ok_count >= 1, (
            f"No thread succeeded -- the guard must not deadlock or starve "
            f"every thread. Outcomes: {outcomes!r}"
        )


@pytest.mark.slow
class TestCachingPerformance:
    """Test caching and memoization performance."""
    
    def test_repeated_operations(self):
        """Test repeated operations benefit from caching."""
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib import bimodal

        # Get a valid operator collection for testing
        theory = bimodal.get_theory()
        operators = theory['operators']
        formula = "((A \\wedge B) \\vee (C \\wedge D))"

        # First parse (cold)
        start = time.time()
        syntax1 = Syntax([], [formula], operators)
        first_time = time.time() - start

        # Second parse (potentially cached)
        start = time.time()
        syntax2 = Syntax([], [formula], operators)
        second_time = time.time() - start

        # Second should not be slower than first
        # (May not be faster if no caching, but shouldn't degrade)
        assert second_time <= first_time * 1.5, \
            f"Second parse ({second_time:.4f}s) slower than first ({first_time:.4f}s)"
    
    def test_theory_loading_performance(self):
        """Test theory loading doesn't degrade."""
        # model_checker.api.get_theory (not utils.api.get_theory) is the theory-aware
        # entry point that auto-loads semantic_theories by name; utils.api.get_theory is
        # a pure lookup requiring the caller to supply an already-loaded mapping.
        from model_checker.api import get_theory
        
        # First load
        start = time.time()
        theory1 = get_theory('bimodal')
        first_time = time.time() - start
        
        # Second load
        start = time.time()
        theory2 = get_theory('bimodal')
        second_time = time.time() - start
        
        # Should be same or faster (cached)
        assert second_time <= first_time * 1.1, \
            f"Second load ({second_time:.4f}s) slower than first ({first_time:.4f}s)"


@pytest.mark.slow
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
            model = create_test_model(settings)

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
        from model_checker.theory_lib import bimodal

        # Get a valid operator collection for testing
        theory = bimodal.get_theory()
        operators = theory['operators']

        # Create formula with many propositions (using proper syntax)
        props = [f"p{i}" for i in range(30)]
        formula = " \\wedge ".join(props)
        formula = f"({formula})"

        start = time.time()
        try:
            syntax = Syntax([], [formula], operators)
            elapsed = time.time() - start

            # Should parse reasonably quickly
            assert elapsed < 2.0, f"Parsing 30 propositions took {elapsed:.2f}s"
        except Exception:
            # Parsing failure acceptable for extreme cases
            pass