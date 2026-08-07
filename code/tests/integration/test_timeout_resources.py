"""Test timeout and resource handling.

This module tests the framework's behavior under resource constraints,
including timeouts, memory limits, and concurrent operations.
"""

import pytest
import time
import threading
from unittest.mock import patch, Mock
from tests.utils.helpers import create_test_module, create_test_model
from model_checker.models.concurrency import ConcurrentConstructionError

# Timing/subprocess-timeout assertions in this file are load-sensitive (see
# TESTING_GUIDE.md 8.6): repeat full-suite sweeps have shown these budgets
# tripped under concurrent load with no code change. Each class carrying
# such assertions is marked "slow" so a default run can opt out via
# `-m "not slow"` for deterministic results; run with `-m slow` (or no -m
# filter) to validate actual timeout/resource handling. This was previously
# a single module-level `pytestmark = pytest.mark.slow`; it is now applied
# per-class (per-method within TestResourceLimits, which mixes timing-
# sensitive tests with the single-threaded-construction contract test) so
# that test_concurrent_model_building -- which asserts the documented
# construction contract, not a wall-clock budget -- runs in the default
# suite (see models/concurrency.py for the contract it pins).


@pytest.mark.slow
class TestTimeoutHandling:
    """Test timeout handling in various components."""
    
    def test_z3_solver_timeout(self):
        """Test Z3 solver respects timeout settings.

        Note: Even with a short Z3 timeout, Python-side constraint generation
        takes time. We use a small N to keep constraint generation fast.
        """
        # Use small N to keep constraint generation fast
        settings = {
            'N': 3,
            'max_time': 0.01,  # 10ms timeout
            'contingent': True,
            'non_empty': True
        }

        start_time = time.time()

        try:
            model = create_test_model(settings)
            # If model completes, check it didn't take too long
            elapsed = time.time() - start_time
            # Allow time for Python constraint generation overhead
            assert elapsed < 5.0  # Should not hang

            # Check model indicates timeout if it occurred
            if hasattr(model, 'timeout_occurred'):
                if model.timeout_occurred:
                    assert model.satisfiable is None
        except Exception as e:
            # Timeout exceptions are acceptable
            elapsed = time.time() - start_time
            assert elapsed < 5.0  # Should timeout within reasonable time
    
    def test_cli_command_timeout(self, tmp_path):
        """Test CLI respects timeout for long-running operations."""
        from tests.utils.helpers import run_cli_command
        
        # Create a module that would take long to process
        content = '''
from model_checker.theory_lib import bimodal
theory = bimodal.get_theory()
semantic_theories = {"test": theory}

# Complex example that might take time
example_range = {
    "COMPLEX": [
        ["A", "B", "C", "D", "E"],
        ["F", "G", "H", "I", "J"],
        {"N": 64, "max_time": 0.01}  # Large N, short timeout
    ]
}
'''
        module_path = create_test_module(content, tmp_path, 'timeout_test.py')
        
        start_time = time.time()
        result = run_cli_command([module_path], timeout=5, check=False)
        elapsed = time.time() - start_time
        
        # Should complete within reasonable time
        assert elapsed < 6.0  # Allow some overhead
    
    @pytest.mark.parametrize("timeout_value", [0.001, 0.01, 0.1])
    def test_various_timeout_values(self, timeout_value):
        """Test handling of various timeout values."""
        settings = {
            'N': 5,
            'max_time': timeout_value
        }

        try:
            model = create_test_model(settings)
            # Should handle all positive timeout values
            assert settings['max_time'] == timeout_value
        except Exception:
            # Very small timeouts might fail immediately
            assert timeout_value < 0.01


class TestResourceLimits:
    """Test resource limit handling.

    Mixed class: test_large_state_space and test_many_propositions are
    resource-handling tests (no wall-clock assertions of their own, but
    the large-N model construction they exercise is expensive enough to
    keep behind the "slow" opt-out), marked individually below since the
    class as a whole also hosts test_concurrent_model_building, which must
    NOT be marked slow (see that test's docstring and models/concurrency.py).
    """

    @pytest.mark.slow
    def test_large_state_space(self):
        """Test handling of large state spaces."""
        # Test increasing N values
        for n in [32, 48, 64]:
            settings = {'N': n}

            try:
                model = create_test_model(settings)
                # Should handle or fail gracefully
                assert model is not None
            except MemoryError:
                # Memory errors acceptable for large N
                assert n >= 48  # Should handle at least N=32
            except Exception as e:
                # Other exceptions should be informative
                assert "memory" in str(e).lower() or "resource" in str(e).lower()
    
    @pytest.mark.slow
    def test_many_propositions(self):
        """Test handling of many propositions."""
        # Create many propositions
        num_props = 50
        assumptions = [f"p{i}" for i in range(num_props)]

        settings = {'N': 4}

        try:
            # This might stress memory with many propositions
            model = create_test_model(settings, premises=assumptions)
            # Should handle many propositions
        except MemoryError:
            # Acceptable for extreme cases
            pass
    
    def test_concurrent_model_building(self):
        """Pins the single-threaded-only model-construction contract at 5
        threads.

        This test used to build 5 models concurrently and only check that
        every thread terminated -- it swallowed the actual outcome
        (`except Exception: return False`) and never inspected it, so a
        segfault was the only way it could ever fail loudly; a crash aborts
        the whole interpreter before any assertion runs. The report
        investigating this measured a 100% crash rate at 5 threads (6/6
        isolated runs), the strongest regression detector of the two
        crashing tests -- kept at 5 threads for that reason.

        Construction is now guarded (see models/concurrency.py): a second
        thread contending for the guard raises ConcurrentConstructionError
        instead of racing on the shared Z3 context. The contract pinned
        here is the same as TestConcurrentPerformance.test_sequential_vs_concurrent
        in test_performance.py: every thread's outcome must be success or
        ConcurrentConstructionError, never a crash or any other exception,
        never swallowed, and at least one thread must succeed.
        """
        outcomes = []
        outcomes_lock = threading.Lock()

        def build_model():
            settings = {'N': 3}
            try:
                create_test_model(settings)
                result = ('ok', None)
            except ConcurrentConstructionError as exc:
                result = ('contended', exc)
            except Exception as exc:  # noqa: BLE001 - intentionally broad: capture, never swallow
                result = ('other', exc)
            with outcomes_lock:
                outcomes.append(result)

        num_threads = 5
        threads = [threading.Thread(target=build_model) for _ in range(num_threads)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(timeout=5)

        assert all(not t.is_alive() for t in threads), (
            "A thread did not terminate within the join timeout."
        )

        other_failures = [exc for kind, exc in outcomes if kind == 'other']
        assert not other_failures, (
            f"Unexpected exception(s) during concurrent construction "
            f"(expected only success or ConcurrentConstructionError): "
            f"{other_failures!r}"
        )

        assert len(outcomes) == num_threads, (
            f"Expected {num_threads} outcomes, got {len(outcomes)}: {outcomes!r}"
        )
        ok_count = sum(1 for kind, _ in outcomes if kind == 'ok')
        assert ok_count >= 1, (
            f"No thread succeeded -- the guard must not deadlock or starve "
            f"every thread. Outcomes: {outcomes!r}"
        )


@pytest.mark.slow
class TestInterruptHandling:
    """Test handling of interrupts and cancellation."""
    
    def test_keyboard_interrupt_cleanup(self, tmp_path):
        """Test cleanup occurs on keyboard interrupt."""
        from tests.utils.helpers import run_cli_command
        
        content = '''
import time
time.sleep(10)  # Long sleep to allow interrupt
'''
        module_path = create_test_module(content, tmp_path, 'interrupt.py')
        
        # This would need actual interrupt testing
        # For now, just verify the module is valid
        assert module_path
    
    @pytest.mark.timeout(10)
    def test_graceful_shutdown(self):
        """Test graceful shutdown on resource-intensive operations.

        Note: N=64 causes exponential blowup (2^64 states) and hangs.
        We use a smaller N that is still large enough to stress resources.
        """
        # Use smaller N that won't hang but still stresses the system
        settings = {
            'N': 5,
            'maximize': True,
            'contingent': True,
            'non_empty': True,
            'max_time': 1.0  # Allow reasonable time
        }

        try:
            model = create_test_model(settings)
            # If successful, model should be valid
            assert model is not None
        except Exception:
            # Any exception is acceptable - the test verifies no hang occurs
            pass


@pytest.mark.slow
class TestPerformanceDegradation:
    """Test performance under degraded conditions."""
    
    def test_performance_with_many_constraints(self):
        """Test performance with many constraints."""
        # Settings that create many constraints
        settings = {
            'N': 10,
            'contingent': True,
            'non_empty': True,
            'non_null': True,
            'disjoint': True,
            'max_time': 1.0
        }

        start_time = time.time()

        try:
            model = create_test_model(settings)
            elapsed = time.time() - start_time

            # Should complete in reasonable time
            assert elapsed < settings['max_time'] + 0.5  # Allow overhead
        except Exception:
            # Should fail quickly if it can't handle
            elapsed = time.time() - start_time
            assert elapsed < settings['max_time'] + 0.5
    
    @pytest.mark.parametrize("n,expected_time", [
        (2, 0.1),
        (4, 0.5),
        (8, 2.0),
    ])
    def test_scaling_behavior(self, n, expected_time):
        """Test that processing time scales reasonably with N."""
        settings = {
            'N': n,
            'max_time': expected_time * 2  # Allow 2x expected
        }

        start_time = time.time()

        try:
            model = create_test_model(settings)
            elapsed = time.time() - start_time

            # Should not take much longer than expected
            assert elapsed < expected_time * 3
        except Exception:
            # Should timeout appropriately
            elapsed = time.time() - start_time
            assert elapsed < settings['max_time'] + 0.5


@pytest.mark.slow
class TestResourceRecovery:
    """Test resource recovery after errors."""
    
    def test_memory_released_after_error(self):
        """Test memory is released after errors."""
        import gc

        initial_objects = len(gc.get_objects())

        # Create and destroy multiple models
        for _ in range(10):
            try:
                settings = {'N': 10}
                model = create_test_model(settings)
                del model
            except Exception:
                pass

        # Force garbage collection
        gc.collect()

        # Check object count hasn't grown too much
        final_objects = len(gc.get_objects())
        growth = final_objects - initial_objects

        # Some growth is normal, but should be bounded
        assert growth < 1000  # Reasonable threshold
    
    def test_file_handles_closed(self, tmp_path):
        """Test file handles are properly closed."""
        import os
        
        # Get initial open files (platform-dependent)
        try:
            import psutil
            process = psutil.Process(os.getpid())
            initial_files = len(process.open_files())
        except ImportError:
            # psutil not available, skip detailed check
            initial_files = 0
        
        # Create and process multiple files
        for i in range(5):
            content = f'''
from model_checker.theory_lib import bimodal
theory = bimodal.get_theory()
semantic_theories = {{"test_{i}": theory}}
example_range = {{"TEST": [[], ["A"], {{"N": 2}}]}}
'''
            module_path = create_test_module(content, tmp_path, f'test_{i}.py')
            
            from tests.utils.helpers import run_cli_command
            result = run_cli_command([module_path], check=False)
        
        # Check file handles
        if initial_files > 0:
            try:
                final_files = len(process.open_files())
                # Should not leak file handles
                assert final_files <= initial_files + 2  # Allow small variance
            except:
                pass  # Can't check without psutil