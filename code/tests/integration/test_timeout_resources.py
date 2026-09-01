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

# The wall-clock budgets this file used to assert have been removed. They were
# not measuring the code's cost: the bimodal theory's default `max_time` is 1
# second, so every `create_test_model` call here measured
# `min(real_solve_time, max_time) + overhead` and pinned near that cap. The
# budgets sat a fraction of a second above a cap-pinned quantity (the tightest
# had 0.01s of margin), which makes them coin flips rather than guards. The
# second-scale budgets that remain are hang guards, marked as such in place --
# they mean "did not hang", not "was fast" -- and `@pytest.mark.timeout(...)`
# is the preferred mechanism where one applies.


class TestTimeoutHandling:
    """Test timeout handling in various components."""
    
    # Contention-sensitive: asserts an absolute wall-clock bound (elapsed < 5.0s)
    # derived from a real time.time() read around Z3 solving, which CPU contention
    # under -n 6 can push past budget -- run serially instead. Surfaced by
    # code/tests/ci/test_timing_marker_coverage.py's AST scan (Phase 5's own
    # inventory, scoped to code/src/model_checker/**/tests/** plus a code/tests/**
    # grep pass, missed this file).
    @pytest.mark.xdist_serial
    def test_z3_solver_timeout(self):
        """Test Z3 solver respects timeout settings.

        Note: Even with a short Z3 timeout, Python-side constraint generation
        takes time. We use a small N to keep constraint generation fast.

        The 5s budgets below are hang guards, not performance budgets: the
        measured cost is 0.07-0.09s, so the assertion means "did not hang",
        with 55x headroom.
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
    
    # Contention-sensitive: asserts an absolute wall-clock bound (elapsed < 6.0s)
    # derived from a real time.time() read around a CLI subprocess call, which CPU
    # contention under -n 6 can push past budget -- run serially instead.
    @pytest.mark.xdist_serial
    def test_cli_command_timeout(self, tmp_path):
        """Test CLI respects timeout for long-running operations.

        The 6s budget below is a hang guard, not a performance budget: it is
        backed by the subprocess's own `timeout=5`, and the measured cost is
        0.26-0.29s. The assertion means "the CLI did not hang".
        """
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
        """Test the requested timeout reaches the constructed model.

        This used to assert `settings['max_time'] == timeout_value` -- that
        the dict it had just built contained what it put there, which is
        tautological. The property worth pinning is that the setting survives
        settings resolution and reaches the model.
        """
        settings = {
            'N': 5,
            'max_time': timeout_value
        }

        try:
            model = create_test_model(settings)
        except Exception:
            # Very small timeouts might fail immediately
            assert timeout_value < 0.01
            return

        # Should handle all positive timeout values
        assert model.max_time == timeout_value
        assert model.settings['max_time'] == timeout_value


class TestResourceLimits:
    """Test resource limit handling.

    Mixed class: test_large_state_space and test_many_propositions are
    resource-handling tests with no wall-clock assertions of their own;
    test_concurrent_model_building pins the single-threaded-construction
    contract (see that test's docstring and models/concurrency.py). None of
    the three is marked "slow".
    """

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
    
    def test_many_propositions(self):
        """Test handling of many propositions."""
        # Create many propositions
        num_props = 50
        assumptions = [f"p{i}" for i in range(num_props)]

        settings = {'N': 4}

        try:
            # This might stress memory with many propositions
            model = create_test_model(settings, premises=assumptions)
        except MemoryError:
            # Acceptable for extreme cases
            return

        # Should handle many propositions
        assert model is not None
    
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


class TestInterruptHandling:
    """Test handling of interrupts and cancellation."""

    # A `test_keyboard_interrupt_cleanup` test used to live here. It created a
    # module containing `time.sleep(10)` and then asserted only that the
    # returned path was truthy -- it never sent an interrupt and tested nothing
    # about cleanup. It was deleted rather than left claiming coverage of
    # interrupt handling that it did not provide.

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


class TestPerformanceDegradation:
    """Test behaviour under constraint-heavy and larger-N conditions."""

    def test_performance_with_many_constraints(self):
        """Test a constraint-heavy construction terminates.

        This used to assert `elapsed < max_time + 0.5` against a measured
        1.14-1.17s. The 0.33s of margin sat above a value pinned by the
        `max_time` cap itself, which is the same shape as the assertions that
        did fail intermittently. What is asserted now is that the attempt
        terminated, one way or the other.

        Pinned to theory_name='bimodal' explicitly, for the same reason
        TestExecutionPerformance.test_complex_model_performance in
        test_performance.py is: N=10 with contingent/non_empty/non_null/
        disjoint was calibrated against bimodal's own state representation.
        `max_time` only bounds the Z3 solve call, not Python-side constraint
        generation -- and under logos's eager 2^N state enumeration, this
        setting was observed to drive the worker process into heavy
        swapping (10+ GB RSS, uninterruptible-sleep I/O wait) well before
        Z3 was ever invoked, which no `except Exception` clause can catch.
        This is exactly the "call site that genuinely needs bimodal" carve-out
        the shared helper's default-swap anticipates.
        """
        # Settings that create many constraints
        settings = {
            'N': 10,
            'contingent': True,
            'non_empty': True,
            'non_null': True,
            'disjoint': True,
            'max_time': 1.0
        }

        try:
            model = create_test_model(settings, theory_name='bimodal')
        except Exception:
            # Failing rather than completing is acceptable here
            return

        assert model is not None

    @pytest.mark.parametrize("n", [2, 4, 8])
    def test_scaling_behavior(self, n):
        """Test model construction terminates across a range of N.

        This used to assert a per-N wall-clock budget. The tightest case had
        as little as 0.01s of margin over a cap-pinned measurement, and the
        N=8 case spent 4.1s purely burning down its own `max_time`. A small
        fixed `max_time` is used instead: no timing is asserted, so there is
        nothing to be gained by waiting out a longer cap.
        """
        settings = {
            'N': n,
            'max_time': 0.05
        }

        try:
            model = create_test_model(settings)
        except Exception:
            # Timing out is an acceptable outcome at this cap
            return

        assert model is not None


class TestResourceRecovery:
    """Test resource recovery after errors."""
    
    def test_memory_released_after_error(self):
        """Test memory is released after errors.

        Pinned to theory_name='bimodal' explicitly: this loops 10 real
        constructions at N=10, and `max_time` bounds only the Z3 solve, not
        the Python-side constraint generation that precedes it -- under
        logos's eager 2^N state enumeration that generation alone measures
        ~22s per call at N=10 (see test_z3_timeout_handling's sibling
        comment in test_error_handling.py), which x10 iterations would turn
        this object-count-growth check into a multi-minute, multi-GB
        construction loop for no coverage benefit. bimodal's construction
        stays cheap at N=10, which is what a x10 loop needs to stay cheap.
        """
        import gc

        initial_objects = len(gc.get_objects())

        # Create and destroy multiple models. A small explicit `max_time` is
        # used because this test never inspects the solve result -- it asserts
        # only object-count growth -- so waiting out the theory's default
        # 1-second cap ten times would be paid for nothing.
        for _ in range(10):
            try:
                settings = {'N': 10, 'max_time': 0.05}
                model = create_test_model(settings, theory_name='bimodal')
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
        
        # Create and process multiple files. Three iterations exercise
        # handle-leak growth as well as five did, at 40% of the CLI cost.
        for i in range(3):
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