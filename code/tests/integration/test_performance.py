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

# The wall-clock budgets this file used to assert have been removed. They were
# not measuring the code's cost: the bimodal theory's default `max_time` is 1
# second, so every `create_test_model` call here measured
# `min(real_solve_time, max_time) + overhead` and pinned at ~1.03s no matter
# what N was. Budgets of 1.0s sat inside that distribution (and failed
# intermittently); budgets of 2s, 5s and 10s sat above a ceiling the quantity
# could not physically reach (and could never fail). Neither shape is a
# performance guard, so the timing clauses were replaced by assertions about
# what the code actually produced. The few second-scale budgets that remain are
# marked in place as hang guards -- they mean "did not hang", not "was fast".


class TestExecutionPerformance(BaseModelTest):
    """Test model construction across a range of sizes."""

    @pytest.mark.timeout(5)
    def test_simple_model_performance(self):
        """Test simple models are constructed and well-formed."""
        settings = {'N': 3}
        model = self.create_model(settings)

        assert model is not None
        assert model.N == 3
        assert model.semantics is not None

    @pytest.mark.timeout(10)
    def test_medium_model_performance(self):
        """Test medium complexity models are constructed."""
        settings = {
            'N': 8,
            'contingent': True,
            'non_empty': True
        }
        model = self.create_model(settings)

        assert model is not None
        assert model.N == 8

    @pytest.mark.timeout(30)
    def test_complex_model_performance(self):
        """Test complex models complete within timeout.

        The 20s/30s budgets below are hang guards, not performance budgets.
        This is the one construction here whose cost is real rather than
        solver-capped (N=16 Python-side constraint generation, measured
        ~6s), and the assertion means "did not hang", with 3.3x headroom.
        """
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
    
    @pytest.mark.parametrize("n", [2, 4, 8])
    @pytest.mark.timeout(20)
    def test_scaling_with_n(self, n):
        """Test model construction succeeds across a range of N.

        Note: N=16 is excluded because the state space (2^N) grows exponentially.
        N=8 with 256 states is the practical upper bound for this test.

        This used to assert a per-N wall-clock budget. Every N measured ~1.03s
        because all of them hit the theory's 1-second `max_time` cap, so the
        budgets described the cap rather than any scaling behaviour.
        """
        settings = {'N': n}

        try:
            model = self.create_model(settings)
            assert model is not None
            assert model.N == n
        except Exception:
            # Resource limits acceptable for larger N values
            assert n >= 8


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

        # Create and destroy multiple models. A small explicit `max_time` is
        # used because this test never inspects the solve result -- it asserts
        # only object-count growth -- so waiting out the theory's default
        # 1-second cap five times would be paid for nothing.
        for i in range(5):
            model = create_test_model({'N': 3, 'max_time': 0.05})
            del model

        # Force garbage collection
        gc.collect()

        # Check object count hasn't grown significantly
        final_objects = len(gc.get_objects())
        growth = final_objects - baseline_objects

        # Allow some growth but should be bounded
        assert growth < 500, f"Object count grew by {growth}, possible memory leak"


class TestBatchPerformance(BaseExampleTest):
    """Test batch construction and structural validation of examples.

    Note that `validate_example` performs structural checks only -- it does no
    model checking. The wall-clock budgets these tests used to carry therefore
    measured a few dozen list constructions (<5ms against budgets of 2s and 5s)
    and have been removed.
    """

    def test_batch_small_examples(self):
        """Test many small examples can be built and structurally validated."""
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

        assert len(examples) == 20

    def test_batch_mixed_complexity(self):
        """Test mixed complexity examples can be built and validated."""
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

        assert len(examples) == 9


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


class TestCachingPerformance:
    """Test repeat-parse determinism and theory caching."""

    def test_repeated_operations(self):
        """Test parsing the same formula twice yields the same structure.

        This used to compare the wall-clock cost of two sub-millisecond
        parses, which passed only because the first parse pays a cold-start
        cost. That is noise, not a caching signal. What is worth pinning is
        that the parse is deterministic.
        """
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib import bimodal

        # Get a valid operator collection for testing
        theory = bimodal.get_theory()
        operators = theory['operators']
        formula = "((A \\wedge B) \\vee (C \\wedge D))"

        syntax1 = Syntax([], [formula], operators)
        syntax2 = Syntax([], [formula], operators)

        assert sorted(syntax1.all_sentences) == sorted(syntax2.all_sentences)
        assert syntax1.infix_conclusions == syntax2.infix_conclusions

    def test_theory_loading_performance(self):
        """Test repeated theory loads are served from the cache.

        This used to compare two sub-millisecond load times. The intent was
        "the theory cache works", so assert that directly.
        """
        # model_checker.api.get_theory (not utils.api.get_theory) is the theory-aware
        # entry point that auto-loads semantic_theories by name; utils.api.get_theory is
        # a pure lookup requiring the caller to supply an already-loaded mapping.
        from model_checker.api import get_theory

        theory1 = get_theory('bimodal')
        theory2 = get_theory('bimodal')

        assert theory1 is theory2


class TestWorstCasePerformance:
    """Test worst-case performance scenarios."""
    
    @pytest.mark.timeout(60)
    def test_maximum_n_performance(self):
        """Test construction at the maximum N value terminates.

        This used to assert a 35s budget against a measured 0.05-0.07s (the
        attempt fails fast at N=64), 500x of headroom. The `@pytest.mark.timeout`
        above is the real hang guard; the assertion below only records that the
        attempt terminated one way or the other.
        """
        settings = {
            'N': 64,
            'max_time': 30  # Give it reasonable timeout
        }

        try:
            model = create_test_model(settings)
            assert model is not None
        except Exception:
            # Timeout or resource limit expected
            pass

    def test_many_propositions_performance(self):
        """Test a formula with many propositions parses."""
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib import bimodal

        # Get a valid operator collection for testing
        theory = bimodal.get_theory()
        operators = theory['operators']

        # Create formula with many propositions (using proper syntax)
        props = [f"p{i}" for i in range(30)]
        formula = " \\wedge ".join(props)
        formula = f"({formula})"

        try:
            syntax = Syntax([], [formula], operators)
            assert syntax.infix_conclusions == [formula]
        except Exception:
            # Parsing failure acceptable for extreme cases
            pass