"""Tests for the model-construction concurrency guard.

Model construction builds Z3 AST nodes against the single process-global
Z3 context with no locking in the call path (see
``model_checker.models.concurrency`` for the full contract). These tests
exercise the guard primitive in isolation, with no dependency on the model
classes themselves: sequential and same-thread-reentrant acquisition must
always succeed, a second thread attempting to acquire while another thread
holds the guard must fail fast with ``ConcurrentConstructionError``, and an
exception raised inside the guarded region must not leave the guard held.
"""

import threading
import time

import pytest

from model_checker.models.concurrency import (
    ConcurrentConstructionError,
    guard_construction,
    single_threaded_construction,
)


class TestSequentialAcquireRelease:
    """Repeated sequential acquire/release from a single thread."""

    def test_single_acquire_release_succeeds(self):
        with single_threaded_construction():
            pass

    def test_repeated_sequential_acquire_release_succeeds(self):
        for _ in range(50):
            with single_threaded_construction():
                pass


class TestSameThreadReentrancy:
    """Same-thread nested acquisition must succeed at any depth."""

    def test_nested_depth_two_succeeds(self):
        with single_threaded_construction():
            with single_threaded_construction():
                pass

    def test_nested_depth_three_succeeds(self):
        with single_threaded_construction():
            with single_threaded_construction():
                with single_threaded_construction():
                    pass

    def test_guard_only_frees_at_depth_zero(self):
        """After the outer context exits, a fresh acquire must succeed
        (proves the guard was actually released, not merely decremented
        past zero or left permanently held)."""
        with single_threaded_construction():
            with single_threaded_construction():
                pass
        # Guard must be fully free now; a new acquire must succeed.
        with single_threaded_construction():
            pass


class TestCrossThreadRejection:
    """A second thread attempting to acquire while another thread holds
    the guard must raise ConcurrentConstructionError, never block and
    never silently proceed."""

    def test_second_thread_raises_while_first_holds(self):
        holder_ready = threading.Event()
        release_holder = threading.Event()
        other_thread_error = []
        other_thread_finished = threading.Event()

        def hold():
            with single_threaded_construction():
                holder_ready.set()
                release_holder.wait(timeout=5)

        def contend():
            holder_ready.wait(timeout=5)
            try:
                with single_threaded_construction():
                    pass
            except ConcurrentConstructionError as exc:
                other_thread_error.append(exc)
            finally:
                other_thread_finished.set()

        holder = threading.Thread(target=hold)
        contender = threading.Thread(target=contend)

        holder.start()
        holder_ready.wait(timeout=5)
        contender.start()
        contender.join(timeout=5)
        assert other_thread_finished.is_set()
        release_holder.set()
        holder.join(timeout=5)

        assert len(other_thread_error) == 1
        assert isinstance(other_thread_error[0], ConcurrentConstructionError)

    def test_guard_is_free_after_holder_releases(self):
        """After the holder releases, a new thread must be able to
        acquire the guard (proves cross-thread rejection does not
        permanently wedge the guard)."""
        holder_ready = threading.Event()
        release_holder = threading.Event()

        def hold():
            with single_threaded_construction():
                holder_ready.set()
                release_holder.wait(timeout=5)

        holder = threading.Thread(target=hold)
        holder.start()
        holder_ready.wait(timeout=5)
        release_holder.set()
        holder.join(timeout=5)

        acquired = []

        def acquire_after_release():
            with single_threaded_construction():
                acquired.append(True)

        follower = threading.Thread(target=acquire_after_release)
        follower.start()
        follower.join(timeout=5)
        assert acquired == [True]


class TestReleaseOnException:
    """An exception raised inside the guarded region must still release
    the guard."""

    def test_exception_inside_guard_still_releases(self):
        class _Boom(Exception):
            pass

        with pytest.raises(_Boom):
            with single_threaded_construction():
                raise _Boom("simulated construction failure")

        # Guard must be free: a later acquire from any thread succeeds.
        with single_threaded_construction():
            pass

    def test_exception_inside_guard_releases_for_other_threads(self):
        class _Boom(Exception):
            pass

        with pytest.raises(_Boom):
            with single_threaded_construction():
                raise _Boom("simulated construction failure")

        acquired = []

        def acquire_from_other_thread():
            with single_threaded_construction():
                acquired.append(True)

        t = threading.Thread(target=acquire_from_other_thread)
        t.start()
        t.join(timeout=5)
        assert acquired == [True]


class TestGuardConstructionDecorator:
    """The guard_construction decorator wraps a function the same way the
    context manager wraps a block."""

    def test_decorator_allows_sequential_calls(self):
        @guard_construction
        def build(x):
            return x * 2

        assert build(1) == 2
        assert build(2) == 4

    def test_decorator_preserves_function_metadata(self):
        @guard_construction
        def build(x):
            """Docstring."""
            return x

        assert build.__name__ == "build"
        assert build.__doc__ == "Docstring."

    def test_decorator_releases_guard_on_exception(self):
        class _Boom(Exception):
            pass

        @guard_construction
        def build():
            raise _Boom("boom")

        with pytest.raises(_Boom):
            build()

        # Guard must be free afterwards.
        with single_threaded_construction():
            pass

    def test_decorator_rejects_cross_thread_contention(self):
        holder_ready = threading.Event()
        release_holder = threading.Event()
        other_thread_error = []

        @guard_construction
        def hold():
            holder_ready.set()
            release_holder.wait(timeout=5)

        @guard_construction
        def contend():
            pass

        def run_hold():
            hold()

        def run_contend():
            holder_ready.wait(timeout=5)
            try:
                contend()
            except ConcurrentConstructionError as exc:
                other_thread_error.append(exc)

        holder = threading.Thread(target=run_hold)
        contender = threading.Thread(target=run_contend)
        holder.start()
        holder_ready.wait(timeout=5)
        contender.start()
        contender.join(timeout=5)
        release_holder.set()
        holder.join(timeout=5)

        assert len(other_thread_error) == 1


class TestErrorMessageAndType:
    """The error names the contract and tells the caller what to do
    instead, and is a RuntimeError subclass."""

    def test_is_runtime_error_subclass(self):
        assert issubclass(ConcurrentConstructionError, RuntimeError)

    def test_error_message_names_contract_and_remedy(self):
        holder_ready = threading.Event()
        release_holder = threading.Event()
        captured = []

        def hold():
            with single_threaded_construction():
                holder_ready.set()
                release_holder.wait(timeout=5)

        def contend():
            holder_ready.wait(timeout=5)
            try:
                with single_threaded_construction():
                    pass
            except ConcurrentConstructionError as exc:
                captured.append(str(exc))

        holder = threading.Thread(target=hold)
        contender = threading.Thread(target=contend)
        holder.start()
        holder_ready.wait(timeout=5)
        contender.start()
        contender.join(timeout=5)
        release_holder.set()
        holder.join(timeout=5)

        assert len(captured) == 1
        message = captured[0].lower()
        # Names the contract.
        assert "single" in message and "thread" in message
        # Tells the caller what to do instead.
        assert "sequential" in message or "process" in message
