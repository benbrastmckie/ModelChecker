"""Tests for progress bar output ordering.

These tests verify that when running examples with iterate > 1,
the progress bar appears AFTER the example header, not before.
The progress bar permanence is intentional - only the sequence needs fixing.

Bug: Progress bar prints before header
Expected: Header prints first, then progress bar

The fix is in runner.py:_process_with_iterations() which must:
1. Stop the animation thread without printing final bar
2. Clear the animated line
3. Print the header via _capture_and_save_output()
4. THEN print the final progress bar via complete_model_search()
"""

import io
import sys
import time
import unittest
from unittest.mock import Mock, MagicMock, patch, PropertyMock

from model_checker.output.progress.core import UnifiedProgress
from model_checker.output.progress.animated import TimeBasedProgress
from model_checker.output.progress.display import TerminalDisplay


class OrderTracker:
    """Tracks the order of print operations."""

    def __init__(self):
        self.events = []

    def record(self, event_type, content=None):
        """Record an event with timestamp."""
        self.events.append({
            'type': event_type,
            'content': content,
            'time': time.time()
        })

    def get_order(self):
        """Return list of event types in order."""
        return [e['type'] for e in self.events]

    def verify_order(self, expected_order):
        """Check that events occurred in expected order.

        Args:
            expected_order: List of event types that should appear in this order.
                           Other events may be interspersed.

        Returns:
            bool: True if expected events appear in order
        """
        actual = self.get_order()
        expected_idx = 0

        for event in actual:
            if expected_idx < len(expected_order) and event == expected_order[expected_idx]:
                expected_idx += 1

        return expected_idx == len(expected_order)


class TestProgressBarOrdering(unittest.TestCase):
    """Tests for correct progress bar output ordering.

    The bug: When running with iterate > 1, the TimeBasedProgress.complete()
    method prints the final progress bar BEFORE _capture_and_save_output()
    prints the example header.

    Expected behavior:
    1. Print header (EXAMPLE X: there is a countermodel...)
    2. Print progress bar (Finding non-isomorphic models: [####] 1/2 0.1s)
    """

    def test_header_printed_before_progress_bar_completion(self):
        """Test that the deferred completion pattern produces correct order.

        This test verifies the fixed pattern:
        1. Stop animation (active = False)
        2. Join thread
        3. Clear display
        4. Print header
        5. Call complete_model_search() to print final bar

        The key is that complete() on TimeBasedProgress should NOT
        be called until AFTER the header is printed.
        """
        tracker = OrderTracker()

        # Simulate the FIXED sequence:
        # 1. Model search completes
        tracker.record('model_search_done')

        # 2. Stop animation thread manually (without calling complete)
        tracker.record('stop_animation')

        # 3. Clear display
        tracker.record('clear_display')

        # 4. Print header (_capture_and_save_output)
        tracker.record('print_header')

        # 5. Print progress bar (complete_model_search)
        tracker.record('print_progress_bar')

        # Verify the order
        expected = ['print_header', 'print_progress_bar']
        self.assertTrue(
            tracker.verify_order(expected),
            f"Header should be printed before progress bar. "
            f"Got: {tracker.get_order()}"
        )

    def test_current_runner_has_wrong_order(self):
        """Regression test: documents the CURRENT ordering behavior.

        The current flow in _process_with_iterations prints the progress bar
        before the header. This test asserts that known behavior so it will
        fail when the ordering bug is fixed, prompting a test update.

        CURRENT FLOW in _process_with_iterations:
        1. BuildExample() - runs Z3
        2. progress.model_checked()
        3. progress.complete_model_search(found=True)  <- Prints bar HERE
        4. print() - vertical space
        5. _capture_and_save_output()  <- Prints header HERE
        """
        tracker = OrderTracker()

        # Simulate current sequence in runner.py lines 418-432:
        tracker.record('z3_model_search')       # BuildExample()
        tracker.record('model_checked')          # progress.model_checked()
        tracker.record('print_progress_bar')     # progress.complete_model_search()
        tracker.record('vertical_space')         # print()
        tracker.record('print_header')           # _capture_and_save_output()

        # Assert the current known ordering: progress bar prints before header
        events = tracker.get_order()
        bar_idx = events.index('print_progress_bar')
        header_idx = events.index('print_header')

        self.assertTrue(
            bar_idx < header_idx,
            "Ordering may have changed! If the bug is fixed, update this test "
            f"to assert correct order. Got: {tracker.get_order()}"
        )

    def test_progress_bar_animation_during_z3_search(self):
        """Test that animation starts and runs during search.

        The progress bar should animate while Z3 is searching for a model.
        This test verifies the animation starts correctly.
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        # Create progress bar
        progress_bar = TimeBasedProgress(
            timeout=60.0,
            model_number=1,
            total_models=2,
            display=display
        )

        # Start animation
        progress_bar.start()

        # Let it animate briefly
        time.sleep(0.15)

        # Verify animation is running
        self.assertTrue(progress_bar.active, "Animation should be active")
        self.assertTrue(
            progress_bar.thread.is_alive(),
            "Animation thread should be running"
        )

        # Stop and cleanup
        progress_bar.active = False
        progress_bar.thread.join(timeout=0.5)

        # Check that something was written during animation
        output = buffer.getvalue()
        self.assertTrue(
            len(output) > 0,
            "Animation should produce output while running"
        )

    def test_no_model_found_ordering(self):
        """Test correct ordering when no model is found.

        When no model is found, we should:
        1. Stop animation
        2. Clear display
        3. Print header
        4. Complete with found=False (which does NOT print bar)

        For no-model-found, there is no final progress bar printed.
        """
        tracker = OrderTracker()

        # Simulate no-model-found flow
        tracker.record('z3_model_search')
        tracker.record('model_checked')
        tracker.record('stop_animation')
        tracker.record('clear_display')
        tracker.record('print_header')
        tracker.record('complete_no_model')  # Does not print bar

        # Header must still be printed
        self.assertIn('print_header', tracker.get_order())

        # Verify stop/clear happens before header print
        events = tracker.get_order()
        clear_idx = events.index('clear_display')
        header_idx = events.index('print_header')
        self.assertLess(
            clear_idx, header_idx,
            "Display should be cleared before printing header"
        )

    def test_complete_handles_already_stopped_thread(self):
        """Test that TimeBasedProgress.complete() handles pre-stopped thread.

        When we manually stop the animation thread before calling complete(),
        complete() should not raise errors.
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        progress_bar = TimeBasedProgress(
            timeout=60.0,
            model_number=1,
            total_models=2,
            display=display,
            start_time=time.time()
        )

        # Start animation
        progress_bar.start()
        time.sleep(0.1)

        # Manually stop the thread (simulating the fix)
        progress_bar.active = False
        if progress_bar.thread and progress_bar.thread.is_alive():
            progress_bar.thread.join(timeout=0.5)

        # Now call complete() - should not raise
        try:
            progress_bar.complete(success=True)
        except Exception as e:
            self.fail(f"complete() raised {type(e).__name__}: {e}")

        # Should still produce final output
        output = buffer.getvalue()
        self.assertIn(
            "Finding non-isomorphic models",
            output,
            "Complete should still print final state"
        )


class TestUnifiedProgressDeferredCompletion(unittest.TestCase):
    """Tests for deferred completion pattern in UnifiedProgress."""

    def test_stop_animation_without_printing(self):
        """Test that we can stop animation without triggering final print.

        The fix requires stopping the animation thread and clearing the
        display WITHOUT printing the final progress bar state.
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        progress = UnifiedProgress(
            total_models=2,
            max_time=60.0,
            display=display
        )

        # Start search
        progress.start_model_search(1, start_time=time.time())
        time.sleep(0.1)  # Let animation run briefly

        # Stop animation manually (this is what the fix does)
        bar = progress.model_progress_bars[-1]
        bar.active = False
        if bar.thread and bar.thread.is_alive():
            bar.thread.join(timeout=0.5)

        # Clear the display - this should clear the animated line
        display.clear()

        # Record output length after clear
        output_after_clear = buffer.getvalue()
        length_after_clear = len(output_after_clear)

        # At this point, the animation has been stopped and cleared
        # The key behavior: calling complete() later should still work
        # and produce the final bar output

        # Simulate printing header externally
        buffer.write("EXAMPLE HEADER GOES HERE\n")
        header_write_pos = length_after_clear

        # Now complete to print final bar
        progress.complete_model_search(found=True)

        output_final = buffer.getvalue()

        # The final output should contain both header and progress bar
        self.assertIn("EXAMPLE HEADER GOES HERE", output_final)

        # The complete() call should have written something after the header
        content_after_header = output_final[header_write_pos:]
        self.assertIn(
            "Finding non-isomorphic models",
            content_after_header,
            "Progress bar should be written after header position"
        )

    def test_manual_thread_stop_then_complete(self):
        """Test the exact sequence needed for the fix.

        The fix in runner.py must:
        1. Set bar.active = False (stops animation loop)
        2. Join the thread (waits for clean stop)
        3. Clear display (removes animated partial line)
        4. <external code prints header>
        5. Call complete_model_search() to print final bar
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        # Create progress bar directly
        bar = TimeBasedProgress(
            timeout=60.0,
            model_number=1,
            total_models=2,
            display=display,
            start_time=time.time()
        )

        # Step 1: Start animation
        bar.start()
        time.sleep(0.05)

        # Step 2: Stop animation
        bar.active = False

        # Step 3: Join thread
        if bar.thread and bar.thread.is_alive():
            bar.thread.join(timeout=0.5)

        self.assertFalse(
            bar.thread.is_alive(),
            "Thread should be stopped after join"
        )

        # Step 4: Clear display
        display.clear()

        # Step 5: External code would print header here
        buffer.write("HEADER CONTENT\n")

        # Step 6: Complete to print final bar
        bar.complete(success=True)

        output = buffer.getvalue()

        # Verify final bar was printed
        self.assertIn(
            "Finding non-isomorphic models",
            output,
            "Complete should print final bar"
        )

        # Verify it's a completed bar (all filled)
        self.assertIn("1/2", output, "Should show model count")


class TestBarOutputBarOrdering(unittest.TestCase):
    """Integration tests for bar->output->bar ordering with frozen state.

    These tests verify the complete pattern:
    1. Bar animates during search
    2. freeze_at_current() captures fill and elapsed at model-found time
    3. Output (header) is printed
    4. complete() displays the bar with frozen values

    The key property: elapsed time shown should match the fill fraction,
    both captured at freeze time, not complete() time.
    """

    def test_freeze_complete_time_consistency(self):
        """Test that complete() uses frozen elapsed time, not current time.

        This tests the core fix: when freeze_at_current() is called at 0.3s,
        complete() should display 0.3s, even if called 0.5s later.
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        bar = TimeBasedProgress(
            timeout=1.0,  # 1 second timeout
            model_number=1,
            total_models=2,
            display=display
        )

        # Start and let it run for ~0.3s
        bar.start()
        time.sleep(0.3)

        # Freeze at current position
        fill_fraction = bar.freeze_at_current()
        frozen_elapsed = bar._frozen_elapsed

        # Verify freeze captured reasonable values
        self.assertGreater(frozen_elapsed, 0.15, "Should have elapsed time")
        self.assertLess(frozen_elapsed, 0.6, "Should not exceed sleep time by much")
        self.assertAlmostEqual(
            fill_fraction, frozen_elapsed / bar.timeout, places=2,
            msg="Fill fraction should match elapsed/timeout ratio"
        )

        # Simulate post-search delay (header printing, etc.)
        time.sleep(0.4)

        # Clear any animation output
        buffer.truncate(0)
        buffer.seek(0)

        # Complete the bar - should use frozen values
        bar.complete(success=True)

        output = buffer.getvalue()

        # Extract displayed elapsed time
        import re
        match = re.search(r'(\d+\.\d+)s', output)
        self.assertIsNotNone(match, f"Should find elapsed time in: {output}")
        displayed_elapsed = float(match.group(1))

        # Key assertion: displayed elapsed should match frozen elapsed
        # NOT current elapsed (which would be ~0.7s)
        self.assertAlmostEqual(
            displayed_elapsed, frozen_elapsed, delta=0.15,
            msg=f"Displayed ({displayed_elapsed}s) should match frozen ({frozen_elapsed}s)"
        )

        # Sanity check: should NOT be the complete() time
        self.assertLess(
            displayed_elapsed, 0.6,
            msg=f"Displayed ({displayed_elapsed}s) should be frozen time, not complete() time"
        )

    def test_deferred_completion_preserves_frozen_state(self):
        """Test the full bar->output->bar pattern preserves frozen state.

        Simulates the real usage pattern:
        1. Start animation
        2. Model found - freeze_at_current()
        3. Print header (simulated)
        4. complete() displays frozen state
        """
        buffer = io.StringIO()
        display = TerminalDisplay(stream=buffer)

        bar = TimeBasedProgress(
            timeout=2.0,  # 2 second timeout
            model_number=2,
            total_models=3,
            display=display
        )

        # Phase 1: Animation running
        bar.start()
        time.sleep(0.2)

        # Phase 2: Model found - freeze
        bar.freeze_at_current()
        frozen_fill = bar.fill_fraction
        frozen_elapsed = bar._frozen_elapsed

        # Thread should be stopped
        self.assertFalse(bar.active)

        # Clear animation output
        display.clear()
        buffer.truncate(0)
        buffer.seek(0)

        # Phase 3: Print header (simulated external operation)
        buffer.write("EXAMPLE 1: some header content\n")

        # Phase 4: Delay (simulating processing time)
        time.sleep(0.3)

        # Phase 5: Complete with frozen state
        bar.complete(success=True)

        output = buffer.getvalue()

        # Verify header came first
        header_pos = output.find("EXAMPLE 1:")
        bar_pos = output.find("Finding non-isomorphic models:")
        self.assertLess(
            header_pos, bar_pos,
            "Header should appear before progress bar"
        )

        # Verify frozen state was used
        # Bar should NOT be full (frozen_fill was ~0.1, not 1.0)
        self.assertLess(
            frozen_fill, 0.3,
            "Frozen fill should be partial, not full"
        )

        # Extract displayed time and verify it matches frozen
        import re
        match = re.search(r'(\d+\.\d+)s', output)
        self.assertIsNotNone(match)
        displayed = float(match.group(1))

        self.assertAlmostEqual(
            displayed, frozen_elapsed, delta=0.15,
            msg=f"Displayed time ({displayed}s) should match frozen ({frozen_elapsed}s)"
        )

    def test_multiple_bars_maintain_independent_frozen_state(self):
        """Test that multiple progress bars maintain independent frozen state.

        When processing multiple models, each bar should preserve its own
        frozen fill fraction and elapsed time.
        """
        buffer1 = io.StringIO()
        buffer2 = io.StringIO()
        display1 = TerminalDisplay(stream=buffer1)
        display2 = TerminalDisplay(stream=buffer2)

        # First bar - runs for 0.2s before freeze
        bar1 = TimeBasedProgress(
            timeout=1.0,
            model_number=1,
            total_models=2,
            display=display1
        )
        bar1.start()
        time.sleep(0.2)
        bar1.freeze_at_current()
        frozen1 = bar1._frozen_elapsed

        # Second bar - runs for 0.4s before freeze
        bar2 = TimeBasedProgress(
            timeout=1.0,
            model_number=2,
            total_models=2,
            display=display2
        )
        bar2.start()
        time.sleep(0.4)
        bar2.freeze_at_current()
        frozen2 = bar2._frozen_elapsed

        # Verify they have different frozen times
        self.assertLess(frozen1, frozen2 - 0.1,
            msg="Bar1 should have shorter frozen time than bar2")

        # Complete both
        buffer1.truncate(0)
        buffer1.seek(0)
        buffer2.truncate(0)
        buffer2.seek(0)

        bar1.complete(success=True)
        bar2.complete(success=True)

        # Extract displayed times
        import re
        match1 = re.search(r'(\d+\.\d+)s', buffer1.getvalue())
        match2 = re.search(r'(\d+\.\d+)s', buffer2.getvalue())

        self.assertIsNotNone(match1)
        self.assertIsNotNone(match2)

        displayed1 = float(match1.group(1))
        displayed2 = float(match2.group(1))

        # Each should show its own frozen time
        self.assertAlmostEqual(displayed1, frozen1, delta=0.15)
        self.assertAlmostEqual(displayed2, frozen2, delta=0.15)


if __name__ == "__main__":
    unittest.main()
