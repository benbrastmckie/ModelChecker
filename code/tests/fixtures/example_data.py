"""Shared example settings for edge-case and error-handling tests.

This module provides small, reusable settings dictionaries for tests that
need a valid settings mapping but don't care about its specific contents
(e.g. tests that only exercise formula-list edge cases).
"""

# Generous max_time per the Solver Timing Budgets convention (see
# code/docs/core/TESTING_GUIDE.md section 8.6): Z3 solve times vary widely
# under load, so budgets should be set well above any observed solve time
# rather than tightly against it.
STANDARD_SETTINGS = {
    'N': 2,
    'max_time': 30,
}
