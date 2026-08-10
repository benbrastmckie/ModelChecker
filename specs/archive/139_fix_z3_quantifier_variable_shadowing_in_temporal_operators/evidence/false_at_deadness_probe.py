"""Phase 5 deadness proof: instrumented invocation counters for the five
quantified operators' `false_at` methods in bimodal/operators.py.

Research finding (report 01, section 2): `BimodalSemantics.false_at`
(semantic/core.py) is unconditionally `z3.Not(self.true_at(...))` and never
dispatches to `operator.false_at`. The five quantified operators'
`false_at` methods (NecessityOperator, FutureOperator, PastOperator,
UntilOperator, SinceOperator) are therefore hypothesized dead code -- no
call path from `find_countermodel()` should ever reach them.

This script monkeypatches each of those five methods with a counting
wrapper IN-PROCESS (not a committed change -- this file is a standalone
probe, run directly, never imported by the real test/source tree), then
runs pytest.main() in-process (so the monkeypatch is visible to the tests)
against:
  1. The full bimodal package test suite (unit + integration).
  2. The oracle gating suite (test_soundness_regression.py and
     test_encoding_nondegeneracy.py -- the fast, non-`slow` oracle tests).

Per the plan's gate: if ANY counter is non-zero afterward, the deletion in
Phase 5 is OFF, and the caller must be identified from the recorded stack
trace.

Usage:
    PYTHONPATH=code/src:oracle python3 false_at_deadness_probe.py
"""

from __future__ import annotations

import sys
import traceback
from pathlib import Path

_THIS_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _THIS_DIR.parents[2]
_SRC_DIR = _REPO_ROOT / "code" / "src"
_ORACLE_DIR = _REPO_ROOT / "oracle"
for _p in (_SRC_DIR, _ORACLE_DIR):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

import pytest  # noqa: E402


def install_counters():
    """Monkeypatch the five quantified operators' false_at methods with
    counting wrappers. Returns (counts, call_sites) dicts, mutated in place
    as calls occur.
    """
    from model_checker.theory_lib.bimodal import operators as ops_mod

    targets = [
        "NecessityOperator",
        "FutureOperator",
        "PastOperator",
        "UntilOperator",
        "SinceOperator",
    ]
    counts = {name: 0 for name in targets}
    call_sites: dict[str, list[str]] = {name: [] for name in targets}

    for name in targets:
        cls = getattr(ops_mod, name)
        orig = cls.false_at

        def make_wrapper(orig_method, counter_name):
            def wrapper(self, *args, **kwargs):
                counts[counter_name] += 1
                stack = "".join(traceback.format_stack(limit=10))
                call_sites[counter_name].append(stack)
                return orig_method(self, *args, **kwargs)
            return wrapper

        cls.false_at = make_wrapper(orig, name)

    return counts, call_sites


def main() -> None:
    counts, call_sites = install_counters()

    suites = [
        (
            "bimodal package (unit + integration)",
            [str(_SRC_DIR / "model_checker" / "theory_lib" / "bimodal" / "tests"), "-q"],
        ),
        (
            "oracle gating suite (soundness_regression + encoding_nondegeneracy)",
            [
                str(_ORACLE_DIR / "bimodal_logic" / "tests" / "test_soundness_regression.py"),
                str(_ORACLE_DIR / "bimodal_logic" / "tests" / "test_encoding_nondegeneracy.py"),
                "-q",
            ],
        ),
    ]

    exit_codes = {}
    for label, args in suites:
        print("=" * 70)
        print(f"Running: {label}")
        print("=" * 70)
        exit_code = pytest.main(args)
        exit_codes[label] = int(exit_code)
        print(f"[{label}] exit code: {exit_code}")
        print(f"[{label}] cumulative counters so far: {counts}")

    print("=" * 70)
    print("FINAL false_at INVOCATION COUNTERS:")
    for name, count in counts.items():
        print(f"  {name}.false_at: {count}")
        if count > 0:
            print(f"    First recorded call site:\n{call_sites[name][0]}")
    print("=" * 70)

    total = sum(counts.values())
    if total == 0:
        print("DEADNESS PROOF: ALL COUNTERS ZERO. Phase 5 deletion is authorized.")
    else:
        print("DEADNESS PROOF FAILED: at least one false_at method was invoked.")
        print("Phase 5 deletion is OFF. Fall back to keep-and-fix for invoked methods.")

    print(f"Suite exit codes: {exit_codes}")


if __name__ == "__main__":
    main()
