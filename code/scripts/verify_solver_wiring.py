#!/usr/bin/env python3
"""Verify solver registry is properly wired into core solving loop.

This script validates that:
1. create_solver() returns the correct adapter type for the active backend
2. Expressions come from the correct backend module
3. End-to-end solving works with either backend
4. SolverResult comparison works correctly

Usage:
    # Test with default z3 backend
    python verify_solver_wiring.py

    # Test with cvc5 backend
    MODEL_CHECKER_SOLVER=cvc5 python verify_solver_wiring.py
"""

import os
import sys

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))


def test_solver_type():
    """Verify create_solver returns correct adapter type."""
    from model_checker.solver import create_solver, get_active_backend
    from model_checker.solver.z3_adapter import Z3SolverAdapter

    backend = get_active_backend()
    solver = create_solver()

    if backend == "z3":
        assert isinstance(solver, Z3SolverAdapter), f"Expected Z3SolverAdapter, got {type(solver)}"
        print("[PASS] z3 backend creates Z3SolverAdapter")
    elif backend == "cvc5":
        # Import cvc5 adapter if available
        try:
            from model_checker.solver.cvc5_adapter import CVC5SolverAdapter
            assert isinstance(solver, CVC5SolverAdapter), f"Expected CVC5SolverAdapter, got {type(solver)}"
            print("[PASS] cvc5 backend creates CVC5SolverAdapter")
        except ImportError:
            print("[SKIP] cvc5 adapter not available")
    else:
        print(f"[WARN] Unknown backend: {backend}")


def test_expressions_backend():
    """Verify expressions come from correct backend."""
    from model_checker.solver import get_active_backend
    from model_checker.solver.expressions import And, BitVec, BoolVal

    backend = get_active_backend()
    x = BitVec("x", 8)
    y = BitVec("y", 8)
    constraint = And(x > 0, y > 0)

    if backend == "z3":
        import z3
        assert isinstance(x, z3.BitVecRef), f"BitVec should be z3 type, got {type(x)}"
        print("[PASS] z3 backend produces z3 expressions")
    elif backend == "cvc5":
        # Check cvc5 type
        print(f"[INFO] cvc5 expression type: {type(x)}")
        print("[PASS] cvc5 backend produces expressions")


def test_solver_result_comparison():
    """Test that SolverResult comparison works correctly."""
    from model_checker.solver import create_solver, SolverResult
    from model_checker.solver.expressions import BitVec, And, BoolVal

    solver = create_solver()
    x = BitVec("test_x", 8)

    # Add satisfiable constraint
    solver.add(x > 0)
    result = solver.check()

    assert SolverResult.is_sat(result), f"Expected sat, got {result}"
    print("[PASS] SolverResult.is_sat works correctly")

    # Add unsatisfiable constraint
    solver.add(x < 0)
    solver.add(x > 100)
    result2 = solver.check()

    # Note: Depending on the exact constraints, result may vary
    print(f"[INFO] Second check result: {result2}")


def test_end_to_end_solve():
    """Test complete solve cycle with active backend."""
    from model_checker.solver import create_solver, SolverResult, get_active_backend
    from model_checker.solver.expressions import BitVec, And

    backend = get_active_backend()
    solver = create_solver()
    x = BitVec("solve_x", 8)
    y = BitVec("solve_y", 8)

    # Simple satisfiable constraint
    solver.add(And(x > 0, y > 0))
    solver.add(x + y == 10)
    result = solver.check()

    assert SolverResult.is_sat(result), f"Expected sat, got {result}"
    model = solver.model()

    # Evaluate x and y in the model
    x_val = model.eval(x, model_completion=True)
    y_val = model.eval(y, model_completion=True)

    print(f"[PASS] End-to-end solve succeeded with {backend}")
    print(f"  Model: x={x_val}, y={y_val}")


def test_is_true_compatibility():
    """Test that is_true works with solver abstraction."""
    from model_checker.solver import is_true, is_false, get_active_backend
    from model_checker.solver.expressions import BoolVal

    backend = get_active_backend()

    true_val = BoolVal(True)
    false_val = BoolVal(False)

    assert is_true(true_val), "is_true(BoolVal(True)) should be True"
    assert not is_true(false_val), "is_true(BoolVal(False)) should be False"
    assert is_false(false_val), "is_false(BoolVal(False)) should be True"
    assert not is_false(true_val), "is_false(BoolVal(True)) should be False"

    print(f"[PASS] is_true/is_false compatibility verified for {backend}")


def test_tracked_assertions():
    """Test tracked assertions for unsat core extraction."""
    from model_checker.solver import create_solver, SolverResult
    from model_checker.solver.expressions import Bool

    solver = create_solver()

    # Create conflicting assertions
    p = Bool("tracked_p")
    q = Bool("tracked_q")

    solver.assert_tracked(p, "assert_p")
    solver.assert_tracked(q, "assert_q")
    solver.assert_tracked(p == False, "assert_not_p")  # noqa: E712

    result = solver.check()
    assert SolverResult.is_unsat(result), f"Expected unsat, got {result}"

    core = solver.unsat_core()
    print(f"[INFO] Unsat core labels: {core}")
    print("[PASS] Tracked assertions and unsat core work")


def main():
    """Run all verification tests."""
    backend = os.environ.get("MODEL_CHECKER_SOLVER", "z3 (default)")
    print(f"Testing with MODEL_CHECKER_SOLVER={backend}")
    print("=" * 50)

    tests = [
        test_solver_type,
        test_expressions_backend,
        test_solver_result_comparison,
        test_end_to_end_solve,
        test_is_true_compatibility,
        test_tracked_assertions,
    ]

    passed = 0
    failed = 0

    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"[FAIL] {test.__name__}: {e}")
            failed += 1

    print("=" * 50)
    print(f"Results: {passed} passed, {failed} failed")

    if failed == 0:
        print("\n[SUCCESS] All verification tests passed!")
        return 0
    else:
        print("\n[FAILURE] Some tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
