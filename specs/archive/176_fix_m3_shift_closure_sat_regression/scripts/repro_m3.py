#!/usr/bin/env python3
"""Standalone minimal reproduction for the M=3 shift-closure SAT regression.

Reproduces TestShiftClosure::test_shift_closure_on_extracted_worlds_m3
(oracle/bimodal_logic/tests/test_soundness_regression.py) outside pytest,
constructing the same BimodalSemantics/ModelConstraints/BimodalStructure
with the test's exact settings dict.

Usage:
    PYTHONPATH=code/src python3 specs/176_fix_m3_shift_closure_sat_regression/scripts/repro_m3.py [--dump-constraints] [--confirm-structure]

Exit code: 0 on SAT (the solver's own check() result is "sat"), 1 otherwise.
Usable as a `git bisect run` predicate.

Prints one JSON line to stdout with the solver's own reported verdict,
never a derived flag: the raw solver check() result (sat/unsat/unknown),
reason_unknown() where available, statistics (rlimit count, max memory),
and wall-clock seconds.

The default path replicates BimodalStructure.solve()'s exact steps
(same settings, same constraint groups, same timeout) directly against a
solver handle this script keeps alive, since BimodalStructure itself nulls
its solver reference in a `finally` block before __init__ returns --
losing reason_unknown()/statistics() access. Pass --confirm-structure to
additionally construct a real BimodalStructure and assert its
z3_model_status/timeout agree with the raw check (this doubles runtime by
re-solving; use it once to confirm equivalence, not on every run).

--dump-constraints prints the count and top-level shape of each constraint
returned by build_frame_constraints, for Phase 2's encoding-drift audit.
"""

from __future__ import annotations

import json
import sys
import time

SETTINGS = {
    'N': 2,
    'M': 3,
    'temporal_depth': 1,
    'contingent': False,
    'disjoint': False,
    'max_time': 15.0,
    'expectation': True,
    'solver': 'z3',
}


def _frame_constraint_shapes(model_constraints):
    """Return (count, [top-level-shape,...]) for the frame constraints."""
    shapes = []
    for c in model_constraints.frame_constraints:
        try:
            shapes.append(c.decl().name())
        except Exception:
            shapes.append(type(c).__name__)
    return len(model_constraints.frame_constraints), shapes


def main() -> int:
    dump_constraints = "--dump-constraints" in sys.argv
    confirm_structure = "--confirm-structure" in sys.argv

    from model_checker import ModelConstraints, Syntax
    from model_checker.theory_lib.bimodal import (
        BimodalProposition, BimodalStructure, bimodal_operators
    )
    from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
    from model_checker.utils.context import isolated_z3_context
    from model_checker.solver.registry import create_solver
    from model_checker.solver.protocols import SolverResult

    result = {
        "settings": SETTINGS,
    }

    with isolated_z3_context():
        semantics = BimodalSemantics(SETTINGS)
        syntax = Syntax([], ["p"], bimodal_operators)
        model_constraints = ModelConstraints(SETTINGS, syntax, semantics, BimodalProposition)

        if dump_constraints:
            count, shapes = _frame_constraint_shapes(model_constraints)
            result["frame_constraint_count"] = count
            result["frame_constraint_shapes"] = shapes

        # Raw solve replicating BimodalStructure.solve(), but keeping the
        # solver handle alive after check() so reason_unknown()/statistics()
        # remain accessible (BimodalStructure nulls its solver reference in
        # a finally block before __init__ returns).
        solver = create_solver(SETTINGS)
        constraint_groups = [
            (model_constraints.frame_constraints, "frame"),
            (model_constraints.model_constraints, "model"),
            (model_constraints.premise_constraints, "premises"),
            (model_constraints.conclusion_constraints, "conclusions"),
        ]
        for constraints, group_name in constraint_groups:
            for ix, constraint in enumerate(constraints):
                solver.assert_tracked(constraint, f"{group_name}{ix + 1}")

        solver.set_timeout(int(SETTINGS["max_time"] * 1000))
        start = time.time()
        raw_result = solver.check()
        wall_seconds = round(time.time() - start, 4)

        result["raw_check_result"] = raw_result
        result["wall_seconds"] = wall_seconds

        if raw_result == "unknown":
            try:
                result["reason_unknown"] = solver.reason_unknown()
            except Exception as e:
                result["reason_unknown"] = f"<error: {e}>"

        try:
            stats = solver.raw_solver.statistics()
            stats_dict = {k: v for k, v in stats}
            # Z3's Statistics __iter__ yields space-separated keys
            # ("rlimit count", "max memory"), not hyphenated ones.
            result["rlimit_count"] = stats_dict.get("rlimit count")
            result["max_memory"] = stats_dict.get("max memory")
        except Exception as e:
            result["statistics_error"] = str(e)

        if SolverResult.is_sat(raw_result):
            result["verdict"] = "sat"
        elif SolverResult.is_unsat(raw_result):
            result["verdict"] = "unsat"
        else:
            result["verdict"] = "unknown"

        if confirm_structure:
            # Construct BimodalStructure exactly as the test does, on a
            # second, independent solve, to confirm z3_model_status/timeout
            # agree with the raw check above and are read from the same
            # code path the test asserts on.
            structure = BimodalStructure(model_constraints, SETTINGS)
            result["structure_z3_model_status"] = structure.z3_model_status
            result["structure_timeout"] = structure.timeout
            expected_status = SolverResult.is_sat(raw_result)
            expected_timeout = raw_result == "unknown"
            result["structure_agrees_with_raw"] = (
                structure.z3_model_status == expected_status
                and structure.timeout == expected_timeout
            )

    print(json.dumps(result))

    return 0 if result["verdict"] == "sat" else 1


if __name__ == "__main__":
    sys.exit(main())
