#!/usr/bin/env python
"""Standalone, foreground Z3 solve-cost probe CLI.

Solves one oracle formula through a settings-dict-identical replication of
`Z3OracleProvider.find_countermodel()`'s pipeline (see
`oracle/bimodal_logic/provider.py`) and reports wall time, decided/undecided,
and the Z3 `rlimit` resource-unit statistic consumed for the draw.

Why a replication rather than calling `find_countermodel()` directly: that
function (1) raises `OracleTimeoutError` on an undecided solve rather than
returning a record, and (2) returns only a serialized countermodel dict (or
None), never the `BimodalStructure` needed to read the rlimit statistic.
Building the settings dict and pipeline inline -- using the exact same keys
and values `find_countermodel()` uses (`N=2`, `M=max(depth+2,3)`,
`temporal_depth`, `contingent=False`, `disjoint=False`, `max_time`,
`expectation=True`, `solver='z3'`) inside `isolated_z3_context()` -- keeps a
probed number a number about the real oracle path, without either problem.

rlimit access path: `structure.stored_solver.raw_solver.statistics()`.
`stored_solver` survives `ModelDefaults._cleanup_solver_resources()` (that
method only clears `.solver` and `.z3_model`, never `.stored_solver`), and
`Z3SolverAdapter.raw_solver` is a **property**, not a method -- read it
without call parentheses.

Usage:
    PYTHONPATH=code/src python oracle/probe_solve_cost.py \\
        --formula-name NAME [--timeout-ms MS] [--seed N] [--repeat N]

Formula registry (--formula-name):
    atemporal_and_neg          and(A, neg(B))            -- atemporal, sub-second
    mixed_and_all_future_neg   and(neg(A), next(B))      -- test_mixed_and_all_future_neg's formula
    mixed_or_diamond_prev      or(diamond(A), prev(B))   -- test_mixed_or_diamond_prev's formula

Every draw emits one JSON record to stdout: formula_name, draw_index,
wall_s, decided, rlimit, z3_version, seed, pythonhashseed, timeout_ms.

Exit codes:
    0  All draws completed (decided or cleanly recorded as undecided).
    2  Operational error (unknown --formula-name, import failure, or similar).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

_ORACLE_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _ORACLE_DIR.parent
_CODE_SRC_DIR = _REPO_ROOT / "code" / "src"

# Ensure both the `bimodal_logic` package (rooted at oracle/) and the
# `model_checker` package are importable, independent of the caller's cwd or
# PYTHONPATH -- mirrors oracle/scan_runner.py's path-insertion approach.
for _p in (_ORACLE_DIR, _CODE_SRC_DIR):
    _p_str = str(_p)
    if _p_str not in sys.path:
        sys.path.insert(0, _p_str)


##############################################################################
# Formula registry -- minimal JSON-formula builders, mirroring the tag schema
# documented in bimodal_logic/translation.py (kept local rather than imported
# from the test module, since this is a standalone CLI, not a test).
##############################################################################

def _atom(name: str) -> dict:
    return {"tag": "atom", "name": name}


def _neg(arg: dict) -> dict:
    return {"tag": "neg", "arg": arg}


def _and(left: dict, right: dict) -> dict:
    return {"tag": "and", "left": left, "right": right}


def _or(left: dict, right: dict) -> dict:
    return {"tag": "or", "left": left, "right": right}


def _diamond(arg: dict) -> dict:
    return {"tag": "diamond", "arg": arg}


def _next(arg: dict) -> dict:
    return {"tag": "next", "arg": arg}


def _prev(arg: dict) -> dict:
    return {"tag": "prev", "arg": arg}


_A = _atom("A")
_B = _atom("B")

FORMULA_REGISTRY: dict[str, dict] = {
    "atemporal_and_neg": _and(_A, _neg(_B)),
    "mixed_and_all_future_neg": _and(_neg(_A), _next(_B)),
    "mixed_or_diamond_prev": _or(_diamond(_A), _prev(_B)),
}


def run_probe(formula_name: str, timeout_ms: int, seed: int | None) -> dict:
    """Solve `FORMULA_REGISTRY[formula_name]` once and return a JSON-ready record.

    Never raises `OracleTimeoutError`-equivalent: an undecided solve is
    reported as `decided: False`, matching the harness's job of measuring
    solve cost, not enforcing a budget.

    Args:
        formula_name: Key into FORMULA_REGISTRY.
        timeout_ms: Wall-clock solver budget in milliseconds (max_time).
        seed: If not None, pins `sat.random_seed`/`smt.random_seed` to this
            value before solving (probe-only; production never sets a seed
            -- see the plan's Non-Goals). If None, no seed param is touched,
            so Z3's own default-seed behavior governs the draw.

    Returns:
        A dict with: formula_name, timeout_ms, seed ("default" or the int),
        wall_s, decided (bool), rlimit (int or None if unreadable),
        z3_version, pythonhashseed.
    """
    if formula_name not in FORMULA_REGISTRY:
        raise KeyError(
            f"Unknown --formula-name {formula_name!r}; "
            f"known names: {sorted(FORMULA_REGISTRY)}"
        )
    formula_json = FORMULA_REGISTRY[formula_name]

    from bimodal_logic.translation import (
        json_to_prefix,
        prefix_to_infix,
        temporal_depth,
    )
    from model_checker.utils.context import isolated_z3_context
    from model_checker import ModelConstraints, Syntax
    from model_checker.theory_lib.bimodal import (
        BimodalSemantics,
        BimodalProposition,
        BimodalStructure,
        bimodal_operators,
    )
    import z3

    depth = temporal_depth(formula_json)
    M = max(depth + 2, 3)
    prefix = json_to_prefix(formula_json)
    infix = prefix_to_infix(prefix)

    # Settings dict replicated verbatim from
    # Z3OracleProvider.find_countermodel() -- see this module's docstring.
    settings = {
        "N": 2,
        "M": M,
        "temporal_depth": depth,
        "contingent": False,
        "disjoint": False,
        "max_time": timeout_ms / 1000.0,
        "expectation": True,
        "solver": "z3",
    }

    if seed is not None:
        z3.set_param("sat.random_seed", seed)
        z3.set_param("smt.random_seed", seed)

    wall_start = time.time()
    rlimit = None
    decided = None
    with isolated_z3_context():
        syntax = Syntax([], [infix], bimodal_operators)
        semantics = BimodalSemantics(settings)
        model_constraints = ModelConstraints(
            settings, syntax, semantics, BimodalProposition
        )
        structure = BimodalStructure(model_constraints, settings)

        decided = not structure.timeout

        # Read rlimit before anything else can drop the reference chain.
        # See module docstring: stored_solver survives cleanup; raw_solver
        # is a property, not a method.
        try:
            stats = structure.stored_solver.raw_solver.statistics()
            rlimit = stats.get_key_value("rlimit count")
        except Exception:
            rlimit = None

    wall_s = round(time.time() - wall_start, 4)

    return {
        "formula_name": formula_name,
        "timeout_ms": timeout_ms,
        "seed": seed if seed is not None else "default",
        "wall_s": wall_s,
        "decided": decided,
        "rlimit": rlimit,
        "z3_version": z3.get_version_string(),
        "pythonhashseed": os.environ.get("PYTHONHASHSEED"),
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    # --formula-name deliberately has no `choices=` constraint: an unknown
    # name is validated in main() so it can return this module's documented
    # exit code 2 (operational error) rather than argparse's exit code 2
    # accidentally coinciding for a different reason.
    parser = argparse.ArgumentParser(
        description="Standalone foreground Z3 solve-cost probe.",
    )
    parser.add_argument(
        "--formula-name", type=str, required=True,
        help=f"Formula to probe. Known names: {sorted(FORMULA_REGISTRY)}.",
    )
    parser.add_argument(
        "--timeout-ms", type=int, default=5000,
        help="Wall-clock solver budget in milliseconds (default: 5000).",
    )
    parser.add_argument(
        "--seed", type=int, default=None,
        help="Pin sat.random_seed/smt.random_seed to this value "
             "(default: unset -- Z3's own default-seed behavior).",
    )
    parser.add_argument(
        "--repeat", type=int, default=1,
        help="Number of draws to run, each emitting its own JSON record "
             "(default: 1).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)

    if args.formula_name not in FORMULA_REGISTRY:
        print(
            f"# ERROR: unknown --formula-name {args.formula_name!r}; "
            f"known names: {sorted(FORMULA_REGISTRY)}",
            flush=True,
        )
        return 2

    try:
        for draw_index in range(args.repeat):
            record = run_probe(
                formula_name=args.formula_name,
                timeout_ms=args.timeout_ms,
                seed=args.seed,
            )
            record["draw_index"] = draw_index
            print(json.dumps(record), flush=True)
    except Exception as exc:  # operational error, not a probe verdict
        print(f"# ERROR: probe failed: {exc!r}", flush=True)
        return 2

    return 0


if __name__ == "__main__":
    sys.exit(main())
