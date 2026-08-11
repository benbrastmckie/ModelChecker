#!/usr/bin/env python3
"""Seeded, paired measurement harness for oracle per-formula Z3 solve cost.

Task 144 Phase 1: drives ``BimodalSemantics`` / ``ModelConstraints`` /
``BimodalStructure`` directly, exactly as ``Z3OracleProvider.find_countermodel``
does (see ``oracle/bimodal_logic/provider.py``), bypassing pytest so the Z3
``smt.random_seed`` / ``sat.random_seed`` parameters are controllable per run.

This script does NOT modify ``code/src/model_checker/solver/z3_adapter.py``.
Seeds are injected via ``z3.set_param(...)`` in this harness only, immediately
before each solve, matching the plan's "seeds pinned in the measurement
harness only" constraint.

Usage (inside ``nix develop``)::

    python specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py \\
        --formula and_box_next --seeds 0,1,2,3,4 --repeats-at-seed0 2 \\
        --out specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.json

Supports append/resume: if ``--out`` already exists and contains a JSON
results file, previously recorded (formula, seed, repeat_index) runs are
skipped and only missing runs are executed, so an interrupted round resumes
rather than restarts.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_ROOT = REPO_ROOT / "oracle"
CODE_SRC = REPO_ROOT / "code" / "src"

for p in (str(ORACLE_ROOT), str(CODE_SRC)):
    if p not in sys.path:
        sys.path.insert(0, p)

import z3  # noqa: E402

from model_checker import ModelConstraints, Syntax  # noqa: E402
from model_checker.theory_lib.bimodal import (  # noqa: E402
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
    bimodal_operators,
)
from model_checker.utils.context import isolated_z3_context  # noqa: E402

from bimodal_logic.translation import (  # noqa: E402
    json_to_prefix,
    prefix_to_infix,
    temporal_depth,
)


##############################################################################
# JSON formula helpers (mirrors oracle/bimodal_logic/tests/test_oracle_interface.py)
##############################################################################

def _atom(name: str) -> dict:
    return {"tag": "atom", "name": name}


def _neg(arg: dict) -> dict:
    return {"tag": "neg", "arg": arg}


def _and(left: dict, right: dict) -> dict:
    return {"tag": "and", "left": left, "right": right}


def _box(child: dict) -> dict:
    return {"tag": "box", "child": child}


def _diamond(arg: dict) -> dict:
    return {"tag": "diamond", "arg": arg}


def _next(arg: dict) -> dict:
    return {"tag": "next", "arg": arg}


def _imp(left: dict, right: dict) -> dict:
    return {"tag": "imp", "left": left, "right": right}


A = _atom("A")
B = _atom("B")


# Each target maps to a list of (name, formula_json, timeout_ms) sub-solves,
# matching exactly what the corresponding pytest test in
# oracle/bimodal_logic/tests/test_oracle_interface.py exercises. Most targets
# have a single sub-solve; "all_sat_task_relation_ternary" replicates all 5
# sub-solves of TestTernarySerializationAll.test_all_sat_task_relation_ternary
# because the slow one (next_A) is only representative when measured in the
# same shape as the real test (see research report section 4).
TARGETS = {
    "and_box_next": [
        ("and_box_next", _and(_box(A), _next(B)), 60000),
    ],
    "and_all_future_neg": [
        ("and_all_future_neg", _and(_neg(A), _next(B)), 60000),
    ],
    "all_sat_task_relation_ternary": [
        ("atom_A", A, 10000),
        ("imp_A_B", _imp(A, B), 10000),
        ("and_A_B", _and(A, B), 10000),
        ("diamond_A", _diamond(A), 10000),
        ("next_A", _next(A), 180000),
    ],
}


##############################################################################
# Single solve, mirroring Z3OracleProvider.find_countermodel's pipeline
##############################################################################

def run_single_solve(formula_json: dict, timeout_ms: int, seed: int) -> dict:
    """Run one solve with a pinned Z3 seed; return measured stats.

    Mirrors ``Z3OracleProvider.find_countermodel`` (oracle/bimodal_logic/provider.py)
    exactly: same M formula, same settings dict shape, same isolated Z3
    context usage. Seeds are set via ``z3.set_param`` immediately before the
    isolated context is entered so the fresh ``z3.Context()`` created inside
    picks up the pinned values (Z3's global param table is process-global,
    not tied to a particular Context instance).
    """
    depth = temporal_depth(formula_json)
    M = max(depth + 2, 3)

    prefix = json_to_prefix(formula_json)
    infix = prefix_to_infix(prefix)

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

    # Pin seeds in the harness only -- never in z3_adapter.py.
    z3.set_param("smt.random_seed", seed)
    z3.set_param("sat.random_seed", seed)

    wall_start = time.time()
    with isolated_z3_context():
        semantics = BimodalSemantics(settings)
        syntax = Syntax([], [infix], bimodal_operators)
        model_constraints = ModelConstraints(
            settings, syntax, semantics, BimodalProposition
        )
        structure = BimodalStructure(model_constraints, settings)
        wall_seconds = time.time() - wall_start

        rlimit = None
        stats_str = None
        if structure.stored_solver is not None:
            try:
                # structure.stored_solver is a Z3SolverAdapter, not a raw
                # z3.Solver -- statistics() lives on the wrapped raw solver.
                raw_solver = structure.stored_solver.raw_solver
                stats = raw_solver.statistics()
                stats_str = str(stats)
                # z3.Statistics supports mapping-like access; 'rlimit count'
                # is the key used by Z3's own stats formatter.
                for key in ("rlimit count", "rlimit_count"):
                    try:
                        rlimit = stats.get_key_value(key)
                        break
                    except Exception:
                        continue
                if rlimit is None:
                    # Fallback: parse from the string representation.
                    for line in stats_str.splitlines():
                        if "rlimit count" in line:
                            parts = line.strip().split()
                            rlimit = int(parts[-1])
                            break
            except Exception as exc:  # pragma: no cover - diagnostic path
                stats_str = f"<stats unavailable: {exc}>"

        return {
            "seed": seed,
            "timeout": bool(structure.timeout),
            "z3_model_status": structure.z3_model_status,
            "rlimit": rlimit,
            "wall_seconds": round(wall_seconds, 4),
            "reported_runtime": structure.z3_model_runtime,
            "temporal_depth": depth,
            "M": M,
            "stats_raw": stats_str,
        }


def run_target(target_name: str, seed: int, repeat_index: int) -> dict:
    """Run all sub-solves for a target formula at a given seed; aggregate."""
    sub_solves = TARGETS[target_name]
    sub_results = []
    total_rlimit = 0
    total_wall = 0.0
    any_rlimit_missing = False
    for sub_name, formula_json, timeout_ms in sub_solves:
        r = run_single_solve(formula_json, timeout_ms, seed)
        r["sub_name"] = sub_name
        sub_results.append(r)
        if r["rlimit"] is None:
            any_rlimit_missing = True
        else:
            total_rlimit += r["rlimit"]
        total_wall += r["wall_seconds"]

    return {
        "formula": target_name,
        "seed": seed,
        "repeat_index": repeat_index,
        "rlimit": None if any_rlimit_missing else total_rlimit,
        "wall_seconds": round(total_wall, 4),
        "sub_results": sub_results,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }


##############################################################################
# Resume / append support
##############################################################################

def load_existing(out_path: Path) -> list:
    if not out_path.exists():
        return []
    try:
        with open(out_path) as f:
            data = json.load(f)
        return data.get("runs", [])
    except (json.JSONDecodeError, OSError):
        return []


def already_done(runs: list, formula: str, seed: int, repeat_index: int) -> bool:
    for r in runs:
        if (
            r.get("formula") == formula
            and r.get("seed") == seed
            and r.get("repeat_index") == repeat_index
        ):
            return True
    return False


def summarize(runs: list, formula: str) -> dict:
    rows = [r for r in runs if r["formula"] == formula and r.get("rlimit") is not None]
    if not rows:
        return {"formula": formula, "n": 0}
    rlimits = [r["rlimit"] for r in rows]
    walls = [r["wall_seconds"] for r in rows]
    per_seed = sorted(
        (r["seed"], r["repeat_index"], r["rlimit"], r["wall_seconds"]) for r in rows
    )
    return {
        "formula": formula,
        "n": len(rows),
        "median_rlimit": statistics.median(rlimits),
        "max_rlimit": max(rlimits),
        "median_wall": statistics.median(walls),
        "max_wall": max(walls),
        "per_seed": per_seed,
    }


def write_markdown_summary(out_json_path: Path, md_path: Path, targets: list, runs: list) -> None:
    lines = ["# Oracle Solve Cost Measurement Summary", ""]
    lines.append(f"Source: `{out_json_path.name}`")
    lines.append("")
    for target in targets:
        summ = summarize(runs, target)
        lines.append(f"## {target}")
        lines.append("")
        if summ["n"] == 0:
            lines.append("No completed runs.")
            lines.append("")
            continue
        lines.append(f"- n = {summ['n']}")
        lines.append(f"- median(rlimit) = {summ['median_rlimit']:.0f}")
        lines.append(f"- max(rlimit) = {summ['max_rlimit']}")
        lines.append(f"- median(wall) = {summ['median_wall']:.2f}s")
        lines.append(f"- max(wall) = {summ['max_wall']:.2f}s")
        lines.append("")
        lines.append("| seed | repeat | rlimit | wall (s) |")
        lines.append("|---|---|---|---|")
        for seed, repeat_index, rlimit, wall in summ["per_seed"]:
            lines.append(f"| {seed} | {repeat_index} | {rlimit} | {wall:.2f} |")
        lines.append("")
    md_path.write_text("\n".join(lines))


##############################################################################
# Main
##############################################################################

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--formula",
        required=True,
        choices=sorted(TARGETS.keys()) + ["all"],
        help="Target formula name, or 'all' to run every target.",
    )
    parser.add_argument(
        "--seeds",
        default="0,1,2,3,4",
        help="Comma-separated list of seeds (default: 0,1,2,3,4).",
    )
    parser.add_argument(
        "--repeats-at-seed0",
        type=int,
        default=2,
        help="Additional repeats at seed 0 to quantify within-seed variance.",
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Path to JSON results file (append/resume if it already exists).",
    )
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",") if s.strip() != ""]
    targets = list(TARGETS.keys()) if args.formula == "all" else [args.formula]

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    runs = load_existing(out_path)

    # Build the full (formula, seed, repeat_index) plan: one run per seed,
    # plus repeats-at-seed0 additional runs at seed 0 (repeat_index 1..N).
    plan = []
    for target in targets:
        for seed in seeds:
            plan.append((target, seed, 0))
        for i in range(1, args.repeats_at_seed0 + 1):
            plan.append((target, 0, i))

    print(f"[bench] plan has {len(plan)} runs across targets={targets}, seeds={seeds}, "
          f"repeats_at_seed0={args.repeats_at_seed0}")
    print(f"[bench] {len(runs)} runs already recorded in {out_path}")

    for target, seed, repeat_index in plan:
        if already_done(runs, target, seed, repeat_index):
            print(f"[bench] SKIP (already done) formula={target} seed={seed} repeat={repeat_index}")
            continue
        print(f"[bench] RUN formula={target} seed={seed} repeat={repeat_index} ...", flush=True)
        t0 = time.time()
        result = run_target(target, seed, repeat_index)
        elapsed = time.time() - t0
        print(
            f"[bench]   -> rlimit={result['rlimit']} wall={result['wall_seconds']:.2f}s "
            f"(harness elapsed {elapsed:.2f}s)"
        )
        runs.append(result)
        # Persist after every run so an interruption loses at most one run.
        with open(out_path, "w") as f:
            json.dump({"runs": runs}, f, indent=2)

    print("\n[bench] === Summary ===")
    for target in targets:
        summ = summarize(runs, target)
        print(f"[bench] {target}: {summ}")

    md_path = out_path.with_suffix(".md")
    write_markdown_summary(out_path, md_path, targets, runs)
    print(f"[bench] wrote markdown summary to {md_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
