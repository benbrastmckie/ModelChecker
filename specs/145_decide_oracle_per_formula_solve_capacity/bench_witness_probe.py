#!/usr/bin/env python3
"""Phase 1 confirmation probes: substitute-witness candidates + BM_CM_4 re-probe.

Copy of the methodology in
specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py: drives
``BimodalSemantics`` / ``ModelConstraints`` / ``BimodalStructure`` directly,
exactly as ``Z3OracleProvider.find_countermodel`` does, with Z3 seeds pinned
via ``z3.set_param`` in this harness only. rlimit is the primary metric, wall
clock secondary.

Targets:
- ``witness_and_neg_next``: primary substitute-witness candidate
  ``_and(_neg(A), _next(B))`` in the ternary-test context (temporal depth 1,
  M=3, N=2, non-contingent), 180 s probe budget.
- ``witness_some_future``: secondary candidate ``_some_future(A)``, same
  context, 180 s probe budget.
- ``bm_cm_4``: the BM_CM_4 countermodel solve (premises ``\\Diamond A``,
  conclusions ``\\past A``, N=2, M=2, contingent=True), 120 s probe budget.

Usage (inside ``nix develop``)::

    python specs/145_decide_oracle_per_formula_solve_capacity/bench_witness_probe.py \
        --formula witness_and_neg_next --seeds 1,2,3,4,5,6,7 \
        --out specs/145_decide_oracle_per_formula_solve_capacity/baselines/03_witness-candidate-probe.json
"""

from __future__ import annotations

import argparse
import json
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


def _atom(name: str) -> dict:
    return {"tag": "atom", "name": name}


def _neg(arg: dict) -> dict:
    return {"tag": "neg", "arg": arg}


def _and(left: dict, right: dict) -> dict:
    return {"tag": "and", "left": left, "right": right}


def _next(arg: dict) -> dict:
    return {"tag": "next", "arg": arg}


def _some_future(arg: dict) -> dict:
    return {"tag": "some_future", "arg": arg}


A = _atom("A")
B = _atom("B")


# JSON-pipeline targets: (name, formula_json, timeout_ms)
JSON_TARGETS = {
    "witness_and_neg_next": [
        ("witness_and_neg_next", _and(_neg(A), _next(B)), 180000),
    ],
    "witness_some_future": [
        ("witness_some_future", _some_future(A), 180000),
    ],
}

# Premise/conclusion targets: (premises, conclusions, settings) with the
# probe budget in max_time.
PC_TARGETS = {
    "bm_cm_4": {
        "premises": ["\\Diamond A"],
        "conclusions": ["\\past A"],
        "settings": {
            "N": 2,
            "M": 2,
            "contingent": True,
            "disjoint": False,
            "max_time": 120.0,
            "expectation": True,
            "solver": "z3",
        },
    },
}

ALL_TARGETS = sorted(JSON_TARGETS) + sorted(PC_TARGETS)


def _extract_stats(structure, wall_seconds: float, depth: int, M: int) -> dict:
    rlimit = None
    stats_str = None
    if structure.stored_solver is not None:
        try:
            raw_solver = structure.stored_solver.raw_solver
            stats = raw_solver.statistics()
            stats_str = str(stats)
            for key in ("rlimit count", "rlimit_count"):
                try:
                    rlimit = stats.get_key_value(key)
                    break
                except Exception:
                    continue
            if rlimit is None:
                for line in stats_str.splitlines():
                    if "rlimit count" in line:
                        rlimit = int(line.strip().split()[-1])
                        break
        except Exception as exc:  # pragma: no cover
            stats_str = f"<stats unavailable: {exc}>"
    return {
        "timeout": bool(structure.timeout),
        "z3_model_status": structure.z3_model_status,
        "rlimit": rlimit,
        "wall_seconds": round(wall_seconds, 4),
        "reported_runtime": structure.z3_model_runtime,
        "temporal_depth": depth,
        "M": M,
        "stats_raw": stats_str,
    }


def run_json_solve(formula_json: dict, timeout_ms: int, seed: int) -> dict:
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
        r = _extract_stats(structure, wall_seconds, depth, M)
        r["seed"] = seed
        return r


def run_pc_solve(target: dict, seed: int) -> dict:
    settings = dict(target["settings"])
    z3.set_param("smt.random_seed", seed)
    z3.set_param("sat.random_seed", seed)
    wall_start = time.time()
    with isolated_z3_context():
        semantics = BimodalSemantics(settings)
        syntax = Syntax(target["premises"], target["conclusions"], bimodal_operators)
        model_constraints = ModelConstraints(
            settings, syntax, semantics, BimodalProposition
        )
        structure = BimodalStructure(model_constraints, settings)
        wall_seconds = time.time() - wall_start
        r = _extract_stats(structure, wall_seconds, depth=1, M=settings["M"])
        r["seed"] = seed
        return r


def run_target(target_name: str, seed: int, repeat_index: int) -> dict:
    if target_name in JSON_TARGETS:
        sub_solves = JSON_TARGETS[target_name]
        sub_results = []
        total_rlimit = 0
        total_wall = 0.0
        missing = False
        for sub_name, formula_json, timeout_ms in sub_solves:
            r = run_json_solve(formula_json, timeout_ms, seed)
            r["sub_name"] = sub_name
            sub_results.append(r)
            if r["rlimit"] is None:
                missing = True
            else:
                total_rlimit += r["rlimit"]
            total_wall += r["wall_seconds"]
        return {
            "formula": target_name,
            "seed": seed,
            "repeat_index": repeat_index,
            "rlimit": None if missing else total_rlimit,
            "wall_seconds": round(total_wall, 4),
            "sub_results": sub_results,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
    r = run_pc_solve(PC_TARGETS[target_name], seed)
    return {
        "formula": target_name,
        "seed": seed,
        "repeat_index": repeat_index,
        "rlimit": r["rlimit"],
        "wall_seconds": r["wall_seconds"],
        "sub_results": [dict(r, sub_name=target_name)],
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }


def load_existing(out_path: Path) -> list:
    if not out_path.exists():
        return []
    try:
        with open(out_path) as f:
            return json.load(f).get("runs", [])
    except (json.JSONDecodeError, OSError):
        return []


def already_done(runs: list, formula: str, seed: int, repeat_index: int) -> bool:
    return any(
        r.get("formula") == formula
        and r.get("seed") == seed
        and r.get("repeat_index") == repeat_index
        for r in runs
    )


def summarize(runs: list, formula: str) -> dict:
    rows = [r for r in runs if r["formula"] == formula and r.get("rlimit") is not None]
    if not rows:
        return {"formula": formula, "n": 0}
    rlimits = [r["rlimit"] for r in rows]
    walls = [r["wall_seconds"] for r in rows]
    per_seed = sorted(
        (r["seed"], r["repeat_index"], r["rlimit"], r["wall_seconds"]) for r in rows
    )
    timeouts = [
        r["seed"] for r in rows if any(s.get("timeout") for s in r["sub_results"])
    ]
    return {
        "formula": formula,
        "n": len(rows),
        "median_rlimit": statistics.median(rlimits),
        "max_rlimit": max(rlimits),
        "median_wall": statistics.median(walls),
        "max_wall": max(walls),
        "timeout_seeds": timeouts,
        "per_seed": per_seed,
    }


def write_markdown_summary(out_json_path: Path, md_path: Path, targets: list, runs: list) -> None:
    lines = ["# Witness-Candidate / BM_CM_4 Confirmation Probe Summary", ""]
    lines.append(f"Source: `{out_json_path.name}`")
    lines.append("")
    lines.append(
        "Seeds pinned via `z3.set_param('smt.random_seed'/'sat.random_seed')` in the"
    )
    lines.append(
        "harness only; pipeline mirrors `Z3OracleProvider.find_countermodel`."
    )
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
        lines.append(f"- timeout seeds = {summ['timeout_seeds'] or 'none'}")
        lines.append("")
        lines.append("| seed | repeat | rlimit | wall (s) |")
        lines.append("|---|---|---|---|")
        for seed, repeat_index, rlimit, wall in summ["per_seed"]:
            lines.append(f"| {seed} | {repeat_index} | {rlimit} | {wall:.2f} |")
        lines.append("")
    md_path.write_text("\n".join(lines))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--formula", required=True, choices=ALL_TARGETS + ["all"],
    )
    parser.add_argument("--seeds", default="1,2,3,4,5,6,7")
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",") if s.strip() != ""]
    targets = ALL_TARGETS if args.formula == "all" else [args.formula]

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    runs = load_existing(out_path)

    plan = [(t, s, 0) for t in targets for s in seeds]
    print(f"[probe] plan has {len(plan)} runs across targets={targets}, seeds={seeds}")
    print(f"[probe] {len(runs)} runs already recorded in {out_path}")

    for target, seed, repeat_index in plan:
        if already_done(runs, target, seed, repeat_index):
            print(f"[probe] SKIP formula={target} seed={seed}")
            continue
        print(f"[probe] RUN formula={target} seed={seed} ...", flush=True)
        result = run_target(target, seed, repeat_index)
        print(
            f"[probe]   -> rlimit={result['rlimit']} wall={result['wall_seconds']:.2f}s"
        )
        runs.append(result)
        with open(out_path, "w") as f:
            json.dump({"runs": runs}, f, indent=2)

    print("\n[probe] === Summary ===")
    for target in targets:
        print(f"[probe] {target}: {summarize(runs, target)}")

    md_path = out_path.with_suffix(".md")
    write_markdown_summary(out_path, md_path, targets, runs)
    print(f"[probe] wrote markdown summary to {md_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
