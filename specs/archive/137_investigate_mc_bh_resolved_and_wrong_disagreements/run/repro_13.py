"""Standalone reproduction of the 13 resolved-and-wrong MC/BH temporal-only
disagreements at complexity<=5, with full formula detail (not truncated to 5
like the pytest assertion message).

Run with:
    PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src \
        python3 specs/137_.../reports/repro_13.py
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "oracle"))
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "code" / "src"))
sys.path.insert(0, "/home/benjamin/Projects/BimodalHarness/src")

from bimodal_logic import OracleTimeoutError, Z3OracleProvider  # noqa: E402
from bimodal_harness.oracle.z3_provider import (  # noqa: E402
    Z3OracleProvider as BHZ3OracleProvider,
)

sys.path.insert(
    0,
    str(
        Path(__file__).resolve().parents[3]
        / "oracle"
        / "bimodal_logic"
        / "tests"
    ),
)
from test_cross_oracle_differential import (  # noqa: E402
    _enumerate_primitive_formulas,
    _is_temporal_only,
    _formula_complexity,
)
from bimodal_logic.translation import prefix_to_infix, json_to_prefix, temporal_depth  # noqa: E402


def formula_str(formula_json: dict) -> str:
    try:
        return prefix_to_infix(json_to_prefix(formula_json))
    except Exception as e:  # pragma: no cover - diagnostic path
        return f"<translation error: {e}> {formula_json}"


def main() -> None:
    mc_oracle = Z3OracleProvider()
    bh_z3 = BHZ3OracleProvider()

    _KNOWN_MC_EDGE_CASES = [
        {"tag": "untl", "event": {"tag": "bot"}, "guard": {"tag": "bot"}},
    ]

    def is_known_edge_case(f):
        return any(f == ec for ec in _KNOWN_MC_EDGE_CASES)

    all_formulas = _enumerate_primitive_formulas(5, ["p"])
    temporal_formulas = [f for f in all_formulas if _is_temporal_only(f)]
    print(f"Total temporal-only formulas at complexity<=5: {len(temporal_formulas)}", flush=True)

    resolved_and_wrong = []
    inconclusive = []
    agreements = 0

    t0 = time.time()
    for i, formula_json in enumerate(temporal_formulas):
        if is_known_edge_case(formula_json):
            continue

        try:
            mc_result = mc_oracle.find_countermodel(formula_json)
        except OracleTimeoutError:
            inconclusive.append(formula_json)
            continue
        mc_sat = mc_result is not None

        try:
            bh_result = bh_z3.find_countermodel(formula_json)
            bh_sat = bh_result is not None
        except Exception as e:
            print(f"  [{i}] BH raised {e!r} on {formula_json}", flush=True)
            continue

        if mc_sat != bh_sat:
            entry = {
                "index": i,
                "formula_json": formula_json,
                "formula_str": formula_str(formula_json),
                "complexity": _formula_complexity(formula_json),
                "temporal_depth": temporal_depth(formula_json),
                "mc_sat": mc_sat,
                "bh_sat": bh_sat,
            }
            resolved_and_wrong.append(entry)
            print(f"  DISAGREE [{i}]: {entry['formula_str']} depth={entry['temporal_depth']} "
                  f"MC_sat={mc_sat} BH_sat={bh_sat}", flush=True)
        else:
            agreements += 1

        if i % 20 == 0:
            print(f"  progress: {i}/{len(temporal_formulas)} "
                  f"agree={agreements} disagree={len(resolved_and_wrong)} "
                  f"inconclusive={len(inconclusive)} elapsed={time.time()-t0:.1f}s",
                  flush=True)

    print(f"\nDONE elapsed={time.time()-t0:.1f}s", flush=True)
    print(f"agreements={agreements} resolved_and_wrong={len(resolved_and_wrong)} "
          f"inconclusive={len(inconclusive)} total={len(temporal_formulas)}", flush=True)

    out_path = Path(__file__).resolve().parent / "13_disagreements.json"
    with open(out_path, "w") as f:
        json.dump(
            {
                "total_temporal_formulas": len(temporal_formulas),
                "agreements": agreements,
                "resolved_and_wrong_count": len(resolved_and_wrong),
                "inconclusive_count": len(inconclusive),
                "resolved_and_wrong": resolved_and_wrong,
                "inconclusive": inconclusive,
            },
            f,
            indent=2,
        )
    print(f"Wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
