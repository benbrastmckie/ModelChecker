"""Instrumented re-run of the complexity<=5 self-consistency scan.

Prints one flushed line per formula and appends a JSONL record, so a long run is
observable while in flight instead of silent until the end. Mirrors exactly what
TestFullScanReport::test_complexity_5_scan_self_consistent does: for each formula
run the oracle twice (once as "reference", once as the subject) and compare.

Usage:
  python scan_instrumented.py [--timeout-ms N] [--limit N] [--out PATH]
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.getcwd(), "oracle", "bimodal_logic", "tests"))

from test_cross_oracle_differential import (  # noqa: E402
    _enumerate_primitive_formulas,
    _formula_complexity,
)


def solve(oracle, formula, timeout_ms):
    """One find_countermodel call. Returns (result, elapsed_s, exc_repr_or_None)."""
    t0 = time.monotonic()
    try:
        if timeout_ms is None:
            out = oracle.find_countermodel(formula)
        else:
            out = oracle.find_countermodel(formula, timeout_ms=timeout_ms)
        return ("UNSAT" if out is None else "SAT"), time.monotonic() - t0, None
    except Exception as e:  # same swallow the test performs, but recorded
        return "TIMEOUT", time.monotonic() - t0, repr(e)[:200]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout-ms", type=int, default=60000)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--out", default="scan_instrumented.jsonl")
    args = ap.parse_args()
    timeout_ms = None if args.timeout_ms <= 0 else args.timeout_ms

    from bimodal_logic import Z3OracleProvider

    oracle = Z3OracleProvider()
    formulas = _enumerate_primitive_formulas(5, ["p"])
    if args.limit:
        formulas = formulas[: args.limit]

    total = len(formulas)
    print(f"# formulas={total} timeout_ms={timeout_ms} pid={os.getpid()}", flush=True)
    print(
        "# idx/total cplx ref(t) mc(t) verdict  cum_disagree cum_timeout elapsed",
        flush=True,
    )

    agreements = disagreements = timeouts = 0
    t_start = time.monotonic()

    with open(args.out, "w", encoding="utf-8") as fh:
        for i, f in enumerate(formulas, 1):
            cplx = _formula_complexity(f)
            ref, ref_t, ref_exc = solve(oracle, f, timeout_ms)
            mc, mc_t, mc_exc = solve(oracle, f, timeout_ms)

            if mc == "TIMEOUT":
                timeouts += 1
                verdict = "TIMEOUT"
            elif mc == ref:
                agreements += 1
                verdict = "agree"
            else:
                disagreements += 1
                verdict = "DISAGREE"

            rec = {
                "idx": i,
                "complexity": cplx,
                "ref_result": ref,
                "ref_elapsed_s": round(ref_t, 3),
                "ref_exc": ref_exc,
                "mc_result": mc,
                "mc_elapsed_s": round(mc_t, 3),
                "mc_exc": mc_exc,
                "verdict": verdict,
                "formula_json": f,
            }
            fh.write(json.dumps(rec) + "\n")
            fh.flush()

            # Loud line for every formula that is slow, disagrees, or times out;
            # otherwise a periodic heartbeat so a healthy run still shows progress.
            loud = verdict != "agree" or max(ref_t, mc_t) > 5.0
            if loud or i % 10 == 0 or i == 1:
                print(
                    f"[{i}/{total}] c{cplx} "
                    f"ref={ref}({ref_t:.1f}s) mc={mc}({mc_t:.1f}s) {verdict}  "
                    f"D={disagreements} T={timeouts} "
                    f"elapsed={time.monotonic() - t_start:.0f}s",
                    flush=True,
                )

    print(
        f"# DONE total={total} agreements={agreements} "
        f"disagreements={disagreements} timeouts={timeouts} "
        f"wall={time.monotonic() - t_start:.0f}s",
        flush=True,
    )
    return 0 if disagreements == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
