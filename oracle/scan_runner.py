#!/usr/bin/env python
"""Standalone instrumented oracle self-consistency scan CLI.

A thin second entry point over the single shared scan core --
`_generate_differential_report()` in
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` -- not a
reimplementation. This script contains no enumerate-solve-compare loop of
its own: it imports the enumerator, the reference-verdict helper, the
shared report generator, and the two assertion-relevant constants from the
test module and calls the shared core directly (Decision D1: instrumentation
lives inside the one function both entry points call, so there is never a
second loop to drift). It exists for bounded/ad-hoc runs (`--limit`,
`--timeout-ms`, `--out-dir`) -- the capability that proved essential during
prior oracle self-consistency triage -- not as the primary path; the primary
exhaustive path is `oracle/run-oracle-exhaustive-scan.sh`, which drives
`pytest oracle -m slow -s` so the pytest test itself produces the same
artifacts via the same shared core.

Usage:
    python oracle/scan_runner.py [--timeout-ms MS] [--max-complexity N]
        [--limit N] [--out-dir DIR] [--heartbeat-every N]
        [--min-conclusive N]

Every run writes, under --out-dir (default a timestamped directory under
oracle/scan-results/):
    progress.jsonl   One flushed JSON record per formula.
    report.json      The full differential report (see _generate_differential_report).
    SCAN_COMPLETE    Completion marker, written last -- see the module
                      docstring of test_cross_oracle_differential.py for the
                      full marker contract. Its existence, not process/PID
                      liveness, is the only sanctioned completion signal.

Exit codes:
    0  Clean scan meeting both assertion teeth (zero disagreements among
       conclusive results, and at least --min-conclusive conclusive formulas).
    1  A disagreement occurred, or the conclusiveness floor was missed.
    2  Operational error (import failure or similar) -- not a scan verdict.
"""

from __future__ import annotations

import argparse
import datetime
import os
import sys
from pathlib import Path

_ORACLE_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _ORACLE_DIR.parent
_TESTS_DIR = _ORACLE_DIR / "bimodal_logic" / "tests"
_CODE_SRC_DIR = _REPO_ROOT / "code" / "src"

# Ensure both the `bimodal_logic` package (rooted at oracle/) and the shared
# scan core module (oracle/bimodal_logic/tests/) are importable, independent
# of the caller's cwd or PYTHONPATH -- mirrors the proven path-insertion
# approach in specs/133_fix_oracle_self_consistency_disagreements/evidence/
# scan_instrumented.py, but resolved from this script's own location rather
# than os.getcwd() so it works regardless of invocation directory.
for _p in (_ORACLE_DIR, _TESTS_DIR, _CODE_SRC_DIR):
    _p_str = str(_p)
    if _p_str not in sys.path:
        sys.path.insert(0, _p_str)

from test_cross_oracle_differential import (  # noqa: E402
    MIN_CONCLUSIVE_SCAN_FORMULAS,
    SELF_SCAN_SOLVE_TIMEOUT_MS,
    _assert_scan_report,
    _enumerate_primitive_formulas,
    _generate_differential_report,
    _reference_verdict,
)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Standalone instrumented oracle self-consistency scan.",
    )
    parser.add_argument(
        "--timeout-ms", type=int, default=SELF_SCAN_SOLVE_TIMEOUT_MS,
        help=f"Per-solve budget in milliseconds (default: {SELF_SCAN_SOLVE_TIMEOUT_MS}, "
             "the deployed self-scan budget).",
    )
    parser.add_argument(
        "--max-complexity", type=int, default=5,
        help="Maximum formula complexity to enumerate (default: 5).",
    )
    parser.add_argument(
        "--limit", type=int, default=None,
        help="Only run the first N enumerated formulas (default: all).",
    )
    parser.add_argument(
        "--out-dir", type=str, default=None,
        help="Output directory for progress.jsonl/report.json/SCAN_COMPLETE "
             "(default: a timestamped directory under oracle/scan-results/).",
    )
    parser.add_argument(
        "--heartbeat-every", type=int, default=10,
        help="Print a heartbeat line every N formulas, plus loud lines for "
             "disagreements/timeouts/slow solves (default: 10).",
    )
    parser.add_argument(
        "--min-conclusive", type=int, default=MIN_CONCLUSIVE_SCAN_FORMULAS,
        help="Conclusiveness floor passed to _assert_scan_report "
             f"(default: {MIN_CONCLUSIVE_SCAN_FORMULAS}, the deployed "
             "exhaustive-scan floor). Never lower this to force a green run.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)

    if args.out_dir is None:
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        out_dir = _ORACLE_DIR / "scan-results" / stamp
    else:
        out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    try:
        from bimodal_logic import Z3OracleProvider
    except Exception as exc:  # operational error: cannot even import the oracle
        print(f"# ERROR: could not import Z3OracleProvider: {exc!r}", flush=True)
        return 2

    oracle = Z3OracleProvider()
    formulas = _enumerate_primitive_formulas(args.max_complexity, ["p"])
    if args.limit is not None:
        formulas = formulas[: args.limit]

    def ref_fn(formula_json):
        return _reference_verdict(oracle, formula_json, timeout_ms=args.timeout_ms)

    print(
        f"# formulas={len(formulas)} timeout_ms={args.timeout_ms} "
        f"max_complexity={args.max_complexity} out_dir={out_dir} pid={os.getpid()}",
        flush=True,
    )

    report = _generate_differential_report(
        oracle,
        formulas,
        ref_fn,
        {"mc": "mc_oracle", "ref": "mc_oracle_self"},
        timeout_ms=args.timeout_ms,
        progress_path=out_dir / "progress.jsonl",
        heartbeat_every=args.heartbeat_every,
        artifact_dir=out_dir,
    )

    conclusive = report["total_formulas"] - report["timeout_count"]
    print(
        f"# DONE total={report['total_formulas']} "
        f"agreements={report['agreements']} "
        f"disagreements={report['disagreements']} "
        f"timeouts={report['timeout_count']} "
        f"conclusive={conclusive} "
        f"wall={report['wall_clock_seconds']:.0f}s "
        f"out_dir={out_dir}",
        flush=True,
    )

    try:
        _assert_scan_report(report, min_conclusive=args.min_conclusive)
    except AssertionError as exc:
        print(f"# ASSERTION FAILED: {exc}", flush=True)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
