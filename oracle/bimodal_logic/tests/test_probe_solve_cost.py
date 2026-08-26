"""Tests for the standalone solve-cost probe CLI (oracle/probe_solve_cost.py).

A reusable, foreground probe harness that solves one oracle formula through
a settings-dict-identical replication of Z3OracleProvider.find_countermodel()'s
pipeline (see provider.py) and reports wall time, decided/undecided, and the
Z3 rlimit resource-unit statistic consumed -- so later measurement work (and
any future "recalibrate from a fresh uncensored probe" instruction in
TESTING_GUIDE.md) uses one tested tool instead of an ad hoc scratch script.

All formulas exercised here are ATEMPORAL (temporal_depth=0), so this file
adds no `slow`/`xdist_serial`/`unstable` test to the gating suite -- every
solve is sub-second by construction.
"""

from __future__ import annotations

import json
import os

import pytest

from probe_solve_cost import FORMULA_REGISTRY, main, run_probe


ATEMPORAL_FORMULA_NAME = "atemporal_and_neg"


class TestFormulaRegistry:
    """The registry backing --formula-name must expose the atemporal probe formula."""

    def test_atemporal_formula_registered(self):
        assert ATEMPORAL_FORMULA_NAME in FORMULA_REGISTRY
        formula = FORMULA_REGISTRY[ATEMPORAL_FORMULA_NAME]
        assert isinstance(formula, dict)
        assert "tag" in formula


class TestRunProbeDecided:
    """A cheap atemporal formula decides with a positive rlimit."""

    def test_decided_result_has_positive_rlimit(self):
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=10000,
            seed=None,
        )
        assert record["decided"] is True
        assert isinstance(record["rlimit"], int)
        assert record["rlimit"] > 0

    def test_decided_record_schema_is_non_null(self, monkeypatch):
        """Verification criterion: a JSON record with non-null wall_s, rlimit,
        decided, z3_version, pythonhashseed (the last requires PYTHONHASHSEED
        to actually be set in the environment -- pinned explicitly here
        rather than relying on ambient shell state)."""
        monkeypatch.setenv("PYTHONHASHSEED", "0")
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=10000,
            seed=None,
        )
        for key in ("wall_s", "rlimit", "decided", "z3_version", "pythonhashseed"):
            assert record[key] is not None, f"{key} was unexpectedly None"
        assert record["seed"] == "default"
        assert record["timeout_ms"] == 10000
        assert record["formula_name"] == ATEMPORAL_FORMULA_NAME


class TestRunProbeUndecided:
    """A deliberately tiny timeout reports undecided, never raises."""

    def test_tiny_timeout_reports_undecided_not_raises(self):
        # timeout_ms=0 is NOT "instant timeout": Z3 treats 0 as disabling
        # its "timeout" option (confirmed empirically -- see the phase
        # handoff), so it decides normally instead of timing out. 1ms is
        # the smallest budget that reliably produces an undecided draw for
        # this formula.
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=1,
            seed=None,
        )
        assert record["decided"] is False
        # rlimit is still readable on an undecided draw -- Phase 2's
        # measurement log records rlimit alongside decided/undecided.
        assert isinstance(record["rlimit"], int)


class TestSeedApplication:
    """--seed pins sat.random_seed/smt.random_seed and is recorded verbatim."""

    def test_seed_recorded_in_record(self):
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=10000,
            seed=42,
        )
        assert record["seed"] == 42
        assert record["decided"] is True

    def test_default_seed_recorded_as_default(self):
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=10000,
            seed=None,
        )
        assert record["seed"] == "default"


class TestPythonHashSeedRecorded:
    def test_pythonhashseed_matches_environment(self):
        record = run_probe(
            formula_name=ATEMPORAL_FORMULA_NAME,
            timeout_ms=10000,
            seed=None,
        )
        assert record["pythonhashseed"] == os.environ.get("PYTHONHASHSEED")


class TestCLIRepeat:
    """--repeat N emits one JSON record per draw."""

    def test_repeat_emits_n_json_lines(self, capsys):
        exit_code = main([
            "--formula-name", ATEMPORAL_FORMULA_NAME,
            "--timeout-ms", "10000",
            "--repeat", "3",
        ])
        assert exit_code == 0
        captured = capsys.readouterr()
        json_lines = [
            line for line in captured.out.splitlines()
            if line.strip().startswith("{")
        ]
        assert len(json_lines) == 3
        for i, line in enumerate(json_lines):
            record = json.loads(line)
            assert record["draw_index"] == i
            assert record["decided"] is True

    def test_cli_accepts_seed_flag(self, capsys):
        exit_code = main([
            "--formula-name", ATEMPORAL_FORMULA_NAME,
            "--timeout-ms", "10000",
            "--seed", "7",
        ])
        assert exit_code == 0
        captured = capsys.readouterr()
        json_lines = [
            line for line in captured.out.splitlines()
            if line.strip().startswith("{")
        ]
        assert len(json_lines) == 1
        record = json.loads(json_lines[0])
        assert record["seed"] == 7

    def test_unknown_formula_name_is_operational_error(self, capsys):
        exit_code = main(["--formula-name", "not_a_real_formula"])
        assert exit_code == 2
