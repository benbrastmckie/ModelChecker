"""Unit tests for oracle/conftest.py's timeout-skip inventory hook.

Loaded by explicit path via importlib rather than `import conftest`: `conftest`
is an ambiguous bare module name (multiple `conftest.py` files exist across
this repository) and pytest's own conftest-loading machinery does not
guarantee a stable, importable module name for any one of them, so importing
by absolute file path is the only way to reach `oracle/conftest.py`'s
internals directly and deterministically.

See `code/docs/core/TESTING_GUIDE.md` section 8.8's "Timeout-skip inventory"
subsection for the contract these tests pin.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest


def _load_oracle_conftest():
    conftest_path = Path(__file__).resolve().parents[2] / "conftest.py"
    spec = importlib.util.spec_from_file_location("oracle_conftest_under_test", conftest_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


oc = _load_oracle_conftest()


def _fake_report(nodeid: str, when: str, skipped: bool, reason: str | None = None):
    """Build a minimal stand-in for pytest.TestReport carrying only the
    attributes oc.pytest_runtest_logreport / oc._extract_skip_reason touch.
    """
    longrepr = None
    if reason is not None:
        longrepr = ("path/to/file.py", 123, f"Skipped: {reason}")
    return SimpleNamespace(nodeid=nodeid, when=when, skipped=skipped, longrepr=longrepr)


@pytest.fixture(autouse=True)
def _reset_session_state():
    """Give each test a clean session-scoped collection state, mirroring a
    fresh pytest invocation -- module-level state in conftest.py is only
    ever session-scoped in a real run, since a new interpreter starts each
    session."""
    oc._seen_node_ids.clear()
    oc._timeout_skips.clear()
    yield
    oc._seen_node_ids.clear()
    oc._timeout_skips.clear()


##############################################################################
# Signature matching against the two real skip messages
##############################################################################

class TestSkipSignatureMatch:
    """Both real skip messages must match the shared signature; an
    unrelated skip reason must not."""

    def test_site_635_message_matches(self):
        # test_oracle_interface.py:635 (TestOracleExampleRegressionViaAPI
        # ::test_oracle_regression)
        reason = (
            "'TN_TH_2': did not decide within 30000 ms (budget/performance "
            "outcome, not a semantic regression -- its ACTIVE_EXAMPLES "
            "expected_sat may itself have been measured under the old "
            "timeout-conflated contract)"
        )
        assert oc._TIMEOUT_SKIP_SIGNATURE in reason

    def test_site_779_message_matches(self):
        # test_oracle_interface.py:779 (TestEnrichedRoundTrip
        # ::test_enriched_vs_primitive_sat_agreement)
        reason = (
            "'all_future': at least one side did not decide within 180000 "
            "ms (budget/performance, not a semantic disagreement)"
        )
        assert oc._TIMEOUT_SKIP_SIGNATURE in reason

    def test_unrelated_skip_reason_does_not_match(self):
        reason = "unsupported frame_class 'Weird' for this provider"
        assert oc._TIMEOUT_SKIP_SIGNATURE not in reason


##############################################################################
# Reason extraction
##############################################################################

class TestExtractSkipReason:
    def test_extracts_from_three_tuple_longrepr(self):
        report = _fake_report(
            "mod.py::test_x", "call", True, reason="did not decide within 30000 ms"
        )
        assert "did not decide within 30000 ms" in oc._extract_skip_reason(report)

    def test_falls_back_to_str_for_non_tuple_longrepr(self):
        report = SimpleNamespace(
            nodeid="mod.py::test_x",
            when="call",
            skipped=True,
            longrepr="some skipif longrepr string",
        )
        assert oc._extract_skip_reason(report) == "some skipif longrepr string"


##############################################################################
# Report collection
##############################################################################

class TestLogreportCollection:
    def test_seen_set_records_every_nodeid_regardless_of_outcome(self):
        oc.pytest_runtest_logreport(_fake_report("t.py::test_a", "call", False))
        assert "t.py::test_a" in oc._seen_node_ids

    def test_timeout_skip_not_recorded_outside_call_phase(self):
        oc.pytest_runtest_logreport(
            _fake_report("t.py::test_a", "setup", True, reason="did not decide within 1 ms")
        )
        assert "t.py::test_a" not in oc._timeout_skips

    def test_non_timeout_skip_not_recorded_as_timeout_skip(self):
        oc.pytest_runtest_logreport(
            _fake_report("t.py::test_a", "call", True, reason="unrelated reason")
        )
        assert "t.py::test_a" not in oc._timeout_skips

    def test_timeout_skip_recorded_at_call_phase(self):
        nodeid = "t.py::test_oracle_regression[TN_TH_2]"
        oc.pytest_runtest_logreport(
            _fake_report(nodeid, "call", True, reason="'TN_TH_2': did not decide within 30000 ms")
        )
        assert nodeid in oc._timeout_skips


##############################################################################
# KNOWN / NEW / RESOLVED classification
##############################################################################

class TestClassification:
    def test_known_entry_classified_known(self):
        nodeid = (
            "oracle/x.py::TestOracleExampleRegressionViaAPI"
            "::test_oracle_regression[TN_TH_2]"
        )
        oc.pytest_runtest_logreport(
            _fake_report(nodeid, "call", True, reason="'TN_TH_2': did not decide within 30000 ms")
        )
        known, new, resolved = oc._classify_session()
        assert [e["nodeid"] for e in known] == [nodeid]
        assert new == []
        assert resolved == []

    def test_unrecognized_timeout_skip_classified_new(self):
        nodeid = (
            "oracle/x.py::TestOracleExampleRegressionViaAPI"
            "::test_oracle_regression[SOME_OTHER]"
        )
        oc.pytest_runtest_logreport(
            _fake_report(
                nodeid, "call", True, reason="'SOME_OTHER': did not decide within 30000 ms"
            )
        )
        known, new, resolved = oc._classify_session()
        assert known == []
        assert [e["nodeid"] for e in new] == [nodeid]

    def test_known_entry_that_now_decides_is_resolved(self):
        nodeid = (
            "oracle/x.py::TestOracleExampleRegressionViaAPI"
            "::test_oracle_regression[TN_TH_2]"
        )
        # Ran this session (present in the seen set) but did NOT skip this
        # time -- report.skipped=False.
        oc.pytest_runtest_logreport(_fake_report(nodeid, "call", False))
        known, new, resolved = oc._classify_session()
        assert known == []
        assert new == []
        assert [e["nodeid"] for e in resolved] == [nodeid]

    def test_known_entry_not_collected_this_session_is_omitted(self):
        """Two-pass-runner safety: a known fragment that never ran in this
        session (absent from the seen set) must never be reported as
        RESOLVED merely because it is also absent from _timeout_skips --
        this is what stops pass 1's skip from looking "resolved" during
        pass 2's session."""
        known, new, resolved = oc._classify_session()
        assert known == []
        assert new == []
        assert resolved == []


##############################################################################
# Opt-in JSON artifact
##############################################################################

class TestJsonArtifact:
    def test_writes_json_artifact_when_env_var_set(self, tmp_path, monkeypatch):
        report_path = tmp_path / "skip-report.json"
        monkeypatch.setenv("ORACLE_SKIP_REPORT", str(report_path))

        nodeid = (
            "oracle/x.py::TestOracleExampleRegressionViaAPI"
            "::test_oracle_regression[TN_TH_2]"
        )
        oc.pytest_runtest_logreport(
            _fake_report(nodeid, "call", True, reason="'TN_TH_2': did not decide within 30000 ms")
        )

        terminalreporter = SimpleNamespace(write_line=lambda *_a, **_k: None)
        oc.pytest_terminal_summary(terminalreporter)

        assert report_path.exists()
        payload = json.loads(report_path.read_text())
        assert set(payload.keys()) == {"known", "new", "resolved"}
        assert [e["nodeid"] for e in payload["known"]] == [nodeid]
        assert payload["new"] == []
        assert payload["resolved"] == []

    def test_no_json_artifact_written_when_env_var_unset(self, monkeypatch, tmp_path):
        monkeypatch.delenv("ORACLE_SKIP_REPORT", raising=False)
        monkeypatch.chdir(tmp_path)
        terminalreporter = SimpleNamespace(write_line=lambda *_a, **_k: None)
        # Must not raise; there is no artifact path to assert on when the
        # env var is unset, so absence of an exception is the whole test.
        oc.pytest_terminal_summary(terminalreporter)
        assert list(tmp_path.iterdir()) == []
