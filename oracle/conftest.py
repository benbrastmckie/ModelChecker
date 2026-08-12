"""Shared pytest configuration for the standalone oracle/ test tree.

Registration lives here rather than in an `oracle/pytest.ini` or
`oracle/pyproject.toml`: a conftest.py is loaded during collection independent
of pytest's rootdir/inifile resolution, so it registers marks for any
`oracle/`-rooted invocation without becoming the first-found inifile and
without perturbing rootdir semantics for the tree.

`differential`, `slow`, and `unstable` are already declared in
`code/pyproject.toml`, but that file is a sibling of `oracle/`, not an
ancestor -- pytest's ini-discovery never reaches it when the invocation is
rooted at `oracle/` (or at the repo root, since the repo root itself has no
ini file). Re-declaring them here closes that ini-discovery gap; keep this
list and `code/pyproject.toml`'s `markers` list in sync so the two
declarations never drift apart.
"""

from __future__ import annotations

import json
import os

import pytest

# Node-id (function name, id-fragment) pairs that must run outside parallel
# workers. Matched by both the test function name and a substring of the
# parametrize id, so a bare id-fragment match cannot spill onto an unrelated
# parametrize site that happens to share a case name.
_XDIST_SERIAL_NODEID_FRAGMENTS = (
    ("test_enriched_vs_primitive_sat_agreement", "[some_past]"),
    ("test_regression_all_active_examples", "[BM_CM_1"),
)


def pytest_configure(config: pytest.Config) -> None:
    """Register custom marks used across the oracle/ suite.

    `differential` and `slow` mirror the descriptions in
    `code/pyproject.toml` so the two declarations do not drift.
    """
    config.addinivalue_line(
        "markers",
        "differential: Tests that compare MC oracle against reference oracles",
    )
    config.addinivalue_line(
        "markers",
        "slow: Tests that are computationally expensive and skipped in CI",
    )
    config.addinivalue_line(
        "markers",
        "unstable: Tests with a documented, investigated non-semantic instability "
        "(e.g. a heavy-tailed solver draw). Deselected from release-gating runs "
        "with `-m \"not unstable\"`; run on their own by the unstable-watch "
        "workflow so they stay observed rather than forgotten.",
    )
    config.addinivalue_line(
        "markers",
        "xdist_serial: Tests whose Z3 solve budget has under ~2x headroom, "
        "which CPU contention under pytest-xdist can push past budget -- "
        "reported as no-countermodel rather than as an error (see "
        "code/docs/core/TESTING_GUIDE.md section 8.6). Run these in the "
        "serial pass of oracle/run-oracle-suite.sh, never under -n.",
    )


def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    """Apply `xdist_serial` to the parametrized cases that cannot be marked at
    the source without breaking the shared data structures they are built
    from (`ENRICHED_PRIMITIVE_PAIRS`'s `ids=` comprehensions and
    `regression_examples`'s `.items()` consumers -- see
    `code/docs/core/TESTING_GUIDE.md` section 8.6 for the underlying
    contention mechanism this mark exists to route around).
    """
    marker = pytest.mark.xdist_serial
    for item in items:
        for func_name, id_fragment in _XDIST_SERIAL_NODEID_FRAGMENTS:
            if func_name in item.nodeid and id_fragment in item.nodeid:
                item.add_marker(marker)


##############################################################################
# Timeout-skip inventory: reporting-only collection and classification of
# every timeout-conditional `pytest.skip()` outcome in a session. See
# `code/docs/core/TESTING_GUIDE.md` section 8.8's "Timeout-skip inventory"
# subsection for the full contract; this is the implementation of it. Never
# adds a marker, never touches `session.exitstatus`, never converts a skip
# into anything else -- this exists purely to make a skip visible and
# classified, not to change what happens to it.
##############################################################################

# Stable substring shared by both timeout-conditional pytest.skip() messages
# in test_oracle_interface.py (site ~635, TestOracleExampleRegressionViaAPI
# ::test_oracle_regression: "'{name}': did not decide within {timeout} ms";
# site ~779, TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement:
# "'{name}': at least one side did not decide within {timeout} ms"). Matching
# on this substring rather than either full message means a future reword of
# either site breaks the dedicated unit test asserting this match
# (test_timeout_skip_inventory.py), not this report silently going quiet.
_TIMEOUT_SKIP_SIGNATURE = "did not decide within"

# Node-id fragment -> short adjudication note. Seeded with exactly the two
# skip sites confirmed live and adjudicated. A timeout-caused skip whose
# node id contains none of these fragments is [NEW]: an unadjudicated
# finding to investigate, never assumed to be a defect in this tooling.
_KNOWN_TIMEOUT_SKIPS: dict[str, str] = {
    "test_oracle_regression[TN_TH_2]": (
        "label corrected to SAT from the ground-truth evaluator; the solver "
        "still does not decide it at 2x budget"
    ),
    "test_enriched_vs_primitive_sat_agreement[all_future]": (
        "primitive untl-based expansion does not decide; the enriched form "
        "decides in under 2s -- a performance gap, not a disagreement"
    ),
}

# Session-scoped collection state. Each pytest invocation (including each
# xdist controller process) is a fresh interpreter, so module-level state
# here is inherently scoped to a single session -- there is no cross-session
# leakage to guard against, and no explicit reset hook is needed.
_seen_node_ids: set[str] = set()
_timeout_skips: dict[str, str] = {}  # node id -> extracted skip reason


def _extract_skip_reason(report: pytest.TestReport) -> str:
    """Extract the skip reason string from a TestReport's longrepr.

    An in-body `pytest.skip()` produces a `(path, lineno, "Skipped: <reason>")`
    tuple; anything else (e.g. a skipif marker's longrepr) falls back to
    `str(report.longrepr)`.
    """
    longrepr = report.longrepr
    if isinstance(longrepr, tuple) and len(longrepr) == 3:
        return str(longrepr[2])
    return str(longrepr)


def pytest_runtest_logreport(report: pytest.TestReport) -> None:
    """Record every report's node id into the session's seen set, and
    classify timeout-caused skips.

    Deriving the seen set from reports actually observed in *this* session
    -- rather than from a static list or a collection-time hook -- is what
    makes the RESOLVED classification below safe under the two-pass gating
    runner: a node id that only ran in a *different* pytest invocation
    (pass 1's parallel run vs. pass 2's serial run, or an unrelated prior
    session) must never be treated as "collected but not skipped" in a
    session that never touched it. This hook fires once per test phase
    (setup/call/teardown) and receives worker reports identically whether
    the session runs under pytest-xdist (`-n 6`) or serially, since xdist's
    controller re-dispatches each worker's report through the standard
    reporting hooks.
    """
    _seen_node_ids.add(report.nodeid)
    if report.when != "call" or not report.skipped:
        return
    reason = _extract_skip_reason(report)
    if _TIMEOUT_SKIP_SIGNATURE in reason:
        _timeout_skips[report.nodeid] = reason


def _matched_known_note(nodeid: str) -> str | None:
    """Return the adjudication note for nodeid if it matches a known
    timeout-skip fragment, else None."""
    for fragment, note in _KNOWN_TIMEOUT_SKIPS.items():
        if fragment in nodeid:
            return note
    return None


def _classify_session() -> tuple[list[dict], list[dict], list[dict]]:
    """Classify this session's timeout skips into KNOWN / NEW / RESOLVED.

    Returns three lists of dicts (known, new, resolved), each entry keyed
    by `nodeid` plus a `note` (known/resolved) or `reason` (new) field --
    shared by both the terminal summary and the opt-in JSON artifact so the
    two can never disagree.
    """
    known: list[dict] = []
    new: list[dict] = []
    resolved: list[dict] = []

    for nodeid, reason in sorted(_timeout_skips.items()):
        note = _matched_known_note(nodeid)
        if note is not None:
            known.append({"nodeid": nodeid, "note": note})
        else:
            new.append({"nodeid": nodeid, "reason": reason})

    # A known entry is RESOLVED only if it actually ran in *this* session
    # (present in _seen_node_ids) and did not skip for a timeout reason this
    # time. A known entry absent from this session's seen set is not this
    # session's business and is omitted entirely.
    for fragment, note in _KNOWN_TIMEOUT_SKIPS.items():
        for nodeid in sorted(_seen_node_ids):
            if fragment in nodeid and nodeid not in _timeout_skips:
                resolved.append({"nodeid": nodeid, "note": note})

    return known, new, resolved


def pytest_terminal_summary(terminalreporter) -> None:
    """Print the timeout-skip inventory, and optionally write it as JSON.

    Reporting-only: never touches `session.exitstatus`, never adds a
    pytest marker, and never converts a skip into anything else. Printed
    unconditionally, even when every category is empty, so silence in the
    gating runner's output is never ambiguous between "nothing to report"
    and "this hook did not run."
    """
    known, new, resolved = _classify_session()

    terminalreporter.write_line("")
    terminalreporter.write_line("== ORACLE TIMEOUT-SKIP INVENTORY ==")
    if not (known or new or resolved):
        terminalreporter.write_line("no timeout skips in this session")
    else:
        for entry in known:
            terminalreporter.write_line(f"[KNOWN] {entry['nodeid']}: {entry['note']}")
        for entry in new:
            terminalreporter.write_line(
                f"[NEW] {entry['nodeid']}: {entry['reason']} -- adjudicate "
                f"this formula's expected_sat against "
                f"bimodal_logic/ground_truth.py before assuming the "
                f"existing label is right"
            )
        for entry in resolved:
            terminalreporter.write_line(
                f"[RESOLVED] {entry['nodeid']}: previously known as "
                f"{entry['note']!r} -- the formula now decides. Re-check "
                f"its label and its REGRESSION_TIMEOUT_EXAMPLES membership."
            )
    terminalreporter.write_line(
        "-- a skip here is a budget/performance outcome, never cleared by "
        "widening a solve budget; see code/docs/core/TESTING_GUIDE.md "
        "sections 8.6 and 8.8."
    )

    report_path = os.environ.get("ORACLE_SKIP_REPORT")
    if report_path:
        with open(report_path, "w") as fh:
            json.dump({"known": known, "new": new, "resolved": resolved}, fh, indent=2)
