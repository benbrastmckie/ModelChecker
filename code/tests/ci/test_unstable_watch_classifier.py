"""Unit tests for `.github/scripts/unstable_watch_classify.py`, the classifier extracted
from `.github/workflows/unstable-watch.yml`'s "Classify results and build the trend report"
step (see `code/docs/core/TESTING_GUIDE.md` section 8.9). The heredoc it replaces was
untestable in place; this module makes the classification contract executable.

Two distinct test groups:

- **Characterization tests** pin the CURRENT `BM_CM_1` behavior (duration >= 0.8x max_time
  AND the `"Test failed for example:"` signature -> `TIMING`; anything else -> `NEW`). These
  must stay green, unmodified, across the extraction (behavior-preserving) and across the
  gating-floor signature addition (additive, not replacing).
- **New-signature tests** define the gating-floor `TIMING` branch this task adds:
  `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`'s
  `_assert_scan_report` floor failure (see `oracle/bimodal_logic/tests/
  test_cross_oracle_differential.py`). The laundering-guard test is the load-bearing one: a
  `disagreements != 0` failure on the SAME node id must never classify `TIMING`, because that
  is a real soundness bug, not the documented budget/performance instability.

Loads the classifier module by absolute path via `importlib.util`, following the established
in-repo pattern in
`oracle/bimodal_logic/tests/test_timeout_skip_inventory.py::_load_oracle_conftest`.

Skip guard mirrors `code/tests/ci/test_workflow_parity.py`'s `_MISSING_REPO_ROOT_FILES` block:
under `nix flake check`'s `checks.default` derivation, `src = ./code` means the sandboxed build
has no repo root at all, so `.github/` is structurally absent there. The guard below probes
STABLE repo-root markers (`.github/workflows/tests.yml`, `flake.nix`) to detect that sandbox,
deliberately NOT the classifier script itself -- the classifier script's own absence (before
Phase 2 of the plan that introduced this module lands it) is the EXPECTED RED failure this
module must report clearly, not something to skip past.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TESTS_YML = REPO_ROOT / ".github" / "workflows" / "tests.yml"
FLAKE_NIX = REPO_ROOT / "flake.nix"
CLASSIFIER_SCRIPT = REPO_ROOT / ".github" / "scripts" / "unstable_watch_classify.py"

_MISSING_REPO_ROOT_FILES = [p for p in (TESTS_YML, FLAKE_NIX) if not p.exists()]
if _MISSING_REPO_ROOT_FILES:
    pytest.skip(
        "Repo-root files not present in this sandbox (expected under `nix flake check`'s "
        "checks.default, whose `src = ./code` excludes the repo root): "
        + ", ".join(str(p) for p in _MISSING_REPO_ROOT_FILES)
        + ". This guard runs in .github/workflows/tests.yml's general-tests job instead, where "
        "actions/checkout@v4 provides the full repository.",
        allow_module_level=True,
    )


def _load_classifier():
    """Load `.github/scripts/unstable_watch_classify.py` by absolute path. Before Phase 2 of
    the plan lands the script, this raises a clear FileNotFoundError naming the missing path
    at collection time -- the correctly-named RED failure for Phase 1."""
    spec = importlib.util.spec_from_file_location(
        "unstable_watch_classify_under_test", CLASSIFIER_SCRIPT
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


classify_mod = _load_classifier()

BM_CM_1_NODEID = (
    "code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::"
    "test_example_cases[BM_CM_1-example_case7]"
)
GATING_NODEID = (
    "oracle/bimodal_logic/tests/test_cross_oracle_differential.py::"
    "TestGatingConclusiveScan::test_known_conclusive_population_self_consistent"
)
UNRECOGNIZED_NODEID = "code/tests/some_other_module.py::test_unrelated_thing"

# Exact strings, copied verbatim from source rather than retyped:
# oracle/bimodal_logic/tests/test_cross_oracle_differential.py::_assert_scan_report.
# FLOOR_MESSAGE below concatenates the floor-assertion message with the print() line that
# precedes it in _assert_scan_report -- exactly the shape production failure_text takes once
# parse_junit() appends a testcase's <system-out> content (see TestParseJunitSystemOut below and
# the "disagreements=0" note on classify()'s gating branch): pytest's default JUnit XML does NOT
# embed a captured print() inside <failure> at all (verified empirically against this exact
# print()-then-assert shape; only sibling <system-out>, present when junit_logging=system-out is
# configured, carries it), so the classifier's "disagreements=0" check is meaningless unless
# parse_junit reads system-out AND unstable-watch.yml's oracle pytest invocation enables
# junit_logging=system-out -- both are part of this task's Phase 3 change.
# The bare assertion-message text alone (what <failure>'s own message/text carries with no
# system-out folded in) -- deliberately does NOT contain "disagreements=0".
FLOOR_ASSERTION_MESSAGE = (
    "Only 96 of 103 formulas were conclusive (floor=100); this is a "
    "budget/performance regression to investigate, not a semantic one."
)
# The realistic production shape: FLOOR_ASSERTION_MESSAGE with the preceding print() line
# folded in ahead of it (as parse_junit does once it reads <system-out> -- see
# TestParseJunitSystemOut below), which is where "disagreements=0" actually comes from.
FLOOR_MESSAGE = (
    "scan report: agreements=96 disagreements=0 timeout_count=7 conclusive=96/103\n"
    + FLOOR_ASSERTION_MESSAGE
)
DISAGREEMENT_MESSAGE = "Self-comparison produced 3 disagreements among conclusive results: []"
# code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases
BM_CM_1_FAILURE_TEXT = "AssertionError: Test failed for example: BM_CM_1"


# ---------------------------------------------------------------------------
# Characterization tests: pin CURRENT BM_CM_1 behavior. Phase 2's extraction
# must not change a single one of these outcomes.
# ---------------------------------------------------------------------------


class TestClassifyBMCM1Characterization:
    def test_timing_signature_at_full_duration(self):
        """duration=60.94 (>= 0.8*60) plus the known failure signature -> TIMING."""
        result = classify_mod.classify(BM_CM_1_NODEID, 60.94, BM_CM_1_FAILURE_TEXT)
        assert result == "TIMING"

    def test_fast_failure_is_new(self):
        """Same node id and text, but duration=3.0 is well under 0.8*60 -- the solver
        decided quickly and the assertion still failed, which is not the documented
        timing signature -> NEW."""
        result = classify_mod.classify(BM_CM_1_NODEID, 3.0, BM_CM_1_FAILURE_TEXT)
        assert result == "NEW"

    def test_different_message_at_full_duration_is_new(self):
        """Same node id and duration, but a different assertion message -> NEW."""
        result = classify_mod.classify(
            BM_CM_1_NODEID, 60.94, "AssertionError: something else entirely failed"
        )
        assert result == "NEW"

    def test_unrecognized_nodeid_is_new(self):
        """No known max_time for this node id -- cannot confirm the timing signature,
        so treat conservatively as NEW regardless of duration or text."""
        result = classify_mod.classify(UNRECOGNIZED_NODEID, 999.0, BM_CM_1_FAILURE_TEXT)
        assert result == "NEW"


# ---------------------------------------------------------------------------
# New-signature tests: define the gating-floor branch this task adds to
# classify(). All fail (NameError / AttributeError / wrong result) until
# Phase 3 lands the branch.
# ---------------------------------------------------------------------------


class TestClassifyGatingFloorSignature:
    def test_floor_failure_with_zero_disagreements_is_timing(self):
        """The documented gating-floor failure shape: the floor message present AND
        disagreements=0 present, no disagreement signature -> TIMING."""
        result = classify_mod.classify(GATING_NODEID, 780.0, FLOOR_MESSAGE)
        assert result == "TIMING"

    def test_laundering_guard_disagreements_failure_is_new(self):
        """THE GUARD: a genuine disagreements != 0 failure on the SAME node id must
        never classify TIMING. This is a real soundness bug -- the two
        _assert_scan_report assertions fire in order (disagreements first, floor
        second), so a disagreements failure and a floor failure are mutually
        exclusive outcomes of the same test, and only the floor shape may launder
        into TIMING."""
        result = classify_mod.classify(GATING_NODEID, 780.0, DISAGREEMENT_MESSAGE)
        assert result == "NEW"

    def test_floor_message_without_disagreements_zero_is_new(self):
        """Floor message present, but "disagreements=0" is ABSENT from the captured
        text -- cannot confirm the soundness half held, so classify NEW rather than
        assume it. Uses FLOOR_ASSERTION_MESSAGE alone (the <failure> message/text
        content with no <system-out> folded in), simulating either a truncated
        capture or an environment where junit_logging=system-out was not honored."""
        result = classify_mod.classify(GATING_NODEID, 780.0, FLOOR_ASSERTION_MESSAGE)
        assert result == "NEW"

    def test_floor_message_with_nonzero_disagreements_substring_is_new(self):
        """Floor message present, but the text ALSO contains a nonzero-disagreements
        substring (e.g. from the printed "scan report: ... disagreements=2 ..."
        line) -> NEW. The floor branch requires disagreements=0 AND the absence of
        the disagreement-failure signature. Built from FLOOR_ASSERTION_MESSAGE (not
        FLOOR_MESSAGE) so no "disagreements=0" substring is present anywhere in the
        text -- only the nonzero variant."""
        combined_text = (
            "scan report: agreements=96 disagreements=2 timeout_count=7 "
            "conclusive=96/103\n" + FLOOR_ASSERTION_MESSAGE
        )
        result = classify_mod.classify(GATING_NODEID, 780.0, combined_text)
        assert result == "NEW"

    def test_error_shaped_failure_is_new(self):
        """An error-shaped failure (e.g. an OracleTimeoutError traceback with no
        assertion message at all) on the gating node id -> NEW: neither the floor
        signature nor "disagreements=0" is present."""
        error_text = (
            "OracleTimeoutError: solve exceeded timeout_ms=40000 "
            "(temporal_depth=3, M=5)"
        )
        result = classify_mod.classify(GATING_NODEID, 41.0, error_text)
        assert result == "NEW"

    def test_gating_branch_is_duration_independent(self):
        """The gating floor is per-formula across up to 103 formulas -- no single
        wall-clock threshold is meaningful, so the branch must classify TIMING at
        both a small and a large duration given the same floor+disagreements=0
        text, confirming no max_time threshold was smuggled into this branch."""
        small_duration_result = classify_mod.classify(GATING_NODEID, 5.0, FLOOR_MESSAGE)
        large_duration_result = classify_mod.classify(GATING_NODEID, 5000.0, FLOOR_MESSAGE)
        assert small_duration_result == "TIMING"
        assert large_duration_result == "TIMING"


# ---------------------------------------------------------------------------
# parse_junit tests
# ---------------------------------------------------------------------------

_JUNIT_XML = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="4">
    <testcase classname="pkg.mod" name="test_passed" time="1.23"></testcase>
    <testcase classname="pkg.mod" name="test_failed" time="60.94">
      <failure message="AssertionError: Test failed for example: BM_CM_1">traceback text</failure>
    </testcase>
    <testcase classname="pkg.mod" name="test_errored" time="0.5">
      <error message="OracleTimeoutError: boom">traceback text</error>
    </testcase>
    <testcase classname="pkg.mod" name="test_skipped" time="0.01">
      <skipped message="skipped reason"></skipped>
    </testcase>
  </testsuite>
</testsuites>
"""


class TestParseJunit:
    def test_parses_passed_failed_error_skipped(self, tmp_path):
        junit_path = tmp_path / "junit.xml"
        junit_path.write_text(_JUNIT_XML)
        results = list(classify_mod.parse_junit(str(junit_path)))
        by_name = {nodeid.rsplit("::", 1)[-1]: (outcome, duration, text) for nodeid, outcome, duration, text in results}

        assert by_name["test_passed"][0] == "passed"
        assert by_name["test_passed"][1] == pytest.approx(1.23)

        assert by_name["test_failed"][0] == "failed"
        assert by_name["test_failed"][1] == pytest.approx(60.94)
        assert "Test failed for example: BM_CM_1" in by_name["test_failed"][2]

        assert by_name["test_errored"][0] == "error"
        assert "OracleTimeoutError" in by_name["test_errored"][2]

        assert by_name["test_skipped"][0] == "skipped"

    def test_missing_file_yields_nothing(self, tmp_path):
        missing_path = tmp_path / "does-not-exist.xml"
        results = list(classify_mod.parse_junit(str(missing_path)))
        assert results == []


_JUNIT_XML_WITH_SYSTEM_OUT = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="oracle.bimodal_logic.tests.test_cross_oracle_differential.TestGatingConclusiveScan" name="test_known_conclusive_population_self_consistent" time="780.0">
      <failure message="AssertionError: Only 96 of 103 formulas were conclusive (floor=100); this is a budget/performance regression to investigate, not a semantic one.">traceback text with no disagreements mention</failure>
      <system-out>--------------------------------- Captured Out ---------------------------------
scan report: agreements=96 disagreements=0 timeout_count=7 conclusive=96/103
</system-out>
    </testcase>
  </testsuite>
</testsuites>
"""


class TestParseJunitSystemOut:
    """pytest's default JUnit XML does NOT embed a captured print() inside <failure> at all --
    <system-out> is a SIBLING of <failure> within <testcase>, populated only when
    junit_logging=system-out (or an equivalent value) is configured (verified empirically
    against the exact print()-then-assert shape _assert_scan_report uses). The gating-floor
    classify() branch's "disagreements=0" check is only meaningful in production if
    parse_junit reads that sibling and folds it into the returned failure_text -- this is what
    makes the check load-bearing rather than a no-op that always falls through to NEW."""

    def test_system_out_is_folded_into_failure_text(self, tmp_path):
        junit_path = tmp_path / "junit.xml"
        junit_path.write_text(_JUNIT_XML_WITH_SYSTEM_OUT)
        results = list(classify_mod.parse_junit(str(junit_path)))
        assert len(results) == 1
        nodeid, outcome, duration, failure_text = results[0]
        assert outcome == "failed"
        assert "budget/performance regression to investigate, not a semantic one" in failure_text
        assert "disagreements=0" in failure_text


# ---------------------------------------------------------------------------
# Promotion-notice honesty rule (Phase 3): a run with ANY failure -- TIMING or
# NEW -- must report the streak as 0 and withhold READY TO PROMOTE, not just a
# NEW-classified failure. The historical (past-runs) component remains
# NEW-sensitive only (job conclusions) -- that residual limitation is
# unaffected by and out of scope for this helper.
# ---------------------------------------------------------------------------


class TestPromotionStreakHonesty:
    def test_any_failure_this_run_zeroes_streak_and_withholds_promotion(self):
        streak, ready = classify_mod.compute_promotion_streak(
            this_run_had_any_failure=True,
            past_run_successes=[True] * 25,
        )
        assert streak == 0
        assert ready is False

    def test_clean_run_extends_streak_over_past_successes(self):
        streak, ready = classify_mod.compute_promotion_streak(
            this_run_had_any_failure=False,
            past_run_successes=[True] * 19,
        )
        assert streak == 20
        assert ready is True

    def test_streak_breaks_at_first_past_failure(self):
        streak, ready = classify_mod.compute_promotion_streak(
            this_run_had_any_failure=False,
            past_run_successes=[True, True, False, True, True],
        )
        assert streak == 3
        assert ready is False


# ---------------------------------------------------------------------------
# Real-pytest regression test (Phase 1 of the laundering-guard fix): a
# synthetic-string test -- everything above this point -- can only ever assert
# against a hand-typed failure_text. It cannot express the actual defect, which
# is a property of how pytest ITSELF renders a two-assertion function's
# <failure> body: a failure at the SECOND of two sequential asserts embeds the
# FIRST (passing) assert's own f-string SOURCE verbatim (the literal
# `{report['disagreements']}` placeholder, never a rendered digit). Only a real
# `subprocess.run([sys.executable, "-m", "pytest", ...])` invocation, parsed
# through the real parse_junit + classify, can catch a laundering-guard
# regression that a hand-typed string would never reproduce.
# ---------------------------------------------------------------------------

_FIXTURE_MODULE_TEMPLATE = '''
def _assert_scan_report(report, min_conclusive):
    """Copied verbatim (shape and messages) from
    oracle/bimodal_logic/tests/test_cross_oracle_differential.py:748 --
    _assert_scan_report -- with no import of oracle/bimodal_logic/z3."""
    conclusive = report["total_formulas"] - report["timeout_count"]
    print(
        f"scan report: agreements={report['agreements']} "
        f"disagreements={report['disagreements']} "
        f"timeout_count={report['timeout_count']} "
        f"conclusive={conclusive}/{report['total_formulas']}"
    )
    assert report["disagreements"] == 0, (
        f"Self-comparison produced {report['disagreements']} disagreements among "
        f"conclusive results: []"
    )
    assert conclusive >= min_conclusive, (
        f"Only {conclusive} of {report['total_formulas']} formulas were conclusive "
        f"(floor={min_conclusive}); this is a "
        "budget/performance regression to investigate, not a semantic one."
    )


def NODEID_NAME():
    report = REPORT_DICT
    _assert_scan_report(report, min_conclusive=MIN_CONCLUSIVE)
'''


def _write_gating_fixture(
    tmp_path, *, agreements, disagreements, timeout_count, total_formulas, min_conclusive
):
    """Write a self-contained fixture module into tmp_path reproducing
    _assert_scan_report's exact two-assertion shape. Plain string substitution (not
    str.format()/an f-string) on the template above, so the template's own literal `{...}`
    f-string braces need no doubling. The generated report dict values determine which
    assertion fails first: `disagreements=0` lets the first assert pass and the floor assert
    fail (or pass, if `conclusive >= min_conclusive`); a nonzero `disagreements` makes the
    first assert fail immediately, before the floor assert is ever reached."""
    report_dict = (
        "{"
        f'"agreements": {agreements}, '
        f'"disagreements": {disagreements}, '
        f'"timeout_count": {timeout_count}, '
        f'"total_formulas": {total_formulas}'
        "}"
    )
    source = (
        _FIXTURE_MODULE_TEMPLATE
        .replace("NODEID_NAME", f"test_{classify_mod.GATING_FLOOR_NODEID_FRAGMENT}")
        .replace("REPORT_DICT", report_dict)
        .replace("MIN_CONCLUSIVE", str(min_conclusive))
    )
    fixture_path = tmp_path / "test_gating_floor_fixture.py"
    fixture_path.write_text(source)
    return fixture_path


def _run_pytest_and_get_junit(fixture_path, tmp_path):
    """Run the fixture module under a real pytest subprocess with
    `junit_logging=system-out`, mirroring unstable-watch.yml's oracle-tree invocation. `cwd` and
    `--rootdir` are both pinned to `tmp_path` and `-p no:cacheprovider` is passed so no repo-root
    `pytest.ini`/`pyproject.toml` addopts or rootdir `conftest.py` can leak in and change
    behavior between a local run and CI. Asserts the subprocess actually ran and exactly one
    test failed (returncode 1) before returning the JUnit XML path -- any other returncode (e.g.
    a collection error) means the fixture itself is broken, not that the guard defect was
    reproduced, and must fail loudly rather than being parsed anyway."""
    xml_path = tmp_path / "junit.xml"
    result = subprocess.run(
        [
            sys.executable, "-m", "pytest", str(fixture_path),
            "-o", "junit_logging=system-out",
            f"--junitxml={xml_path}",
            "-p", "no:cacheprovider",
            f"--rootdir={tmp_path}",
        ],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1, (
        f"expected the fixture's real pytest subprocess to run and fail exactly one test "
        f"(returncode 1), got {result.returncode}\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    return xml_path


class TestRealPytestJunitRoundTrip:
    """A synthetic-string test cannot express this defect -- see the module-level comment
    above this class. Both directions are covered here through a real pytest subprocess."""

    def test_real_pytest_floor_failure_classifies_timing(self, tmp_path):
        """The documented false positive: disagreements=0 (first assert passes), conclusive
        96 < floor 100 (second/floor assert fails). Before the Phase 2 fix, the first assert's
        source-listing echo makes this misclassify NEW; after the fix, TIMING."""
        fixture_path = _write_gating_fixture(
            tmp_path,
            agreements=96, disagreements=0, timeout_count=7, total_formulas=103,
            min_conclusive=100,
        )
        xml_path = _run_pytest_and_get_junit(fixture_path, tmp_path)
        results = list(classify_mod.parse_junit(str(xml_path)))
        assert len(results) == 1
        nodeid, outcome, duration, failure_text = results[0]
        assert outcome == "failed"
        assert classify_mod.GATING_FLOOR_NODEID_FRAGMENT in nodeid
        # Confirm the fixture actually reproduces the source-listing echo first -- a fixture
        # that fails to reproduce it fails HERE, with a distinct message, rather than the
        # classification assertion below passing or failing for the wrong reason.
        assert "Self-comparison produced" in failure_text, (
            "fixture did not reproduce the source-listing echo; construction error, not the "
            "documented defect"
        )
        assert classify_mod.classify(nodeid, duration, failure_text) == "TIMING"

    def test_real_pytest_disagreement_failure_still_classifies_new(self, tmp_path):
        """The laundering guard's positive direction, driven through real pytest: a genuine
        disagreements != 0 failure (first assert fails, rendered "3 disagreements") must still
        classify NEW -- a real soundness bug must never launder into TIMING."""
        fixture_path = _write_gating_fixture(
            tmp_path,
            agreements=96, disagreements=3, timeout_count=7, total_formulas=103,
            min_conclusive=100,
        )
        xml_path = _run_pytest_and_get_junit(fixture_path, tmp_path)
        results = list(classify_mod.parse_junit(str(xml_path)))
        assert len(results) == 1
        nodeid, outcome, duration, failure_text = results[0]
        assert outcome == "failed"
        assert "Self-comparison produced 3 disagreements" in failure_text
        assert classify_mod.classify(nodeid, duration, failure_text) == "NEW"
