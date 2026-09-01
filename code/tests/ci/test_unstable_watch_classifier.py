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
import json
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
# The raw SOURCE-LISTING f-string _assert_scan_report's first assert carries, verbatim -- what
# pytest embeds in a <failure> body for a failure at the SECOND (floor) assert, since the first
# assert's own source is textually earlier in the same function. Note this has no literal digit
# where a rendered failure would have one -- `{report['disagreements']}` is never interpolated
# in a source listing, only in the rendered print()/assertion output.
DISAGREEMENT_SOURCE_LISTING = (
    "f\"Self-comparison produced {report['disagreements']} disagreements among \""
)
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

    def test_disagreement_source_listing_does_not_match_anchored_pattern(self):
        """Synthetic companion to TestRealPytestJunitRoundTrip: pins the discrimination
        property directly against the classifier's own compiled pattern, independent of the
        subprocess-pytest path. The raw source-listing f-string (no literal digit) must NOT
        match DISAGREEMENT_SIGNATURE -- if it did, the laundering-guard defect this task fixes
        would still be live."""
        assert classify_mod.DISAGREEMENT_SIGNATURE.search(DISAGREEMENT_SOURCE_LISTING) is None
        # Sanity check on the positive side: a rendered failure (a literal digit) does match.
        assert classify_mod.DISAGREEMENT_SIGNATURE.search(DISAGREEMENT_MESSAGE) is not None


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


# ---------------------------------------------------------------------------
# Per-node-id promotion streak (Phase 3): a pure, network-free primitive
# alongside compute_promotion_streak, computed from ONE node id's own
# classification history rather than the whole run's any_failure boolean --
# the defect this fixes is two marked node ids' promotion paths being coupled
# through a single shared streak.
# ---------------------------------------------------------------------------


class TestPerTestPromotionStreak:
    def test_clean_20_run_history_reaches_ready_to_promote(self):
        streak, ready = classify_mod.compute_per_test_promotion_streak(
            "BM_CM_1-example_case7",
            this_run_classification="N/A",
            past_run_classifications=["N/A"] * 19,
        )
        assert streak == 20
        assert ready is True

    def test_single_timing_in_window_zeroes_the_streak(self):
        # this_run ("N/A") plus the two leading "N/A" past entries count (streak=3), then the
        # "TIMING" entry breaks the run of clean entries -- the remaining "N/A" entries past it
        # are never reached, matching compute_promotion_streak's own break-on-first-failure walk.
        streak, ready = classify_mod.compute_per_test_promotion_streak(
            "BM_CM_1-example_case7",
            this_run_classification="N/A",
            past_run_classifications=["N/A", "N/A", "TIMING", "N/A"] + ["N/A"] * 16,
        )
        assert streak == 3
        assert ready is False

    def test_single_new_in_window_zeroes_the_streak(self):
        streak, ready = classify_mod.compute_per_test_promotion_streak(
            "test_known_conclusive_population_self_consistent",
            this_run_classification="NEW",
            past_run_classifications=["N/A"] * 19,
        )
        assert streak == 0
        assert ready is False

    def test_missing_record_breaks_the_streak_conservatively(self):
        """A run with no record for this node id (artifact fetch failure, or the node id was
        not collected) must not be assumed clean -- it breaks the streak just like a real
        failure, rather than being silently skipped or treated as success."""
        streak, ready = classify_mod.compute_per_test_promotion_streak(
            "BM_CM_1-example_case7",
            this_run_classification="N/A",
            past_run_classifications=["N/A", "N/A", None, "N/A"] + ["N/A"] * 16,
        )
        assert streak == 3
        assert ready is False

    def test_two_nodeids_with_divergent_histories_yield_divergent_streaks(self):
        """THE DEFECT THIS FIXES: two marked node ids' promotion paths must be independent. A
        clean BM_CM_1 history reaches its own streak/readiness regardless of the gating test's
        own (here, currently-failing) history, and vice versa -- neither call's result may
        depend on the other's classifications."""
        bm_cm_1_streak, bm_cm_1_ready = classify_mod.compute_per_test_promotion_streak(
            "BM_CM_1-example_case7",
            this_run_classification="N/A",
            past_run_classifications=["N/A"] * 19,
        )
        gating_streak, gating_ready = classify_mod.compute_per_test_promotion_streak(
            "test_known_conclusive_population_self_consistent",
            this_run_classification="TIMING",
            past_run_classifications=["TIMING"] * 19,
        )
        assert bm_cm_1_streak == 20
        assert bm_cm_1_ready is True
        assert gating_streak == 0
        assert gating_ready is False


# ---------------------------------------------------------------------------
# run()-level wiring (Phase 4): drives run() directly against tmp_path JUnit
# fixtures with past_runs_fn/fetch_past_classifications_fn injected -- no
# real `gh` CLI or network access -- confirming the per-test streak actually
# reaches READY TO PROMOTE independently per node id, and that run()'s
# return code is unaffected by any of this wiring.
# ---------------------------------------------------------------------------

_CODE_JUNIT_BM_CM_1_PASSED = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal" name="test_example_cases[BM_CM_1-example_case7]" time="45.0"></testcase>
  </testsuite>
</testsuites>
"""

_CODE_JUNIT_BM_CM_1_TIMING_FAILURE = f"""<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal" name="test_example_cases[BM_CM_1-example_case7]" time="60.94">
      <failure message="{BM_CM_1_FAILURE_TEXT}">traceback text</failure>
    </testcase>
  </testsuite>
</testsuites>
"""

_ORACLE_JUNIT_GATING_ERROR_FAILURE = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="TestGatingConclusiveScan" name="test_known_conclusive_population_self_consistent" time="41.0">
      <error message="OracleTimeoutError: solve exceeded timeout_ms=40000">traceback</error>
    </testcase>
  </testsuite>
</testsuites>
"""


def _fake_past_runs_20(repo, current_run_id):
    """19 fake prior COMPLETED runs. Job `conclusion` is irrelevant to the per-test streak
    wiring under test here -- that streak is driven entirely by the injected
    fetch_past_classifications_fn below, not by gh run list's job-level conclusions."""
    return [
        {
            "databaseId": 9000 + i,
            "conclusion": "success",
            "createdAt": f"2026-07-{(i % 28) + 1:02d}T05:00:00Z",
            "status": "completed",
        }
        for i in range(19)
    ]


def _fake_fetch_clean_bm_cm1_dirty_gating(repo, nodeids, past_run_ids, field="classification"):
    """BM_CM_1 has a spotless 19-run classification history; the gating test has been failing
    NEW on every prior run too (moot for this run's own gating result, which already fails NEW
    on its own current-run classification regardless of history)."""
    return {
        nodeid: (
            ["N/A"] * len(past_run_ids) if "BM_CM_1" in nodeid else ["NEW"] * len(past_run_ids)
        )
        for nodeid in nodeids
    }


class TestRunPerTestStreakWiring:
    def test_clean_bm_cm1_and_failing_gating_yields_ready_for_bm_cm1_only(self, tmp_path, capsys):
        """A clean BM_CM_1 history (this run passed, 19 prior clean runs) plus a gating test
        that fails NEW this run must produce READY TO PROMOTE naming BM_CM_1 alone -- never
        both, and never the gating test, which is nowhere close to its own streak."""
        code_xml = tmp_path / "code.xml"
        code_xml.write_text(_CODE_JUNIT_BM_CM_1_PASSED)
        oracle_xml = tmp_path / "oracle.xml"
        oracle_xml.write_text(_ORACLE_JUNIT_GATING_ERROR_FAILURE)
        record_path = tmp_path / "record.jsonl"

        exit_code = classify_mod.run(
            code_junit_path=str(code_xml),
            oracle_junit_path=str(oracle_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="777",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        captured = capsys.readouterr()
        notice_lines = [
            line for line in captured.out.splitlines()
            if line.startswith("::notice title=READY TO PROMOTE::")
        ]
        assert len(notice_lines) == 1
        notice = notice_lines[0]
        assert "BM_CM_1-example_case7" in notice
        assert "test_known_conclusive_population_self_consistent" not in notice
        # The gating test's own current-run failure classifies NEW -- run()'s return code is
        # driven solely by any_new, unaffected by the per-test streak/notice wiring above.
        assert exit_code == 1

    def test_failing_bm_cm1_yields_no_ready_to_promote_notice(self, tmp_path, capsys):
        """BM_CM_1 failing TIMING this run must not be READY TO PROMOTE (its own streak is
        zeroed by this run's failure); with no gating testcase collected at all (oracle_junit_path
        points at a file that does not exist -- the "no unstable test in this tree" case
        parse_junit already handles), no notice should print at all."""
        code_xml = tmp_path / "code.xml"
        code_xml.write_text(_CODE_JUNIT_BM_CM_1_TIMING_FAILURE)
        missing_oracle_xml = tmp_path / "does-not-exist.xml"
        record_path = tmp_path / "record.jsonl"

        exit_code = classify_mod.run(
            code_junit_path=str(code_xml),
            oracle_junit_path=str(missing_oracle_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="778",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        captured = capsys.readouterr()
        assert "READY TO PROMOTE" not in captured.out
        # A TIMING-only failure must never fail the job -- the non-gating contract, unaffected
        # by the per-test streak/notice wiring.
        assert exit_code == 0


# ---------------------------------------------------------------------------
# Phase 3: DEV_STATUS classification path -- a third, optional JUnit input of
# `development`-marked results. Every dev-input testcase is recorded with
# classification == "DEV_STATUS" and its true outcome, regardless of pass/fail/error,
# and NEVER feeds any_new or any_failure (see run()'s dev_junit_path parameter and the
# module docstring's DEV_STATUS contract paragraph). A missing dev JUnit file is
# tolerated exactly like a missing code/oracle file.
# ---------------------------------------------------------------------------

_DEV_JUNIT_FAILING = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal_future" name="test_frame_axiom_not_yet_implemented" time="0.02">
      <failure message="AssertionError: frame axiom not yet enforced">traceback text</failure>
    </testcase>
  </testsuite>
</testsuites>
"""

_DEV_JUNIT_PASSING = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal_future" name="test_frame_axiom_now_passes" time="0.03"></testcase>
  </testsuite>
</testsuites>
"""

_DEV_JUNIT_ERROR = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal_future" name="test_collection_broken" time="0.0">
      <error message="ImportError: cannot import name 'not_yet_defined'">traceback text</error>
    </testcase>
  </testsuite>
</testsuites>
"""

# Deliberately shares BM_CM_1's currently_unstable fragment in its node id, to drive the
# overlap test below -- a real workflow would never mark the same test both `unstable` and
# `development`, but the classifier must defend against a dev record's node id happening to
# contain a currently-unstable fragment regardless.
_DEV_JUNIT_OVERLAPPING_FRAGMENT = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_bimodal" name="test_example_cases[BM_CM_1-example_case7]" time="0.01"></testcase>
  </testsuite>
</testsuites>
"""

_CODE_JUNIT_A_CLEAN_PASS = """<?xml version="1.0" encoding="utf-8"?>
<testsuites>
  <testsuite name="pytest" tests="1">
    <testcase classname="test_unrelated" name="test_something_fine" time="0.01"></testcase>
  </testsuite>
</testsuites>
"""


def _five_successful_past_runs(repo, current_run_id):
    return [
        {
            "databaseId": 100 + i,
            "conclusion": "success",
            "createdAt": f"2026-07-{i + 1:02d}T05:00:00Z",
            "status": "completed",
        }
        for i in range(5)
    ]


def _fake_fetch_no_history(repo, nodeids, past_run_ids, field="classification"):
    return {nodeid: [None] * len(past_run_ids) for nodeid in nodeids}


class TestDevStatusClassification:
    def test_failing_dev_test_yields_dev_status_record_and_exit_code_zero(self, tmp_path):
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_FAILING)
        record_path = tmp_path / "record.jsonl"

        exit_code = classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="900",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        assert exit_code == 0
        records = [json.loads(line) for line in record_path.read_text().splitlines()]
        assert len(records) == 1
        assert records[0]["classification"] == "DEV_STATUS"
        assert records[0]["outcome"] == "failed"

    def test_failing_dev_test_does_not_set_any_new(self, tmp_path, capsys):
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_FAILING)
        record_path = tmp_path / "record.jsonl"

        classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="901",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        captured = capsys.readouterr()
        assert "UNSTABLE-WATCH: NEW FAILURE MODE" not in captured.out

    def test_failing_dev_test_does_not_feed_any_failure_via_legacy_streak(self, tmp_path):
        """A failing development test must not zero an unstable test's streak via
        `any_failure`. A clean code/oracle run (no failures there) plus a failing dev test
        must leave the legacy per-run streak exactly as if the dev test did not exist -- the
        dev parse loop must never set `any_failure`, matching this module's own DEV_STATUS
        contract that it never gates and is never signature-matched."""
        code_xml = tmp_path / "code.xml"
        code_xml.write_text(_CODE_JUNIT_A_CLEAN_PASS)
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_FAILING)
        record_path = tmp_path / "record.jsonl"
        summary_path = tmp_path / "summary.md"

        exit_code = classify_mod.run(
            code_junit_path=str(code_xml),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            summary_path=str(summary_path),
            repo="acme/repo",
            current_run_id="902",
            past_runs_fn=_five_successful_past_runs,
            fetch_past_classifications_fn=_fake_fetch_no_history,
        )
        assert exit_code == 0
        summary_text = summary_path.read_text()
        assert "Legacy global streak" in summary_text
        # This clean run (any_failure must be False despite the dev failure) plus 5 clean
        # past runs == 6. If the dev loop wrongly set any_failure, this would read 0.
        assert "**6** / 20" in summary_text

    def test_missing_dev_junit_file_is_tolerated(self, tmp_path):
        record_path = tmp_path / "record.jsonl"
        exit_code = classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(tmp_path / "does-not-exist-dev.xml"),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="903",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        assert exit_code == 0
        assert record_path.read_text() == ""

    def test_passing_dev_test_is_recorded_with_dev_status_classification(self, tmp_path):
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_PASSING)
        record_path = tmp_path / "record.jsonl"

        classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="904",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        records = [json.loads(line) for line in record_path.read_text().splitlines()]
        assert len(records) == 1
        assert records[0]["outcome"] == "passed"
        assert records[0]["classification"] == "DEV_STATUS"

    def test_error_outcome_dev_test_is_recorded_as_dev_status(self, tmp_path):
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_ERROR)
        record_path = tmp_path / "record.jsonl"

        classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            repo="acme/repo",
            current_run_id="905",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        records = [json.loads(line) for line in record_path.read_text().splitlines()]
        assert len(records) == 1
        assert records[0]["outcome"] == "error"
        assert records[0]["classification"] == "DEV_STATUS"

    def test_dev_nodeid_overlapping_unstable_fragment_does_not_corrupt_streak_matching(
        self, tmp_path
    ):
        """A dev record whose node id happens to contain a currently_unstable fragment must
        never be allowed to supply that fragment's this-run classification for streak
        purposes: 'development wins' for the dev record's OWN classification (recorded as
        DEV_STATUS), but the unstable node id's own streak-relevant classification must come
        only from the code/oracle loop, and no double-counting occurs -- both records are
        written, never merged into one. A TIMING failure on BM_CM_1 this run must break its
        streak to 0 regardless of a same-fragment dev record."""
        code_xml = tmp_path / "code.xml"
        code_xml.write_text(_CODE_JUNIT_BM_CM_1_TIMING_FAILURE)
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_OVERLAPPING_FRAGMENT)
        record_path = tmp_path / "record.jsonl"
        summary_path = tmp_path / "summary.md"

        exit_code = classify_mod.run(
            code_junit_path=str(code_xml),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            summary_path=str(summary_path),
            repo="acme/repo",
            current_run_id="906",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=lambda repo, nodeids, past_run_ids, field="classification": {
                nodeid: (["N/A"] * len(past_run_ids)) for nodeid in nodeids
            },
        )
        assert exit_code == 0
        summary_text = summary_path.read_text()
        # BM_CM_1's own row must show a broken (0) streak -- if the dev record's DEV_STATUS
        # classification incorrectly overwrote the code loop's TIMING classification for
        # this fragment, the streak would wrongly read as clean (up to 20) instead of 0.
        assert "`BM_CM_1-example_case7` | 0 / 20" in summary_text
        # Two records were written -- the code-loop TIMING record and the dev-loop
        # DEV_STATUS record -- never merged/deduplicated into one.
        records = [json.loads(line) for line in record_path.read_text().splitlines()]
        classifications = {r["classification"] for r in records}
        assert "TIMING" in classifications
        assert "DEV_STATUS" in classifications


# ---------------------------------------------------------------------------
# Phase 4: Development trend reporting -- per-`development`-marked-node-id pass rate over
# the last N observed runs, reusing fetch_past_classifications (generalized with a `field`
# selector) rather than duplicating its cross-run artifact machinery. A progress signal,
# never a gate: no READY TO PROMOTE wording, no 20-run framing (those mean "the instability
# resolved", a different claim than "the theory is progressing toward completion").
# ---------------------------------------------------------------------------


class TestFetchPastClassificationsFieldSelector:
    def test_field_selector_returns_outcome_default_returns_classification_unchanged(
        self, tmp_path, monkeypatch
    ):
        """The default (no `field` argument) path must stay byte-for-byte the existing
        `classification`-returning behavior; the new `field="outcome"` path returns a
        different value from the SAME underlying record."""
        record_line = json.dumps(
            {"nodeid": "some/test.py::test_x", "outcome": "passed", "classification": "N/A"}
        )

        def _fake_gh_run_download(cmd, capture_output, text, check):
            dest_dir = Path(cmd[cmd.index("-D") + 1])
            (dest_dir / classify_mod.DEFAULT_RECORD_PATH).write_text(record_line + "\n")
            return subprocess.CompletedProcess(cmd, 0)

        monkeypatch.setattr(classify_mod.subprocess, "run", _fake_gh_run_download)

        default_result = classify_mod.fetch_past_classifications(
            "acme/repo", ["some/test.py::test_x"], [111]
        )
        assert default_result == {"some/test.py::test_x": ["N/A"]}

        outcome_result = classify_mod.fetch_past_classifications(
            "acme/repo", ["some/test.py::test_x"], [111], field="outcome"
        )
        assert outcome_result == {"some/test.py::test_x": ["passed"]}


class TestComputeDevPassRate:
    def test_counts_only_runs_with_a_record(self):
        passes, total = classify_mod.compute_dev_pass_rate(
            "some/dev/test.py::test_x",
            this_run_outcome="passed",
            past_run_outcomes=["passed", "failed", None, "passed"],
        )
        # This run (passed) + 3 non-None past runs; the one None entry is excluded from
        # both the numerator and the denominator.
        assert total == 4
        assert passes == 3

    def test_this_run_always_counts(self):
        passes, total = classify_mod.compute_dev_pass_rate(
            "some/dev/test.py::test_x", this_run_outcome="failed", past_run_outcomes=[]
        )
        assert total == 1
        assert passes == 0

    def test_missing_past_records_excluded_from_both_numerator_and_denominator(self):
        passes, total = classify_mod.compute_dev_pass_rate(
            "some/dev/test.py::test_x",
            this_run_outcome="passed",
            past_run_outcomes=[None, None, None],
        )
        assert total == 1
        assert passes == 1


def _fake_fetch_all_passed(repo, nodeids, past_run_ids, field="classification"):
    return {nodeid: (["passed"] * len(past_run_ids)) for nodeid in nodeids}


class TestDevelopmentWatchSummary:
    def test_summary_has_development_watch_section_with_pass_rate(self, tmp_path):
        dev_xml = tmp_path / "dev.xml"
        dev_xml.write_text(_DEV_JUNIT_PASSING)
        record_path = tmp_path / "record.jsonl"
        summary_path = tmp_path / "summary.md"

        classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(dev_xml),
            record_path=str(record_path),
            summary_path=str(summary_path),
            repo="acme/repo",
            current_run_id="950",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_all_passed,
        )
        summary_text = summary_path.read_text()
        assert "## Development Watch" in summary_text
        dev_section = summary_text.split("## Development Watch", 1)[1]
        assert "test_frame_axiom_now_passes" in dev_section
        # This run (passed) + 19 fake past "passed" runs from _fake_past_runs_20's window.
        assert "20/20" in dev_section
        assert "informational" in dev_section.lower()
        assert "never gating" in dev_section.lower()
        # Must not borrow the unstable-quarantine promotion vocabulary -- a different claim.
        assert "READY TO PROMOTE" not in dev_section
        assert "/ 20" not in dev_section

    def test_no_dev_records_omits_development_watch_section(self, tmp_path):
        record_path = tmp_path / "record.jsonl"
        summary_path = tmp_path / "summary.md"

        classify_mod.run(
            code_junit_path=str(tmp_path / "missing-code.xml"),
            oracle_junit_path=str(tmp_path / "missing-oracle.xml"),
            dev_junit_path=str(tmp_path / "missing-dev.xml"),
            record_path=str(record_path),
            summary_path=str(summary_path),
            repo="acme/repo",
            current_run_id="951",
            past_runs_fn=_fake_past_runs_20,
            fetch_past_classifications_fn=_fake_fetch_clean_bm_cm1_dirty_gating,
        )
        summary_text = summary_path.read_text()
        assert "## Development Watch" not in summary_text
        # Nothing else in the summary changes -- the Unstable Watch section is unaffected.
        assert "## Unstable Watch" in summary_text
