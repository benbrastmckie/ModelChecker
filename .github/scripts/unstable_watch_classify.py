#!/usr/bin/env python3
"""Parse the JUnit XML from both `unstable-watch.yml` watch steps, classify every failure as
TIMING (the documented, expected timing signature) or NEW (a possible semantic regression),
append one JSON line per test to an append-only record, query this workflow's own run history
via `gh run list` for the cross-run trend (no committed state needed -- GitHub's run history is
already append-only), surface READY TO PROMOTE when the last 20 runs are all green, and write
the `$GITHUB_STEP_SUMMARY` table. Exits non-zero (and the job fails) only when a NEW-classified
failure is found -- a TIMING failure is recorded but leaves the job green, which is the entire
point of the `unstable` category (see code/docs/core/TESTING_GUIDE.md section 8.9).

**Extracted from `.github/workflows/unstable-watch.yml`'s inline heredoc** (originally an
untestable `python3 - <<'PY' ... PY` step) so this logic can be unit-tested per the project's
mandatory TDD requirement -- see `code/tests/ci/test_unstable_watch_classifier.py`. Importing
this module has no side effects (no file writes, no `gh` subprocess, no `sys.exit`): all of that
happens only under `if __name__ == "__main__":`, via `main()`.

Stdlib only -- the watch job installs no PyYAML and no third-party parsing dependency, and none
may be added here.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
import xml.etree.ElementTree as ET

# Default JUnit input paths (mirror the workflow's own `--junitxml` flags) and default record
# output path. Parameterizable rather than hard-coded inline, so a test can drive `run()`
# against `tmp_path` fixtures without touching `/tmp` or the cwd.
DEFAULT_CODE_JUNIT_PATH = "/tmp/watch-code.xml"
DEFAULT_ORACLE_JUNIT_PATH = "/tmp/watch-oracle.xml"
DEFAULT_RECORD_PATH = "unstable-watch-record.jsonl"

# Per-test max_time, used by the TIMING classification rule below. Keyed by a substring of the
# test's node id. UPDATE THIS DICT whenever a new test is marked `unstable` with a
# duration-based TIMING signature -- one whose failure surfaces at ~max_time, so "did it fail
# near its budget" is itself the signature (cross-reference the marking site's UNSTABLE_EXAMPLES
# set / entry-criteria comment, and TESTING_GUIDE.md section 8.9's "Currently marked" list). A
# test whose TIMING signature is NOT duration-based (e.g. a per-formula budget floor across many
# formulas, where no single wall-clock threshold is meaningful) gets its own dedicated branch in
# classify() instead of an entry here -- see GATING_FLOOR_NODEID_FRAGMENT immediately below for
# the second such branch, and follow that pattern (not this dict) for a third duration-independent
# marking.
MAX_TIME_BY_NODEID_FRAGMENT = {
    "BM_CM_1-example_case7": 60,
}

FAILURE_SIGNATURE = "Test failed for example:"

# Safety survey: FAILURE_SIGNATURE is the last statement of a *single*-assertion test
# (`test_example_cases`'s `assert result, f"Test failed for example: {example_name}"` --
# code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py) and pytest prints a
# frame's source only up to the point of failure, never past it -- so there is no earlier,
# textually-preceding sibling assertion whose source could leak this string into an unrelated
# failure's <failure> body. This is a POSITIVE confirmation signature (its presence confirms
# the expected failure), not a NEGATIVE guard against a co-located different failure mode --
# the structural distinction that makes DISAGREEMENT_SIGNATURE below dangerous as a bare
# substring and this one safe as one. Deliberately left unchanged; see the
# laundering-guard-fix-design research report's section 2 for the full survey.

# Gating-floor TIMING signature for
# TestGatingConclusiveScan::test_known_conclusive_population_self_consistent (see
# oracle/bimodal_logic/tests/test_cross_oracle_differential.py). Strings copied verbatim from
# `_assert_scan_report`'s actual assertion messages in that file, not retyped from memory.
GATING_FLOOR_NODEID_FRAGMENT = "test_known_conclusive_population_self_consistent"
GATING_FLOOR_SIGNATURE = "budget/performance regression to investigate, not a semantic one"

# Negative guard: a genuine disagreements != 0 failure on the gating node id is a real
# soundness bug and must never launder into TIMING. See classify()'s gating branch below.
#
# Anchored on the RENDERED count, not a bare substring. `_assert_scan_report`'s own source
# contains two sequential asserts; pytest's <failure> body for a failure at the SECOND (floor)
# assert embeds the full frame source up to and including the failing line -- which includes
# the FIRST (disagreements) assert's own f-string source verbatim:
# `f"Self-comparison produced {report['disagreements']} disagreements among "`. A bare
# substring match on "Self-comparison produced" matches that source listing even though no
# disagreement ever occurred, misclassifying every genuine gating-floor TIMING failure as NEW.
# Requiring a literal digit between "produced" and "disagreements" discriminates a RENDERED
# failure ("...produced 3 disagreements...") from the source listing (which only ever contains
# the unrendered `{report['disagreements']}` placeholder, never a literal digit) -- verified
# empirically against both the source-listing text and a real rendered failure. Remedy (b) (a
# machine-readable `UNSTABLE-SIGNATURE:` line emitted by `_assert_scan_report` itself) was
# considered and declined: that helper is called from at least five other test groups that pin
# its current message text, so changing what it prints has a much larger blast radius than
# anchoring this classifier's own regex. See the laundering-guard-fix-design research report's
# section 2 for the full comparison.
DISAGREEMENT_SIGNATURE = re.compile(r"Self-comparison produced \d+ disagreements")

# Tightened alongside DISAGREEMENT_SIGNATURE for consistency, NOT because it shares the same
# defect: `_assert_scan_report`'s print() f-string source is
# `f"disagreements={report['disagreements']} "` -- the literal substring "disagreements=0"
# never appears in a source listing (the value is interpolated, not written literally), only in
# the RENDERED <system-out> print() output. So the bare-substring form of this check was never
# exposed to the DISAGREEMENT_SIGNATURE defect. It shared only the general brittleness of an
# unanchored substring match (nothing pinned it to the "scan report:" line specifically), which
# this anchors. Validated against the real captured text from a subprocess-pytest run (not a
# hand-typed string) reproducing _assert_scan_report's exact shape.
ZERO_DISAGREEMENTS_PATTERN = re.compile(r"scan report:.*?disagreements=0", re.DOTALL)


def parse_junit(path):
    """Yield (nodeid, outcome, duration_s, failure_text) for every testcase in a JUnit XML
    file. outcome is one of 'passed', 'failed', 'error', 'skipped'. Returns nothing if the
    file does not exist (a step whose pytest never ran, rather than exit-5's "ran, found
    nothing").

    For a failed/error testcase, failure_text folds in the testcase's `<system-out>` sibling
    element (when present) alongside the `<failure>`/`<error>` message/text. This matters
    because pytest's default JUnit XML does NOT embed a captured `print()` inside `<failure>`
    at all -- `<system-out>` is populated only when `junit_logging` includes stdout (see
    `.github/workflows/unstable-watch.yml`'s oracle-tree pytest invocation, which sets
    `-o junit_logging=system-out` for exactly this reason: `_assert_scan_report`'s unconditional
    `print()` of `disagreements=...` is the ONLY place the gating-floor classify() branch's
    "disagreements=0" confirmation can come from).
    """
    if not os.path.exists(path):
        return
    tree = ET.parse(path)
    root = tree.getroot()
    suites = [root] if root.tag == "testsuite" else list(root)
    for suite in suites:
        for case in suite.findall("testcase"):
            classname = case.get("classname", "")
            name = case.get("name", "")
            nodeid = f"{classname}::{name}" if classname else name
            duration = float(case.get("time", "0") or "0")
            failure = case.find("failure")
            error = case.find("error")
            skipped = case.find("skipped")
            system_out = case.find("system-out")
            system_out_text = (system_out.text or "") if system_out is not None else ""
            if failure is not None:
                text = (
                    (failure.get("message") or "")
                    + " " + (failure.text or "")
                    + " " + system_out_text
                )
                yield nodeid, "failed", duration, text
            elif error is not None:
                text = (
                    (error.get("message") or "")
                    + " " + (error.text or "")
                    + " " + system_out_text
                )
                yield nodeid, "error", duration, text
            elif skipped is not None:
                yield nodeid, "skipped", duration, ""
            else:
                yield nodeid, "passed", duration, ""


def classify(nodeid, duration, failure_text):
    """Return 'TIMING' or 'NEW' for a failing/erroring testcase.

    Evaluated BEFORE the duration-based `max_time` fall-through below: the gating-floor branch
    for TestGatingConclusiveScan::test_known_conclusive_population_self_consistent. Duration
    plays NO part in this branch -- the budget is per-formula across up to 103 formulas, so no
    single wall-clock threshold is meaningful (unlike BM_CM_1's single-solve max_time). Returns
    TIMING only when ALL of: the node id matches the gating fragment, the floor signature is
    present, the rendered "disagreements=0" report line is present, AND the rendered
    disagreement-failure signature is absent; otherwise NEW. This is the laundering guard:
    `_assert_scan_report`'s two assertions fire in order (disagreements first, floor second), so
    a genuine floor failure necessarily implies the disagreements assertion already passed --
    that mutual-exclusivity is true of BEHAVIOR, but NOT of the TEXT pytest renders for the
    failure: a failure at the second assert embeds the first (passing) assert's own f-string
    SOURCE in the <failure> body, and that source contains the literal words "Self-comparison
    produced" with no rendered count. This is why both signature checks below match against the
    RENDERED count (a literal digit), not a bare substring -- matching the source listing would
    misclassify every genuine floor failure as NEW, and a disagreements != 0 failure is a real
    soundness bug that must never be classified TIMING regardless.

    TIMING (the documented BM_CM_1-style signature): the recorded duration is at least 0.8x the
    example's max_time AND the failure text carries the expected assertion message. A budget
    overrun surfaces as model_found == False, so it fails at ~max_time, never much faster.

    NEW (possible semantic regression): anything else -- a fast failure (well under budget,
    meaning the solver decided and the assertion still failed), a different assertion message,
    or an error/exception instead of an assertion.
    """
    if GATING_FLOOR_NODEID_FRAGMENT in nodeid:
        has_floor_signature = GATING_FLOOR_SIGNATURE in failure_text
        has_zero_disagreements = bool(ZERO_DISAGREEMENTS_PATTERN.search(failure_text))
        has_disagreement_failure = bool(DISAGREEMENT_SIGNATURE.search(failure_text))
        if has_floor_signature and has_zero_disagreements and not has_disagreement_failure:
            return "TIMING"
        return "NEW"

    max_time = None
    for fragment, mt in MAX_TIME_BY_NODEID_FRAGMENT.items():
        if fragment in nodeid:
            max_time = mt
            break
    if max_time is None:
        # No known max_time for this node id -- cannot confirm the timing signature, so treat
        # conservatively as NEW rather than silently assuming TIMING.
        return "NEW"
    if duration >= 0.8 * max_time and FAILURE_SIGNATURE in failure_text:
        return "TIMING"
    return "NEW"


def compute_promotion_streak(this_run_had_any_failure, past_run_successes):
    """Return (streak, ready_to_promote).

    Promotion-notice honesty rule: `this_run_had_any_failure` must be True if THIS run recorded
    a failure of ANY classification (TIMING or NEW), not just NEW -- a TIMING failure
    deliberately leaves the job's own exit code green (see classify()'s docstring and the
    module docstring above), but it is still a real failure of the marked test and must not
    silently extend a "zero failures" streak. `READY TO PROMOTE` firing after 20 nights of a
    TIMING-failing test would directly contradict TESTING_GUIDE.md section 8.9's exit criterion
    ("20 consecutive runs recording zero failures").

    `past_run_successes`: booleans derived from `gh run list` job conclusions for prior runs.
    This historical component is NECESSARILY NEW-sensitive only (a past run's *job* conclusion
    was success whenever that run had no NEW failure, even if it had a TIMING failure) --
    `unstable-watch.yml` does not persist enough state to recompute a past run's "any failure"
    status after the fact. This is a documented residual limitation, not something this function
    can fix: only THIS run's own contribution to the streak gets the honesty correction. See
    TESTING_GUIDE.md section 8.9's promotion-streak-limitation note and the step-summary's own
    "upper bound" wording for the same caveat surfaced to a human reader.
    """
    conclusions = [not this_run_had_any_failure] + list(past_run_successes)
    streak = 0
    for ok in conclusions:
        if ok:
            streak += 1
        else:
            break
    return streak, streak >= 20


def compute_per_test_promotion_streak(nodeid, this_run_classification, past_run_classifications):
    """Return (streak, ready_to_promote) for a SINGLE node id, computed from that node id's own
    classification history rather than the whole run's `any_failure` boolean.

    Unlike `compute_promotion_streak` above, this function's history component is
    classification-ACCURATE: `past_run_classifications` comes from parsing each prior run's own
    uploaded `unstable-watch-record-<run_id>` JSONL artifact (see `fetch_past_classifications`),
    which records the real per-nodeid `classification` value ("TIMING", "NEW", or "N/A" for a
    passing/non-failing testcase) -- not `gh run list`'s job-level conclusion, which is
    NEW-sensitive only. The residual limitation `compute_promotion_streak`'s own docstring and
    the module docstring record for the per-run path does NOT apply here.

    `nodeid`: the node id this streak is being computed for. Not consulted in the arithmetic
    below (the caller has already scoped `this_run_classification`/`past_run_classifications` to
    this one node id) -- carried in the signature so a caller and a test failure message can
    both name which node id a given streak belongs to, and so two node ids' streaks are always
    computed by two separate calls rather than one call silently averaging across node ids.

    `this_run_classification` / each entry of `past_run_classifications`: the recorded
    `classification` string for this node id in that run ("TIMING", "NEW", "N/A"), or `None` if
    that run has no record for this node id at all (the artifact could not be fetched, or the
    node id was not collected in that run for any other reason).

    Honesty rule, matching `compute_promotion_streak`'s: a run counts toward the streak ONLY when
    this node id was recorded in it AND that recorded classification is neither `TIMING` nor
    `NEW` -- ANY failure classification (of either kind) for THIS node id zeroes THIS node id's
    streak, exactly as `compute_promotion_streak` treats any failure as zeroing the (single,
    global) streak it computes. A run with NO record for this node id is treated
    CONSERVATIVELY -- as breaking the streak, not extending it -- because a missing record means
    the outcome cannot be confirmed, and assuming success on missing data would let a fetch
    failure silently manufacture progress toward `READY TO PROMOTE`.
    """
    def _is_clean(classification):
        return classification is not None and classification not in ("TIMING", "NEW")

    conclusions = [_is_clean(this_run_classification)] + [
        _is_clean(c) for c in past_run_classifications
    ]
    streak = 0
    for ok in conclusions:
        if ok:
            streak += 1
        else:
            break
    return streak, streak >= 20


def run(
    code_junit_path=DEFAULT_CODE_JUNIT_PATH,
    oracle_junit_path=DEFAULT_ORACLE_JUNIT_PATH,
    record_path=DEFAULT_RECORD_PATH,
    summary_path=None,
    repo="",
    current_run_id="",
):
    """The full classify-and-report pipeline, parameterized for testability (the workflow's
    `main()` supplies the real paths/env values; a test can drive this directly against
    `tmp_path` fixtures). Behavior is otherwise identical to the original heredoc. Returns the
    exit code: 0 unless a NEW-classified failure was found (1) -- the workflow's non-gating
    contract (a TIMING failure must never fail the job)."""
    records = []
    any_new = False
    any_failure = False
    summary_rows = []

    for path in (code_junit_path, oracle_junit_path):
        for nodeid, outcome, duration, failure_text in parse_junit(path):
            classification = "N/A"
            if outcome in ("failed", "error"):
                classification = classify(nodeid, duration, failure_text)
                # any_failure tracks ANY classification (TIMING or NEW), feeding the
                # promotion-notice honesty rule below -- distinct from any_new, which alone
                # still drives the job's own exit code per the non-gating contract.
                any_failure = True
                if classification == "NEW":
                    any_new = True
                    print(
                        f"::error title=UNSTABLE-WATCH: NEW FAILURE MODE::"
                        f"{nodeid} failed in a way that does not match its "
                        f"documented timing signature (duration={duration:.2f}s, "
                        f"outcome={outcome}). Investigate before assuming this "
                        f"is the known instability -- see TESTING_GUIDE.md "
                        f"section 8.9."
                    )
            records.append({
                "run_id": current_run_id,
                "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "nodeid": nodeid,
                "outcome": outcome,
                "duration_s": duration,
                "classification": classification,
            })
            summary_rows.append((nodeid, outcome, duration, classification))

    with open(record_path, "w") as fh:
        for rec in records:
            fh.write(json.dumps(rec) + "\n")

    # Cross-run trend via GitHub's own run history -- no committed state.
    try:
        out = subprocess.run(
            [
                "gh", "run", "list",
                "--repo", repo,
                "--workflow", "unstable-watch.yml",
                "--json", "conclusion,createdAt,databaseId,status",
                "--limit", "25",
            ],
            capture_output=True, text=True, check=True,
        )
        history = json.loads(out.stdout)
    except Exception as exc:  # pragma: no cover -- network/CLI dependent
        print(f"::warning::could not query run history via gh run list: {exc}")
        history = []

    # Exclude the current (still-in-progress) run from the historical list, and treat this
    # run's own outcome (no NEW failure) as the most recent entry.
    past = [
        r for r in history
        if str(r.get("databaseId")) != str(current_run_id)
        and r.get("status") == "completed"
    ]
    past.sort(key=lambda r: r.get("createdAt", ""), reverse=True)

    past_run_successes = [r.get("conclusion") == "success" for r in past]
    streak, ready_to_promote = compute_promotion_streak(any_failure, past_run_successes)

    # Covers BOTH marked-test patterns -- the duration-based MAX_TIME_BY_NODEID_FRAGMENT
    # entries and the duration-independent GATING_FLOOR_NODEID_FRAGMENT gating branch -- so a
    # READY TO PROMOTE notice names every currently-marked test, not just the first pattern
    # historically registered here.
    currently_unstable = sorted(
        set(MAX_TIME_BY_NODEID_FRAGMENT.keys()) | {GATING_FLOOR_NODEID_FRAGMENT}
    )
    if ready_to_promote:
        names = ", ".join(currently_unstable) if currently_unstable else "(none)"
        print(
            f"::notice title=READY TO PROMOTE::{names} -- {streak} consecutive "
            f"green unstable-watch runs. See TESTING_GUIDE.md section 8.9's "
            f"promotion path."
        )

    if summary_path:
        with open(summary_path, "a") as fh:
            fh.write("## Unstable Watch\n\n")
            fh.write(
                f"Consecutive green streak: **{streak}** / 20 (promotion threshold). "
                f"This run's own contribution reflects ANY failure (TIMING or NEW); the "
                f"historical component beyond it is derived from `gh run list` job "
                f"conclusions, which are NEW-sensitive only (a TIMING-failing run's job "
                f"still exits 0) -- so this number is an UPPER BOUND on the true "
                f"zero-failure streak. See TESTING_GUIDE.md section 8.9 and the uploaded "
                f"per-run `unstable-watch-record.jsonl` artifacts for the authoritative "
                f"per-test history.\n\n"
            )
            if ready_to_promote:
                fh.write("**READY TO PROMOTE** -- see TESTING_GUIDE.md section 8.9.\n\n")
            if summary_rows:
                fh.write("| Node ID | Outcome | Duration (s) | Classification |\n")
                fh.write("|---|---|---|---|\n")
                for nodeid, outcome, duration, classification in summary_rows:
                    fh.write(f"| `{nodeid}` | {outcome} | {duration:.2f} | {classification} |\n")
            else:
                fh.write("No `unstable`-marked tests were collected in either tree.\n")

    return 1 if any_new else 0


def main():
    return run(
        summary_path=os.environ.get("GITHUB_STEP_SUMMARY"),
        repo=os.environ.get("GITHUB_REPOSITORY", ""),
        current_run_id=os.environ.get("GITHUB_RUN_ID", ""),
    )


if __name__ == "__main__":
    sys.exit(main())
