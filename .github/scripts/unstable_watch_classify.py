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
# test's node id. UPDATE THIS DICT whenever a new test is marked `unstable` with a duration-based
# TIMING signature (cross-reference the marking site's UNSTABLE_EXAMPLES set / entry-criteria
# comment, and TESTING_GUIDE.md section 8.9's "Currently marked" list).
MAX_TIME_BY_NODEID_FRAGMENT = {
    "BM_CM_1-example_case7": 60,
}

FAILURE_SIGNATURE = "Test failed for example:"


def parse_junit(path):
    """Yield (nodeid, outcome, duration_s, failure_text) for every testcase in a JUnit XML
    file. outcome is one of 'passed', 'failed', 'error', 'skipped'. Returns nothing if the
    file does not exist (a step whose pytest never ran, rather than exit-5's "ran, found
    nothing").
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
            if failure is not None:
                text = (failure.get("message") or "") + " " + (failure.text or "")
                yield nodeid, "failed", duration, text
            elif error is not None:
                text = (error.get("message") or "") + " " + (error.text or "")
                yield nodeid, "error", duration, text
            elif skipped is not None:
                yield nodeid, "skipped", duration, ""
            else:
                yield nodeid, "passed", duration, ""


def classify(nodeid, duration, failure_text):
    """Return 'TIMING' or 'NEW' for a failing/erroring testcase.

    TIMING (the documented signature): the recorded duration is at least 0.8x the example's
    max_time AND the failure text carries the expected assertion message. A budget overrun
    surfaces as model_found == False, so it fails at ~max_time, never much faster.

    NEW (possible semantic regression): anything else -- a fast failure (well under budget,
    meaning the solver decided and the assertion still failed), a different assertion message,
    or an error/exception instead of an assertion.
    """
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
    summary_rows = []

    for path in (code_junit_path, oracle_junit_path):
        for nodeid, outcome, duration, failure_text in parse_junit(path):
            classification = "N/A"
            if outcome in ("failed", "error"):
                classification = classify(nodeid, duration, failure_text)
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
    streak = 0
    ready_to_promote = False
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

    this_run_success = not any_new
    conclusions = [this_run_success] + [
        r.get("conclusion") == "success" for r in past
    ]
    for ok in conclusions:
        if ok:
            streak += 1
        else:
            break

    currently_unstable = sorted(MAX_TIME_BY_NODEID_FRAGMENT.keys())
    if streak >= 20:
        ready_to_promote = True
        names = ", ".join(currently_unstable) if currently_unstable else "(none)"
        print(
            f"::notice title=READY TO PROMOTE::{names} -- {streak} consecutive "
            f"green unstable-watch runs. See TESTING_GUIDE.md section 8.9's "
            f"promotion path."
        )

    if summary_path:
        with open(summary_path, "a") as fh:
            fh.write("## Unstable Watch\n\n")
            fh.write(f"Consecutive green streak: **{streak}** / 20 (promotion threshold)\n\n")
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
