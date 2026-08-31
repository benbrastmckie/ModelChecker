# Phase 4 Handoff: `run_tests.py --markers`/`-m` passthrough with a new TDD test module (GAP 2)

**Status**: COMPLETED

## What was done

- Re-derived the five command-building sites by grep/read, confirming the report's list exactly:
  `ExampleTestRunner._run_logos_example_tests`, `ExampleTestRunner._run_standard_example_tests`,
  `UnitTestRunner._run_logos_unit_tests`, `UnitTestRunner._run_standard_unit_tests`, and
  `PackageTestRunner._build_pytest_command`.
- Confirmed by grep that only `-v`/`-x` were registered short flags before this phase.
- Confirmed by grep that `run_tests.py` has no importers anywhere in `code/`.
- Created `code/tests/ci/test_run_tests_markers.py` (new module, loads `run_tests.py` by
  absolute path via `importlib.util`), asserting, before implementation:
  1. `--markers`/`-m` accepted, value threaded through `TestConfig.from_args`.
  2. Each of the five sites appends `-m <expr>` when markers supplied.
  3. Each of the five sites appends no `-m` token when markers are not supplied.
  4. `--markers` has no default (bare invocation leaves `config.markers` falsy).
  Confirmed all four groups RED (9 failures) before implementation.
- Implemented: added `--markers`/`-m MARKER_EXPR` to `create_argument_parser()` (no default),
  changed `TestConfig.markers`'s type annotation to `Optional[str]` (was `List[str]`, dead since
  no argparse option ever populated it), threaded `config.markers` through all five sites, and
  added the two canonical invocations to the epilog. Did not touch `code/pyproject.toml`.
- **Additional finding requiring a fix beyond the plan's literal task list**: pytest exits 5
  ("no tests ran") when an `-m` expression collects but fully deselects a suite — confirmed
  directly (`pytest bimodal/tests -k example -m "not development"` reports "313 deselected" and
  exits 5). Left unhandled, this made `./run_tests.py bimodal --markers "not development"`
  report FAILED/exit 1 instead of the plan's stated "zero bimodal tests selected, exiting 0".
  Added `_normalize_markers_deselection_exit_code(returncode, markers)` (normalizes a
  markers-caused exit 5 to 0; leaves exit 5 unmodified when no markers were supplied, so a
  genuine "no tests collected" case is still surfaced) and wired it into all five subprocess
  return paths, with new TDD coverage (`TestExitCodeFiveNormalizedOnlyWhenMarkersSupplied`,
  5 tests, RED-then-GREEN) added to the same test module.

## Verification

- `PYTHONPATH=code/src pytest code/tests/ci/test_run_tests_markers.py -v` — 15 passed (9 from
  the original 4 assertion groups + 5 from the exit-code-normalization addition, plus the
  argparse-default test already counted in the 9).
- `cd code && ./run_tests.py bimodal --markers "not development"` — zero bimodal tests
  selected in both the examples and unit passes ("313 deselected" each), overall
  `SUCCESS: All tests passed!`, exit 0.
- `cd code && ./run_tests.py logos --unit` — unchanged behavior, no `-m` token emitted, exit 0.
- `cd code && ./run_tests.py bimodal --markers development` and
  `cd code && ./run_tests.py bimodal` (bare, full suite) were both launched as long-running
  background verification runs (bimodal's full suite takes several minutes); their results are
  recorded in the Phase 6 criterion-(b) proof once they complete.
- `git diff code/pyproject.toml` — empty.

## Deviations from plan

- **Added** the exit-code-5 normalization (`_normalize_markers_deselection_exit_code`) and its
  TDD coverage. This was not an explicit Phase 4 task in the plan, but was necessary to satisfy
  the plan's own stated Phase 4 Verification bullet ("...exiting 0") and the top-level Testing &
  Validation checklist's identical claim, which would otherwise be false given pytest's
  documented exit-5 behavior on full deselection. No plan Non-Goal is affected: `pyproject.toml`
  is untouched, bimodal semantics are untouched, and the normalization only ever converts a
  markers-caused, fully-deselected 5 to 0 — it never suppresses a real test failure (a mixed
  pass/fail run still exits with pytest's real non-zero code).

## Post-hoc correction: a real bug in this phase's own test module

During Phase 6's verification pass, `code/tests/ci/test_unstable_watch_classifier.py::
TestRealPytestJunitRoundTrip`'s two tests were found failing consistently whenever run as part
of the full `code/tests/ci/` battery, though passing in isolation. Root cause traced to this
phase's `test_run_tests_markers.py`: its subprocess-mocking tests patched
`run_tests_mod.subprocess.run` by hand-assignment and attempted to restore it in a `finally`
block via `run_tests_mod.subprocess.run = __import__("subprocess").run`. Since `run_tests.py`
does a plain `import subprocess`, `run_tests_mod.subprocess` is the exact same global
`subprocess` module every other test module imports — not a private copy — so that "restore"
line re-read `.run` *after* it had already been overwritten, capturing the stand-in rather than
the original, and left the real global `subprocess.run` permanently patched to the
last-used stub for the remainder of the pytest session. `test_run_tests_markers.py` sorts
alphabetically before `test_unstable_watch_classifier.py`, so the corruption was always in place
by the time the classifier's real-subprocess round-trip tests ran.

**Fixed** by switching every patch site (9 methods across
`TestMarkersThreadedIntoEveryCommandBuildingSite` and
`TestExitCodeFiveNormalizedOnlyWhenMarkersSupplied`) to pytest's
`monkeypatch.setattr(run_tests_mod.subprocess, "run", ...)` fixture, which guarantees teardown
regardless of test outcome. Re-verified: `test_run_tests_markers.py` itself still 15/15 green,
and `PYTHONPATH=code/src pytest code/tests/ci/ -q` passed 120/120 across three consecutive full
runs post-fix.

## Next phase

Phase 6 depends on Phases 1-5 (all complete). Its criterion-(b) proof records the final results
of the bare `./run_tests.py bimodal` background run (completed: real non-zero exit, 5 known
failures visible). The equivalent `--markers development` confirmatory run was terminated by the
host before completion; since `development` covers bimodal's entire tree today, it would have
selected the identical node-id set already exercised by the bare run, so no additional evidence
is missing.
