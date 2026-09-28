# Implementation Summary: Fix lazy-bounded-probe parallel flake and close the scanner blind spot

- **Task**: 213 - Fix the wall-clock flake in test_checker.py::TestLazyBoundedMemoizedProbe, and close the scanner blind spot that let it land unmarked
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T18:35:37Z
- **Completed**: 2026-09-28T18:44:11Z
- **Effort**: ~2.5 hours (per plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_lazy-bounded-probe-flake-fix.md, reports/01_lazy-bounded-probe-flake-fix.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Two independent defects sharing one root-cause shape. `test_import_performs_no_subprocess_call`
carried a redundant wall-clock assertion (`elapsed < 1.0`) inside a Python source string handed to
`subprocess.run`, which flaked under `-n 4` contention. The CI guard built to catch exactly that
shape (`code/tests/ci/test_timing_marker_coverage.py`) could not see it because its AST scan meets
one opaque `ast.Constant` where the clock read and bound assert actually live. Both items are now
fixed: the assertion is deleted, and the scanner now resolves and re-scans embedded source strings
passed to subprocess/exec-style call sites.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py`: removed the
  `import time`, `t = time.time()`, `elapsed = time.time() - t`, and `assert elapsed < 1.0,
  elapsed` lines from the subprocess-injected source in `test_import_performs_no_subprocess_call`,
  leaving only the import and the deterministic `assert m._memoized_result is m._UNSET` invariant.
  `subprocess.run(..., timeout=15)` and the `returncode == 0` assertion are unchanged.
  `test_probe_timeout_yields_unavailable_not_a_hang` (already `@pytest.mark.xdist_serial`-marked,
  out of scope) is byte-for-byte unchanged.
- `code/tests/ci/test_timing_marker_coverage.py`:
  - Label computation in `_find_unmarked_timing_tests` now falls back to `str(path)` when
    `path.relative_to(REPO_ROOT)` raises `ValueError`, so `tmp_path` fixture files can be scanned.
  - New helpers (`_is_source_executing_call`, `_local_string_bindings`,
    `_candidate_strings_from_value`, `_embedded_trees`, `_scanned_trees`, `_calls_clock_deep`,
    `_has_bound_assertion_deep`) resolve string arguments passed to
    `subprocess.run`/`call`/`check_call`/`check_output`/`Popen` or bare `exec`/`eval` — including
    a string first bound to a local name and then referenced by name, even nested one level
    inside a list/tuple literal — parse each resolved string, and re-apply the existing
    clock-read/bound-assert detectors against the union of the function's own AST and every
    embedded tree.
  - Both detection call sites (`_find_unmarked_timing_tests` and the inline duplicate inside
    `test_scan_finds_the_known_marked_inventory`) now route through the shared deep helpers.
  - Two new self-tests: `test_embedded_subprocess_source_is_flagged_when_unmarked` (positive) and
    `test_embedded_subprocess_source_respects_marker_suppression` (negative).
  - Module docstring extended to document the embedded-source-string route, its declared limits,
    and the reasoning for excluding `os.system` from the recognized call-target set.

## Decisions

- Deleted the wall-clock assertion outright rather than marking/widening it: the neighbouring
  `m._memoized_result is m._UNSET` assertion already checks the test's stated invariant
  deterministically and load-independently, and `subprocess.run(..., timeout=15)` already guards
  against a genuine hang, so `elapsed < 1.0` was a redundant, host-load-sensitive proxy.
- Implemented the AST extension (rather than the docstring-only escape hatch) since detection
  proved tractable: a narrow, structural rule (recognized call-target set + one-hop local-variable
  string binding + embedded-string re-parse) closes the gap without expanding into general
  dataflow analysis.
- Excluded `os.system` from the recognized call-target set: its argument is a shell command line,
  not Python source, so resolving and parsing it as Python would routinely raise `SyntaxError` and
  never match. Reasoning recorded in the module docstring per the module's existing
  `time.sleep()`-carve-out precedent.

## Plan Deviations

- Phase 2's optional `performance`-marker fixture variant (in addition to `xdist_serial`) was not
  added; the plan itself marked this variant optional, so this is not a deviation, just an
  explicitly-declared choice not to exercise the optional extra.
- `os.system` inclusion vs. exclusion was an explicit either/or choice offered by the plan;
  exclusion was chosen, with the reasoning recorded in the module docstring as required.
- No other deviations from the plan.

## Impacts

- The `test_import_performs_no_subprocess_call` wall-clock flake is eliminated by construction
  (the failure mode no longer exists) rather than merely marked to dodge parallel contention.
- The timing-marker coverage guard now has a positive detection mode for a previously invisible
  shape (clock-read-plus-bound-assert inside an embedded subprocess source string), closing the
  exact blind spot that let this flake land unmarked in the first place.
- No change to `code/pyproject.toml` marker registration; no change to
  `test_probe_timeout_yields_unavailable_not_a_hang`.

## Follow-ups

- None identified. The plan's non-goals (general dataflow analysis, `+=`/f-string string
  building, cross-function string passing) remain explicitly out of scope and are documented in
  the module docstring as declared limits, not open gaps.

## References

- `specs/213_fix_lazy_bounded_probe_parallel_flake/reports/01_lazy-bounded-probe-flake-fix.md`
- `specs/213_fix_lazy_bounded_probe_parallel_flake/plans/01_lazy-bounded-probe-flake-fix.md`
- `specs/213_fix_lazy_bounded_probe_parallel_flake/handoffs/phase-1-handoff-20260928113652.md`
- `specs/213_fix_lazy_bounded_probe_parallel_flake/handoffs/phase-2-3-handoff-20260928114500.md`
- `specs/213_fix_lazy_bounded_probe_parallel_flake/handoffs/phase-4-handoff-20260928115200.md`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py`
- `code/tests/ci/test_timing_marker_coverage.py`
