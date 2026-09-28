# Research Report: Fix logos subtheory-orchestration meta-test timeout

- **Task**: 208 - Fix logos subtheory meta test timeout
- **Started**: 2026-09-27T23:54:00Z
- **Completed**: 2026-09-28T00:30:00Z
- **Effort**: ~35 minutes
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`
  - `.github/workflows/tests.yml` (CI gate invocation shape)
  - `code/pyproject.toml` (`[tool.pytest.ini_options]` marker registry, `testpaths`)
  - `.github/workflows/unstable-watch.yml` (existing non-gating scheduled-workflow pattern)
  - `code/tests/ci/test_timing_marker_coverage.py` (marker-coverage AST guard)
  - `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (only other `subprocess`
    user under `theory_lib/*/tests/`)
  - Local measurements on an idle host (see Findings)
- **Artifacts**: `specs/208_fix_logos_subtheory_meta_test_timeout/reports/01_logos-subtheory-meta-test-timeout.md` (this report)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- `TestSubtheoryOrchestration::test_all_subtheory_tests_pass` re-executes, via a serial
  `subprocess.run` loop over four nested `pytest` invocations, test suites that CI's own gate
  (`.github/workflows/tests.yml`) already collects and runs directly in the same job — confirmed
  by `--collect-only`, which shows 127 of those exact test nodes present in the gate's own
  3099-item selection.
- No unique coverage was found that only the subprocess reinvocation provides. Imports in every
  subtheory test file are absolute (package-qualified), none of the four subtheory `tests/`
  directories has its own `conftest.py`, and no module-level mutable/global cache exists in
  `logos/operators.py` or `logos/semantic/` that a fresh-subprocess run would exercise
  differently than in-process collection. The one property a subprocess loop could uniquely
  guard — "these subtheories don't conflict when loaded together" — is already asserted
  in-process, cheaply, by `test_no_operator_conflicts` and `test_dependency_resolution` in the
  same file.
- Local measurement confirms the wall time is highly load-sensitive and already straddles the CI
  per-test ceiling: this run measured 136.54s in isolation on an idle host, versus the dispatch's
  own prior 320.90s measurement on the same test with no intervening code change — a 2.4x swing
  that corroborates the "boundary case" framing rather than a deterministic failure.
- Subprocess overhead is *not* the primary cost: running the same four subtheory suites directly,
  in one process, serially, took 134.91s — statistically indistinguishable from the subprocess
  version's 136.54s. The cost is re-executing 418 Z3-backed tests a second time, not spawning
  processes.
- Those same 418 tests, run with `-n 4` (matching CI's actual parallel-pass mechanism), complete
  in 52.13s — confirming they already parallelize well once merged into the ordinary direct-run
  pool, and that no single one of them risks the 300s per-test ceiling the way the monolithic
  meta-test does.
- No sibling theory (`bimodal`, `exclusion`, `imposition`) has the same nested-`pytest`-via-
  `subprocess` pattern; `bimodal`'s only `subprocess` user is an unrelated Lean certificate
  checker (`_lean_check.py`), which shells out to `lake exe check_certificate`, not to a nested
  `pytest`.
- **Recommendation: delete `test_all_subtheory_tests_pass`** rather than optimize it. This is a
  duplication-with-worse-diagnostics test, not a test carrying a distinct isolation guarantee;
  deleting it removes ~135-320s of duplicate, load-sensitive, single-item CI risk with zero loss
  of gating coverage, since the same 418 tests remain directly collected (with full pytest
  tracebacks, not a captured-`stderr` summary) by the same gate.

## Context & Scope

Task 208 asks for a fix to
`code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass`,
which the dispatch measured at 320.90s in isolation against CI's 300s per-test ceiling
(`.github/workflows/tests.yml`'s `--timeout=300 --timeout-method=thread`), and which has been
observed both passing and failing across two runs of the same full-repository gate on the same
tree with no code change — the signature of a test sitting on its timeout boundary rather than a
deterministic regression.

The dispatch explicitly forbids raising the timeout (hides cost rather than fixing it), requires
establishing whether the test adds coverage beyond direct collection before choosing an approach,
and requires comparing at least four alternatives: deletion, in-process replacement of the
independence property, marker-based relocation to a serial/scheduled path, and parallelizing the
subprocess loop. It also asks whether sibling theories share the same pattern (checked; they do
not — see Findings).

This report only investigates and recommends; no source files were modified. `.dispatch/3.md`
names `specs/208_fix_logos_subtheory_meta_test_timeout/reports/` as the sole output for this
round.

## Findings

### 1. What the test currently asserts

`test_all_subtheory_tests_pass` (lines 148-176 of the test file) loops over the four subtheory
names (`extensional`, `modal`, `constitutive`, `counterfactual`), and for each one whose
`subtheories/{name}/tests` directory exists, runs:

```
subprocess.run([sys.executable, '-m', 'pytest', str(test_path), '-v', '--tb=short'],
               capture_output=True, text=True, cwd=base_path)
```

and fails with a summary message (the captured `stderr` of each failing nested run) if any
nested pytest process returns non-zero. It asserts nothing else — no isolation-specific
assertion, no ordering assertion, no shared-state assertion. It is a pass/fail gate on "each
subtheory's own tests still pass," expressed via re-execution rather than via the outcome the
main session's own direct collection of those same files already produces.

### 2. Direct collection already covers the same tests

`code/pyproject.toml`'s `testpaths = ["tests", "src/model_checker"]` means every file under
`code/src/model_checker/theory_lib/logos/subtheories/*/tests/` is already collected by the exact
CI invocation in `.github/workflows/tests.yml`
(`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not
xdist_serial" -n 4 ...`). A `--collect-only` run against that identical marker expression
confirms 127 matching subtheory-example test nodes are present in the resulting 3099-item
selection (out of 3237 collected before marker deselection). The meta-test's nested subprocess
calls therefore re-run tests the surrounding session has already run once, directly, in the same
job.

### 3. No isolation property is uniquely exercised by the subprocess reinvocation

Checked and ruled out as reasons the subprocess indirection could matter:

- **cwd-dependent imports**: every subtheory test file (e.g.
  `subtheories/modal/tests/test_modal_examples.py`) imports via fully-qualified
  `model_checker.theory_lib.logos...` paths, not relative/cwd-sensitive imports. Running from the
  repository root (direct collection) versus `cwd=base_path` (the subprocess call) makes no
  difference to what is importable.
- **Per-subtheory `conftest.py` fixtures**: none exist (`find
  .../logos/subtheories -iname conftest.py` returned nothing), so there is no fixture-isolation
  concern a fresh interpreter would resolve differently than shared collection.
- **Module-level mutable/global state**: no cache/global registry pattern was found in
  `logos/operators.py` or the `logos/semantic/` package that a single shared pytest session could
  leak across subtheories in a way a subprocess would avoid.
- **Cross-subtheory conflict / dependency-resolution property**: this is the one property a
  fresh multi-subtheory load could plausibly guard, and it is already asserted in-process, in the
  same file, by `test_no_operator_conflicts` (loads all four subtheories together via one
  `LogosOperatorRegistry` and asserts `validate_operator_compatibility()` returns no issues) and
  `test_dependency_resolution` (asserts `modal` pulls in its `extensional`/`counterfactual`
  dependencies). Neither needs a subprocess to do this.

No git history changes or comments elsewhere in the module explain a further isolation rationale;
the commit history for this file traces back to the original theory refactor (task 126 / "all
tests pass" / "refactored theories") with no evidence of a later isolation-driven design intent.

### 4. Measured costs (idle host, no CI contention)

| Scenario | Wall time | Notes |
|---|---|---|
| `test_all_subtheory_tests_pass` alone (current subprocess-loop form) | 136.54s | This run; dispatch's own prior measurement of the identical test, same tree, no code change: 320.90s |
| Same 4 subtheory `tests/` dirs, run directly in one process, serial (no subprocess) | 134.91s (418 tests) | Statistically indistinguishable from the subprocess form — confirms subprocess/interpreter-startup overhead is not the dominant cost |
| Same 4 subtheory `tests/` dirs, run directly with `-n 4` | 52.13s (418 tests) | Matches CI's actual parallel-pass mechanism; ~2.6x faster than serial, and each test item is independently schedulable rather than one monolithic 130-320s block |

The 136.54s vs. 320.90s spread for the *identical* test on the *same* tree, with no intervening
change, is itself evidence: this test's wall time tracks ambient system load, which is exactly
why it flakes across the 300s boundary in CI's `-n 4` pool (four xdist workers plus this serial
loop's own nested-pytest processes all contend for the same cores) while sometimes finishing
comfortably under budget when the host happens to be less loaded.

### 5. Sibling-theory check

`grep -rl "subprocess.run\|subprocess.(Popen|call)" code/src/model_checker/theory_lib/*/tests/`
and a separate grep for `-m', 'pytest'`-shaped invocations found exactly one other `subprocess`
user under any theory's `tests/` tree: `bimodal/tests/_lean_check.py`, which resolves and invokes
`lake exe check_certificate` for Lean-certificate cross-checking — a different mechanism serving
a different purpose (external tool verification, not nested-pytest re-execution of the project's
own test suite). No sibling theory (`bimodal`, `exclusion`, `imposition`) has a nested-pytest
meta-test analogous to `test_all_subtheory_tests_pass`, so no mechanical fix needs to be applied
elsewhere.

### 6. Why the other three named alternatives are weaker than deletion

- **In-process replacement of the "independence property"**: there is no independence property
  left to preserve beyond what `test_no_operator_conflicts`/`test_dependency_resolution` already
  assert (Finding 3). Writing a new in-process check would duplicate those two tests for no
  additional guarantee.
- **`xdist_serial` or `slow` marking, moved off the per-PR path**: `xdist_serial` only moves a
  test to CI's second, un-parallelized pass — it does not shrink the work, and this test's
  measured 136-320s already exceeds the 300s ceiling even with *zero* contention (Finding 4,
  first row), so relocating it to the serial pass does not fix the timeout; it only relocates
  where it fails. `slow` is not even deselected by either of CI's two `-m` expressions in
  `tests.yml`, so it would stay exactly where it is today. A scheduled, non-gating workflow
  (mirroring `.github/workflows/unstable-watch.yml`'s pattern) is mechanically available, but
  pointless here: it would spend recurring CI minutes to monitor a property — "these subtheory
  tests still pass" — that the gate already checks on every PR via direct collection, for zero
  net new signal.
- **Parallelizing the subprocess loop**: would likely cut the loop's own wall time roughly in
  line with the `-n 4` measurement (Finding 4, third row), but it still re-executes all 418 tests
  a second time for no unique assertion, adds `ThreadPoolExecutor`/`multiprocessing` complexity to
  the test file, and does not remove the duplication `test_all_subtheory_tests_pass` was flagged
  for in the first place — it only makes the duplicate faster.

Deletion is the only option that removes both the duplicate compute and the single-item timeout
risk, without weakening the gate: the same 418 tests keep gating the PR path via direct
collection, with strictly *better* per-test diagnostics (full pytest tracebacks rather than a
captured-`stderr` summary of a nested `--tb=short` run).

## Decisions

- **Establish coverage overlap first (per dispatch instruction)**: confirmed complete overlap —
  direct collection already runs every test the meta-test's subprocess loop reruns, with no
  distinct isolation property uniquely exercised by the subprocess indirection (Findings 2-3).
- **Chosen fix**: delete `test_all_subtheory_tests_pass` from
  `test_subtheory_orchestration.py`, and drop its now-unused `subprocess`/`sys` imports if no
  other test in the file uses them (a check for other `subprocess`/`sys` references belongs to
  the implementation phase, immediately before editing).
- **No change proposed to sibling theories** — none share the pattern (Finding 5), consistent
  with the dispatch's "fix only logos here unless the same fix applies mechanically" constraint.
- **No timeout increase, no marker relocation, and no assertion dropped without justification**:
  the only assertion removed is "each subtheory's nested `pytest -v --tb=short` invocation
  returns 0," which is subsumed by the surviving direct-collection assertion "each of those same
  tests individually passes" — a strictly equivalent, already-gating check with better failure
  detail.

## Recommendations

1. In the implementation phase: remove `test_all_subtheory_tests_pass` from
   `TestSubtheoryOrchestration` in
   `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`,
   and remove the `subprocess`/`sys`/`Path` imports at the top of the file if implementation
   confirms (via grep within the file) that no other test still needs them (`Path` is also used
   by `test_type_hint_coverage`, so it likely stays; `subprocess` and `sys` are candidates for
   removal — verify before deleting).
2. Verify against the full repository gate under CI's exact invocation shape
   (`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and
   not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`, matching
   `.github/workflows/tests.yml`) both before and after the deletion, and report both node counts
   and wall times — the dispatch requires measured before/after numbers, not an estimate; this
   report's Finding 4 numbers are targeted, cheaper proxies (isolated meta-test, direct 4-dir
   run, and `-n 4` run) rather than the full ~3099-test gate run, which is expensive enough that
   it is better run once, deliberately, in the implementation/verification phase after the actual
   code change lands.
3. Confirm the surviving `TestSubtheoryOrchestration` tests
   (`test_all_subtheories_loadable`, `test_subtheory_protocol_compliance`,
   `test_operator_protocol_compliance`, `test_registry_protocol_compliance`,
   `test_semantics_protocol_compliance`, `test_dependency_resolution`,
   `test_no_operator_conflicts`, `test_iterator_contract_compliance`,
   `test_type_hint_coverage`) and `TestProtocolDefinitions` still pass unchanged after the
   deletion — none of them depend on `test_all_subtheory_tests_pass`.
4. No action needed for `bimodal`, `exclusion`, or `imposition` — confirmed no analogous pattern
   exists there (Finding 5).

## Risks & Mitigations

- **Risk**: a future contributor could reintroduce a similar re-execution pattern believing it
  adds isolation coverage. **Mitigation**: the implementation's commit message and/or a short
  code comment at the deletion site should record why it was removed (duplicate of direct
  collection, no unique isolation property, see this report), so the reasoning is not lost.
- **Risk**: the two targeted `-n 4`/serial comparisons in this report used only the 4 subtheory
  `tests/` directories in isolation, not the full 3099-test gate, so they do not capture
  cross-suite contention effects from the other ~2680 tests sharing the same 4 xdist workers.
  **Mitigation**: Recommendation 2 above requires a full-gate before/after measurement in the
  implementation phase before this fix is considered verified.

## Appendix

- CI gate invocation shapes referenced: `.github/workflows/tests.yml`'s two `pytest` steps (the
  `-n 4` parallel pass and the `xdist_serial`-only serial pass).
- Marker registry consulted: `code/pyproject.toml`'s `[tool.pytest.ini_options].markers`
  (`slow`, `xdist_serial`, `unstable`, `packaging`, `performance`, `countermodel`, `theorem`,
  `differential`) — no marker exists that both removes a test from the `-n 4` pass *and* keeps it
  gating without a second, non-parallel pass; `xdist_serial` is the only one that does either
  half, and (per Finding 6) does not solve this test's problem even so.
