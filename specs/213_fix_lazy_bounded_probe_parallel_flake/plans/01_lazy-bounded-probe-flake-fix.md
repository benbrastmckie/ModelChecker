# Implementation Plan: Fix lazy-bounded-probe parallel flake and close the scanner blind spot

- **Task**: 213 - Fix the wall-clock flake in test_checker.py::TestLazyBoundedMemoizedProbe, and close the scanner blind spot that let it land unmarked
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/213_fix_lazy_bounded_probe_parallel_flake/reports/01_lazy-bounded-probe-flake-fix.md
- **Artifacts**: plans/01_lazy-bounded-probe-flake-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Two independent defects, one root cause shape. A wall-clock assertion (`elapsed < 1.0`) living
inside a Python source string that `test_import_performs_no_subprocess_call` hands to
`subprocess.run` flakes under `-n 4` contention, and the CI guard built to catch exactly that
shape (`code/tests/ci/test_timing_marker_coverage.py`) cannot see it, because its AST scan meets
one opaque `ast.Constant` where the clock read and the bound assert actually live. Item 1 deletes
the redundant assertion; Item 2 teaches the scanner to parse embedded source strings passed to
subprocess/exec-style call sites and re-apply its existing two-condition detection against them.
Done means: the assertion is gone, the extended scanner provably flags the pre-fix shape and
provably respects marker suppression through the new route, the known-marked inventory is
unchanged, and one full parallel gate run passes clean.

### Research Integration

The research report (`reports/01_lazy-bounded-probe-flake-fix.md`) confirmed by direct inspection
that the dispatch's scope correction is accurate (`test_probe_timeout_yields_unavailable_not_a_hang`
already carries `@pytest.mark.xdist_serial` at `test_checker.py:184` and is out of scope), pinned
the exact structural reason the scanner misses the shape (the `code = (...)` string is bound to a
local name, then referenced by name inside a list literal argument — so detection needs a
same-scope variable resolution step, not just literal-argument scanning), and established by
repo-wide grep that `test_checker.py` is the *only* file in `code/src/model_checker` or
`code/tests` combining `subprocess.run` with a clock function name. That last fact drives the
plan's shape: after Item 1 there will be zero real instances of the target shape left in the tree,
so Item 2's detection can only be proven by a synthetic fixture, and its non-regression can only
be proven by the known-inventory test staying green.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context was provided for this dispatch.

## Goals & Non-Goals

**Goals**:
- Remove the host-load-sensitive `elapsed < 1.0` assertion (and its now-dead supporting lines)
  from the subprocess source injected by `test_import_performs_no_subprocess_call`, preserving
  the deterministic `m._memoized_result is m._UNSET` invariant the test actually exists to check.
- Extend `code/tests/ci/test_timing_marker_coverage.py` so a clock-read-plus-bound-assert pair
  inside a string literal passed to a subprocess/exec-style call site is detected, including the
  intermediate-local-variable binding form actually used in the repo.
- Prove the extension with self-tests in the module's existing style: a synthetic unmarked fixture
  that IS flagged, and a marked variant that is NOT.
- Keep the existing known-marked inventory (`test_scan_finds_the_known_marked_inventory`) exactly
  as-is, with no new real-tree violations introduced by the broadened scan.

**Non-Goals**:
- Touching `test_probe_timeout_yields_unavailable_not_a_hang` in any way (already correctly
  marked; its `elapsed < 1.0` is against a mocked, never-sleeping invoke path).
- Marking or widening the bound in `test_import_performs_no_subprocess_call` instead of deleting
  it. Deletion is the decided approach (see Risks for the condition that would reopen this).
- General dataflow analysis in the scanner. String building across statements (`code = "a"` then
  `code += "b"`) and strings passed through intermediate functions stay out of scope, consistent
  with the module's existing structural-scan-not-dataflow posture.
- Any change to `code/pyproject.toml` marker registration — `xdist_serial` and `performance` are
  already registered and unaffected.
- Repeated parallel runs to "prove a negative." One clean full-gate run under `-n 4` is the
  agreed bar, per the dispatch.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Broadened scan produces false positives on unrelated subprocess call sites | M | L | The two-condition AND (clock-read node AND bound-assert node) is preserved unchanged; only the *source* of AST nodes widens. Phase 4 runs the real-tree scan and asserts zero new violations; research's repo-wide grep already found no other candidate file. |
| `_find_unmarked_timing_tests` calls `path.relative_to(REPO_ROOT)`, which raises `ValueError` for a `tmp_path` fixture file, breaking the self-test before detection is even reached | M | H | Phase 2 handles this explicitly: wrap the label computation in `try/except ValueError` falling back to `str(path)`. Real-tree labels (and therefore `MOCKED_CLOCK_ALLOWLIST` keys) are unchanged. |
| `test_scan_finds_the_known_marked_inventory` duplicates the detection logic inline; extending only `_find_unmarked_timing_tests` lets the two drift | M | M | Phase 3 routes both call sites through the same shared deep-detection helpers rather than editing one path only. Phase 4 verifies the inventory test still passes unmodified in expectation. |
| Landing the scanner extension before Item 1 would make `test_all_wall_clock_timing_assertions_are_marked` fail on the real `test_checker.py` | M | M | Encoded as a hard dependency: Phase 3 depends on Phase 1 as well as Phase 2. |
| Concurrent sibling task 214 shares this working tree with no declared `file_scope` | M | M | Re-read each target file immediately before editing; stage only this task's own hunks with an explicit file list (never `git add -A`, never a directory/glob pathspec); never run `git-snapshot.sh` in reverting default mode; treat an unexpected failure outside these two files as possibly a sibling's in-flight edit and report rather than "fix" it. |
| Deleting the timing assertion is judged to drop real coverage during review | L | L | The dispatch requires the case be made explicitly either way. The recorded case: the neighbouring `_UNSET` assertion checks the stated invariant deterministically and load-independently, and `subprocess.run(..., timeout=15)` independently guards a genuine hang. If review disagrees, the fallback is to mark the test `@pytest.mark.xdist_serial` and justify the bound in a comment — not to raise the number. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Delete the wall-clock assertion from the injected subprocess source [COMPLETED]

**Goal**: `test_import_performs_no_subprocess_call` no longer reads a clock or asserts a timing
bound, while still proving that importing the checker module does not eagerly resolve.

**Tasks**:
- [x] Re-read `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` immediately
      before editing (sibling task 214 shares this tree).
- [x] In `test_import_performs_no_subprocess_call` (currently ~line 141), reduce the injected
      `code` string to exactly the import plus the `_UNSET` assertion, dropping the `import time`,
      `t = time.time()`, `elapsed = time.time() - t`, and `assert elapsed < 1.0, elapsed` lines:
      ```python
      code = (
          "import model_checker.theory_lib.bimodal.semantic.checker as m\n"
          "assert m._memoized_result is m._UNSET, 'import must not resolve eagerly'\n"
      )
      ```
- [x] Leave `subprocess.run(..., timeout=15)` and `assert result.returncode == 0, ...` untouched —
      the timeout is the genuine-hang guard and the returncode assert is how the inner assertion
      surfaces.
- [x] Confirm `test_probe_timeout_yields_unavailable_not_a_hang` is byte-for-byte unchanged.
- [x] Commit this file alone with an explicit single-file `git add`.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` - delete four lines from
  the injected source string in one test function; no other edit.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -q`
  passes in full (not just the one test — the module's other tests share `checker_module` state).
- `git diff` for this file shows only the four deleted lines inside the one function.

---

### Phase 2: RED — self-tests for embedded-string detection [COMPLETED]

**Goal**: Two new self-tests in `test_timing_marker_coverage.py` that encode the required
behaviour and fail against the current scanner, plus the label fix that lets a `tmp_path` fixture
be scanned at all.

**Tasks**:
- [x] Re-read `code/tests/ci/test_timing_marker_coverage.py` immediately before editing.
- [x] In `_find_unmarked_timing_tests`, make the label computation tolerant of paths outside the
      repo: `try: label = str(path.relative_to(REPO_ROOT)) except ValueError: label = str(path)`.
      Real-tree labels — and therefore `MOCKED_CLOCK_ALLOWLIST` keys — are unchanged by this.
- [x] Add `test_embedded_subprocess_source_is_flagged_when_unmarked`: write a fixture module to
      `tmp_path` reproducing the pre-fix shape — a test function binding a local
      `code = ("import time\n" "t = time.time()\n" ... "assert elapsed < 1.0, elapsed\n")` and
      passing it by name inside `subprocess.run([sys.executable, "-c", code], ...)`, with no
      marker — and assert `_find_unmarked_timing_tests(fixture_path)` returns exactly one
      violation naming that function.
- [x] Add `test_embedded_subprocess_source_respects_marker_suppression`: the same fixture with
      `@pytest.mark.xdist_serial` on the function, asserting `_find_unmarked_timing_tests` returns
      `[]`. Do the same for `performance` if it costs nothing (both markers flow through the same
      `_REQUIRED_MARKERS` check, so one extra fixture variant is optional, not required). Deviation:
      implemented only the `xdist_serial` variant (the plan itself marked the `performance`
      variant optional).
- [x] Run both new tests and record that they fail for the right reason (the unmarked fixture is
      NOT flagged today, i.e. an empty violations list where one entry is expected) — a RED that
      errors on `relative_to` instead would mean the label fix did not land.
- [x] Do NOT commit a red state. This phase's output is staged into Phase 3's green commit.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts exactly two new test functions plus one `try/except`
label change, all inside the single file `code/tests/ci/test_timing_marker_coverage.py`. Confirm
at implementation time by reading the module before editing: if the fixture-writing style the
module already uses differs from `tmp_path` (it currently scans only real tree files, so there is
no in-module precedent), adopt `tmp_path` and note the deviation in the test docstring rather than
inventing a new fixtures directory.

**Files to modify**:
- `code/tests/ci/test_timing_marker_coverage.py` - `try/except ValueError` around the label
  computation; two new self-test functions.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_timing_marker_coverage.py -q` shows the two new
  tests failing (positive case unflagged) and the two pre-existing tests still passing.
- The RED failure message confirms an empty-violations assertion failure, not a `ValueError` or
  collection error.

---

### Phase 3: GREEN — extend the AST scan through embedded source strings [COMPLETED]

**Goal**: The scanner resolves string arguments to subprocess/exec-style call sites (including via
a simple same-scope local binding), parses them, and re-applies its existing clock-read and
bound-assert detectors against the parsed sub-trees — turning Phase 2's self-tests green without
disturbing the real-tree results.

**Tasks**:
- [x] Add a recognized-call-target set: `ast.Attribute` calls on `Name("subprocess")` with `attr`
      in `{run, call, check_call, check_output, Popen}`, plus bare `ast.Name` calls to
      `{exec, eval}`. `os.system` may be included on the same reasoning; if included, say so in
      the docstring, and if excluded, say why. (Excluded; reasoning recorded in the module
      docstring.)
- [x] Add a same-scope string-binding map built from simple `ast.Assign` nodes whose single target
      is a `Name` and whose value is an `ast.Constant` str. (Python folds the adjacent string
      literals in `code = ("a\n" "b\n")` at parse time, so no concatenation handling is needed for
      the live case; `+`-concatenation stays out of scope.)
- [x] Add a resolver that, for each matched call, collects candidate strings from `args` and
      `keywords`: direct `ast.Constant` strs, and `ast.Name` nodes resolved through the binding
      map — including names nested one level inside `ast.List`/`ast.Tuple` elements, which is what
      `[sys.executable, "-c", code]` requires.
- [x] Parse each resolved string under `try: ... except SyntaxError: continue`, and expose the
      results through shared deep helpers (e.g. `_scanned_trees(node)` returning the function node
      plus every parsed embedded tree, consumed by `_calls_clock_deep` / `_has_bound_assertion_deep`).
      A violation fires when the clock-read and bound-assert conditions are jointly satisfied
      across the *union* of the function's own nodes and the embedded trees — the same union
      semantics the existing one-hop helper case already uses.
- [x] Route BOTH detection call sites through the shared helpers: `_find_unmarked_timing_tests`
      and the inline duplicate inside `test_scan_finds_the_known_marked_inventory`. Leaving the
      latter on the old logic is the drift this task is meant to prevent.
- [x] Marker checking (function decorators, enclosing class decorators, module `pytestmark`) and
      `MOCKED_CLOCK_ALLOWLIST` semantics are unchanged.
- [x] Update the module docstring: extend the numbered detection description to name the embedded
      string-literal route and its declared limits (single-hop simple local binding only; no
      `+=`/f-string/cross-function building), in the same style as the existing deliberate
      `time.sleep()` carve-out.
- [x] Commit the whole Phase 2 + Phase 3 change to this file as one green commit.

**Timing**: 1 hour

**Depends on**: 1, 2

**Verification Tier**: local

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts that the entire extension fits in
`code/tests/ci/test_timing_marker_coverage.py` with no change to any scanned test file and no new
module. Confirm at implementation time by running the full-tree scan (Phase 4): if the broadened
detection flags any real file other than zero, the hypothesis is falsified and the new violation
must be triaged (genuine finding → mark that test; false positive → narrow the rule or allowlist
with a comment) before the phase closes.

**Files to modify**:
- `code/tests/ci/test_timing_marker_coverage.py` - new call-target set, binding map, string
  resolver, shared deep helpers; both detection sites rewired; docstring extended.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_timing_marker_coverage.py -q` — all four tests
  pass (two pre-existing, two new).
- Temporarily re-checking the pre-fix shape is unnecessary: Phase 2's synthetic fixture IS the
  pre-fix shape, so its now-passing positive case is the proof the extension would have caught
  the original defect.

**Escape hatch** (only if implementation discovers the AST rule is genuinely too broad or too
fragile): do not leave the gap silent. Record the decision and its reasoning in the module
docstring alongside the existing `time.sleep()` carve-out, naming the exact uncovered shape, and
report the decision in `.orchestrator-handoff.json`. Research found no evidence of infeasibility,
so this path requires an explicit finding, not a preference.

---

### Phase 4: Full-tree scan and single parallel gate run [NOT STARTED]

**Goal**: Confirm the broadened scan introduces no real-tree violations and that the flake is gone
from a contended run.

**Tasks**:
- [ ] Run the CI guard module against the real tree and confirm
      `test_all_wall_clock_timing_assertions_are_marked` and
      `test_scan_finds_the_known_marked_inventory` both pass unchanged.
- [ ] Run the full parallel gate once:
      `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
- [ ] Confirm no `test_import_performs_no_subprocess_call` failure in that run. Do NOT repeat the
      run to accumulate draws — Item 1's correctness is by construction, and the dispatch
      explicitly forbids proving a negative by repetition.
- [ ] If an unrelated failure appears in a file outside these two, check `git log`/`git status`
      first: it may be sibling task 214's in-flight edit, not a regression from this work. Report
      rather than silently fixing.
- [ ] Record the run's outcome (pass/fail counts, duration) in the handoff.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification only).

**Verification**:
- Guard module: 4 passed.
- Full parallel gate: clean pass, with `test_import_performs_no_subprocess_call` present and
  passing in the collected set.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -q` — all pass.
- [ ] `PYTHONPATH=code/src pytest code/tests/ci/test_timing_marker_coverage.py -q` — 4 passed
      (2 pre-existing + 2 new).
- [ ] New positive self-test flags the synthetic unmarked embedded-clock fixture.
- [ ] New negative self-test does not flag the `@pytest.mark.xdist_serial` variant.
- [ ] `test_scan_finds_the_known_marked_inventory`'s known set is unmodified and still fully found.
- [ ] One full parallel gate run under `-n 4` passes clean.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` — wall-clock assertion
  removed from the injected subprocess source.
- `code/tests/ci/test_timing_marker_coverage.py` — embedded-string detection, two new self-tests,
  label-computation fallback, extended docstring.
- `specs/213_fix_lazy_bounded_probe_parallel_flake/summaries/01_*-summary.md` — implementation
  summary.
- `specs/213_fix_lazy_bounded_probe_parallel_flake/.orchestrator-handoff.json` — phase accounting
  and the recorded gate-run outcome.

## Rollback/Contingency

Each phase touches exactly one file and each green state is committed, so rollback is a targeted
`git revert` of the specific commit(s) — no working-tree discard is required and none should be
attempted while sibling task 214 is active on this same tree.

- Phase 1 alone reverted: the flake returns but nothing else changes; the scanner (if Phase 3
  landed) would then correctly flag the restored shape, so revert Phase 3 with it or accept a red
  guard.
- Phase 3 reverted: the scanner returns to its current blind spot with Item 1's fix still in
  place — a safe, strictly-better-than-today state.
- If a genuine whole-tree rollback ever becomes necessary, use the snapshot-then-rollback recipe
  in `context/contracts/recovery.md`'s rollback rung (including its out-of-scope override flag),
  never a bare default-mode `git-snapshot.sh` call.
