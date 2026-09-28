# Research Report: Fix lazy-bounded-probe parallel flake and close the scanner blind spot

- **Task**: 213 - Fix the wall-clock flake in test_checker.py::TestLazyBoundedMemoizedProbe, and close the scanner blind spot that let it land unmarked
- **Started**: 2026-09-28T18:20:00Z
- **Completed**: 2026-09-28T18:35:00Z
- **Effort**: ~1 hour (research only)
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` (target test, lines ~142-159)
  - `code/tests/ci/test_timing_marker_coverage.py` (scanner to extend)
  - `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` (evidence: 3 independent reproductions)
  - `code/pyproject.toml` (marker registration, `xdist_serial` / `performance`)
  - Live standalone reruns of both files during this research session (see Findings)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The dispatch's scope correction is confirmed correct by direct inspection: `test_probe_timeout_yields_unavailable_not_a_hang` already carries `@pytest.mark.xdist_serial` (`test_checker.py:184`) and must not be touched.
- The actual failing test, `TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call` (`test_checker.py:139-159`), spawns a subprocess whose *injected source string* reads a real clock and asserts `elapsed < 1.0` around a module import — a redundant proxy for the invariant the very next assertion (`m._memoized_result is m._UNSET`) already checks deterministically.
- Re-ran both the target test and the full scanner suite standalone today: both pass cleanly (target: 0.61s; scanner: 2/2 passed). This reconfirms the "never fails standalone, only under `-n` contention" character already recorded in the task-206 baseline.
- Root cause of the scanner blind spot confirmed structurally: the offending `time.time()`/`elapsed < 1.0` pair lives entirely inside a Python source string assigned to a local variable (`code = (...)`) that is later passed, by name, inside a list literal (`[sys.executable, "-c", code]`) to `subprocess.run(...)`. The AST scanner's `_calls_clock`/`_has_bound_assertion` walk the *real* function body only, so they see one `ast.Constant` (the joined string) and nothing resembling a `time.time()` call node or a `>`/`<` comparison — exactly as the module's own docstring already predicts for this scan's declared limits.
- A repo-wide grep confirms `test_checker.py` is the **only** test file in `code/src/model_checker` or `code/tests` combining `subprocess.run` with any of `time.time`/`perf_counter`/`monotonic` — so Item 2's fix has no other live instance to worry about breaking or needing allowlisting; only a synthetic self-test fixture can prove the extended detection actually fires (per the dispatch's own suggestion to follow the module's existing self-test style).
- Recommend: (1) delete the wall-clock assertion and its now-unused `import time`/`t = time.time()` lines from the injected subprocess source outright (dispatch's stated preference; costs no coverage); (2) extend the AST scanner to resolve simple same-function string-variable arguments passed to subprocess/exec-style calls and recursively re-run the existing clock/bound-assert detectors against the parsed embedded source, with a synthetic self-test proving the new path fires and a marked variant proving it's suppressed correctly.

## Context & Scope

Task 213 targets exactly two items inside a single test module plus a single CI-guard module:

1. `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` — remove (or justify-and-mark) a wall-clock assertion that flakes under `-n 4` contention.
2. `code/tests/ci/test_timing_marker_coverage.py` — extend the AST guard so this shape cannot silently recur, plus a self-test proving the extension works.

No other files are in scope. The task's `file_scope` is not declared in state.json (`file_scope: null` per the dispatch's Territory block for this task), so scope is bounded by the description text alone, which names exactly these two files.

## Findings

### Item 1 — the failing assertion

`test_checker.py:139-159`:

```python
def test_import_performs_no_subprocess_call(self):
    """Importing the module must not probe -- resolution is lazy. Run in a subprocess
    (never `importlib.reload`, which would redefine `Unavailable`/`CheckerHandle` as new
    class objects, breaking every subsequent `isinstance` check in this same test
    session)."""
    import subprocess
    import sys

    code = (
        "import time\n"
        "t = time.time()\n"
        "import model_checker.theory_lib.bimodal.semantic.checker as m\n"
        "elapsed = time.time() - t\n"
        "assert m._memoized_result is m._UNSET, 'import must not resolve eagerly'\n"
        "assert elapsed < 1.0, elapsed\n"
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=15
    )
    assert result.returncode == 0, result.stdout + result.stderr
```

- The test's real, load-bearing invariant is `m._memoized_result is m._UNSET` (import must not eagerly resolve the checker). That assertion is deterministic and independent of host load.
- `elapsed < 1.0` is a second, redundant proxy for "import didn't do something expensive" — but with ~0.6s standalone cost against a 1.0s bound, it has only ~0.4s of headroom, which a contended 4-worker pool routinely eats. `subprocess.run(..., timeout=15)` already guards the genuine-hang case independently of this assertion.
- Confirmed via live standalone run today: passes in 0.61s (0.23s test call) — consistent with the task-206 baseline's 0.58s/0.60s standalone timings, reinforcing that this is purely a contention artifact, not a logic defect.
- **Recommendation**: delete `import time`, `t = time.time()`, `elapsed = ...`, and `assert elapsed < 1.0, elapsed` from the injected `code` string. The remaining string becomes:
  ```python
  code = (
      "import model_checker.theory_lib.bimodal.semantic.checker as m\n"
      "assert m._memoized_result is m._UNSET, 'import must not resolve eagerly'\n"
  )
  ```
  This is the dispatch's explicitly stated preference ("Prefer deleting the wall-clock assertion outright over marking or widening it") and costs no coverage — the test's docstring/name (`test_import_performs_no_subprocess_call`) already describes the no-eager-probe invariant, not a timing budget, so no rename is needed.
- Nothing else in the test file references `elapsed`, `t`, or the injected `time` import — the removal is fully self-contained within this one function.
- Confirmed `test_probe_timeout_yields_unavailable_not_a_hang` (`test_checker.py:184-197`) already carries `@pytest.mark.xdist_serial` and its own `elapsed < 1.0` assertion is against a *mocked* clock path (`timing_out_invoke` never sleeps) — this test is correctly out of scope and must not be touched, exactly as the dispatch's scope correction states.

### Item 2 — the scanner blind spot

`code/tests/ci/test_timing_marker_coverage.py` detects a violation when, within a test function's own body (or a same-module non-test helper it calls — the "one-hop" case), both hold:
1. `_calls_clock`: an `ast.Call` node shaped `time.time()` / `time.perf_counter()` / `time.monotonic()` appears.
2. `_has_bound_assertion`: an `ast.Assert` with a `<`/`>`/`<=`/`>=` comparison (or a `self.assertLess`/etc. call) appears.

In `test_import_performs_no_subprocess_call`, both the clock read and the bound assertion exist only as *text inside a Python string literal* (the `code` variable), which the outer AST sees as a single opaque `ast.Constant`. Two facts matter for how to fix this correctly:

- **The string literal is not passed inline to `subprocess.run`** — it is first bound to a local variable (`code = (...)`, where Python's parser already folds the adjacent string literals into one `ast.Constant` at parse time, so no string-concatenation handling is needed), and that variable name is later referenced inside a list literal argument: `subprocess.run([sys.executable, "-c", code], ...)`. Any AST extension must resolve this same-function local-variable binding, not just scan literal arguments directly inside the call.
- Repo-wide check (`grep -rl subprocess.run` combined with `time.time|perf_counter|monotonic` over every `test_*.py` under `code/src/model_checker` and `code/tests`) found **exactly one file**: `test_checker.py`. There is no other live instance of this shape in the tree today, and after Item 1's fix there will be **zero** real instances left containing a clock read (the fixed injected string contains no `time.time()` call at all). This means Item 2's correctness cannot be demonstrated against a real fixed-up file; the dispatch itself anticipates this by asking for a **self-test in the module's existing style** proving the extended scan flags the shape, which must therefore use a synthetic fixture rather than a real repo file.

**Recommended detection extension** (for the planning/implementation phase to refine):

1. Define a set of subprocess/exec-style call targets to recognize: attribute calls `subprocess.run`, `subprocess.call`, `subprocess.check_call`, `subprocess.check_output`, `subprocess.Popen` (i.e. `ast.Call` whose `func` is `ast.Attribute` with `value` a `Name` equal to `"subprocess"` and `attr` in that set), plus bare `exec(...)` / `eval(...)` (`ast.Call` whose `func` is `ast.Name` in `{"exec", "eval"}`). `os.system(...)` is a reasonable additional inclusion given the same string-execution shape, though not present in the current failing case.
2. Within the same scope already being scanned (test function body, or its one-hop helper — reuse the existing traversal, don't add a second one), build a small map of `local_name -> str_value` from simple `ast.Assign` statements whose target is a single `Name` and whose value is an `ast.Constant` with a `str` value (this already covers adjacent-string-literal folding; string-concatenation via `+` could be added later but is not needed for the current case).
3. For every matched subprocess/exec-style `ast.Call`, collect candidate string sources from its `args`/`keywords`: direct `ast.Constant` str nodes, and `ast.Name` nodes (including ones nested inside `ast.List`/`ast.Tuple` elements, to catch the `[sys.executable, "-c", code]` shape) resolved through the map from step 2.
4. For each resolved string, `ast.parse` it in a `try/except SyntaxError: continue` guard, and run the **existing** `_calls_clock`/`_has_bound_assertion` helpers against the resulting sub-tree, OR-ing their results into the same detection used for the outer function body (i.e., a violation is flagged if the clock-read and bound-assert conditions are jointly satisfied across the *union* of the function's own AST nodes and any resolved embedded-string AST nodes — matching how the existing one-hop helper case already unions the test function with a called helper).
5. Marker requirement (decorators on the function, its enclosing class, or module `pytestmark`) is unchanged.
6. Add a **synthetic self-test** (module's existing style is to assert against real scanned files, e.g. `test_scan_finds_the_known_marked_inventory`; since no real unmarked instance of this shape will remain in the tree after Item 1, this self-test should write a small fixture source string to a `tmp_path` file reproducing the *pre-fix* shape — a local `code = (...)` string containing `time.time()`/`elapsed < 1.0`, referenced by name inside a `subprocess.run([...])` call, with no marker — and assert `_find_unmarked_timing_tests(that_path)` flags it; a second fixture with `@pytest.mark.xdist_serial` added should assert it is *not* flagged, confirming the marker-suppression path still works through the new detection route).
7. After implementing, re-run `test_all_wall_clock_timing_assertions_are_marked` and `test_scan_finds_the_known_marked_inventory` across the real tree to confirm the broadened detection introduces no new (real) violations and the existing known-inventory list is unaffected (expected: unaffected, since the one real instance is fixed by Item 1 and no other file matches the new call-target set today per the grep above).

**Escape hatch** (only if the AST extension is judged too broad/fragile during implementation): document the boundary directly in the module's docstring, following the existing precedent for the deliberately-excluded `time.sleep()` case — i.e., add a paragraph naming this exact shape (clock-read-plus-bound-assert inside a string literal passed to a subprocess/exec-style call, potentially via an intermediate variable binding) as a known, reasoned scope carve-out, rather than leaving the gap undocumented. The dispatch treats implementing the detection as the default expectation and documentation-only as the fallback, not the other way around; nothing found during this research suggests the AST extension is infeasible — the required variable-resolution step is a bounded, same-scope, single-hop lookup consistent with the file's existing one-hop helper-tracing precedent.

## Decisions

- Treat `test_probe_timeout_yields_unavailable_not_a_hang` as strictly out of scope (confirmed already marked `xdist_serial`; the dispatch's scope correction is verified accurate).
- Prefer outright deletion of the wall-clock assertion (and its now-dead supporting lines) in `test_import_performs_no_subprocess_call` over marking/widening it, per the dispatch's explicit preference and this research's confirmation that the neighboring `_UNSET` assertion already covers the test's real invariant.
- Recommend implementing the AST scanner extension (not falling back to documentation-only), since the required variable-resolution step is small, bounded, and consistent with the module's existing one-hop-helper detection philosophy; documentation-only should be used only if implementation discovers unforeseen fragility.

## Recommendations

1. **Implementation, Item 1**: In `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py`, edit `test_import_performs_no_subprocess_call` to drop `import time`, `t = time.time()`, `elapsed = time.time() - t`, and `assert elapsed < 1.0, elapsed` from the injected `code` string, leaving only the import and the `_UNSET` assertion. No other change to the test is needed.
2. **Implementation, Item 2**: In `code/tests/ci/test_timing_marker_coverage.py`, extend detection per the algorithm above (subprocess/exec-style call-site recognition + same-scope simple string-variable resolution + recursive re-application of the existing `_calls_clock`/`_has_bound_assertion` helpers against parsed embedded source), and add a synthetic self-test (fixture written to `tmp_path`, exercised directly through `_find_unmarked_timing_tests`) proving both the positive (unmarked, flagged) and negative (marked, not flagged) cases.
3. **Verification order**: Fix Item 1 first and confirm the target test still passes standalone (trivial — the removed assertion cannot fail by construction). Then run the full parallel gate once: `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread` and confirm a clean pass with no `test_import_performs_no_subprocess_call` failure. Per the dispatch, a single clean run suffices — do not attempt repeated draws to "prove a negative."
4. **Verification, Item 2**: Run `code/tests/ci/test_timing_marker_coverage.py` (both existing self-tests plus the new one) and confirm all pass, including the new synthetic-fixture proof.
5. No changes are needed to `code/pyproject.toml`'s marker registration — `xdist_serial` and `performance` already exist and are unaffected by either item.

## Risks & Mitigations

- **Risk**: broadening the AST scanner to resolve variable-bound strings could introduce false positives elsewhere in the tree (e.g., a subprocess call whose string argument happens to contain unrelated comparison operators that are not actually `time.time()`-adjacent). **Mitigation**: the detection still requires *both* a clock-read call node and a bound-comparison assert node inside the same resolved string/scope — the existing two-condition AND logic is preserved, only the source of AST nodes is widened; the repo-wide grep in this report found no other file matching even the coarser `subprocess.run` + clock-function-name text pattern, so no other file is at risk of being newly (and incorrectly) flagged today.
- **Risk**: resolving string-literal variables via a naive same-function scan could miss cases where the string is built across multiple statements (e.g., `code = "a\n"` then `code += "b\n"`) or passed through an intermediate function. **Mitigation**: this matches the same known, accepted limitation already documented for the existing one-hop helper tracing (structural AST scan, not full dataflow) — out of scope to solve generally; if it is judged necessary, document the boundary rather than attempting full dataflow analysis, per the same escape-hatch precedent used for `time.sleep()`.
- **Risk**: none identified for Item 1 — deleting an assertion cannot introduce a new failure mode, and the invariant it was meant to protect (no eager resolution) remains independently and deterministically checked.

## Appendix

- References:
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py:139-159` (target test)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py:184-197` (`test_probe_timeout_yields_unavailable_not_a_hang`, confirmed out of scope, already `xdist_serial`)
  - `code/tests/ci/test_timing_marker_coverage.py` (scanner module, full contents reviewed)
  - `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md:44-54,107-113,171-179` (three independent reproductions plus standalone-pass confirmations)
  - `code/pyproject.toml:88-97` (marker registration block)
  - Live verification today: `PYTHONPATH=code/src pytest .../test_checker.py::TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call -v` → passed in 0.61s; `PYTHONPATH=code/src pytest code/tests/ci/test_timing_marker_coverage.py -v` → 2 passed in 1.35s.
