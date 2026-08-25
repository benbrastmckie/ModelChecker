# Research: Recurring `unstable-watch.yml` Failures

**Task**: 166 - Research and fix recurring unstable-watch.yml GitHub Actions failures
**Started**: 2026-08-25
**Completed**: 2026-08-25
**Effort**: Small (single-file fix, high confidence)
**Dependencies**: None
**Sources/Inputs**: `gh run view`/`gh run list` against benbrastmckie/ModelChecker, local
  reproduction via pytest, `.github/workflows/*.yml`, `oracle/bimodal_logic/tests/`,
  `code/docs/core/TESTING_GUIDE.md` section 8.9, prior task 159 artifacts
**Artifacts**: - this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Single root cause, 100% of runs.** Every `unstable-watch.yml` run since the workflow was
  created (13/13 runs checked, 2026-08-13 through 2026-08-25, including the reported run
  32813308100) fails identically: a pytest **collection** error (`ModuleNotFoundError: No module
  named 'bimodal_harness'`) while importing
  `oracle/bimodal_logic/tests/test_oracle_interface.py`, which the workflow's classification step
  cannot recognize and therefore (correctly, per its own conservative design) reports as a `NEW`
  failure, failing the job.
- **Not a ModelChecker code defect and not solver-timing flakiness.** No test actually ran or
  failed logically. It is a **pre-existing test-authoring defect**: `test_oracle_interface.py`
  has an unconditional, top-level `from bimodal_harness.oracle.protocol import OracleProvider`
  import. `bimodal_harness` is not a dependency of this repository at all -- it lives in a
  separate, developer-local checkout at `/home/benjamin/Projects/BimodalHarness/src`, is never
  installed by any CI workflow, and is not declared anywhere in `code/pyproject.toml`.
- **Why it never showed up before task 159.** No other CI workflow ever collects
  `test_oracle_interface.py`. `differential-tests.yml` deliberately targets only
  `test_cross_oracle_differential.py` by filename (its own comment: "Run differential tests
  (non-slow, no BimodalHarness)"). `unstable-watch.yml` (added in task 159) is the first, and
  currently only, CI job that runs pytest against the whole `oracle/bimodal_logic/tests/`
  directory, which sweeps in `test_oracle_interface.py` along with everything else.
- **Why it "worked" for the author locally.** `test_cross_oracle_differential.py` already has a
  *correct*, guarded pattern for this exact dependency (`_try_import_bimodal_harness()`, lines
  1236-1253): it checks `Path("/home/benjamin/Projects/BimodalHarness/src").exists()`, inserts it
  onto `sys.path` only if present, and catches `ImportError`, setting a module-level
  `_BH_AVAILABLE` flag that gates a `pytest.skip()`. Because that file sorts alphabetically before
  `test_oracle_interface.py` and both live in the same collected directory, on the *original
  author's own machine* (where `/home/benjamin/Projects/BimodalHarness/src` really exists) its
  module-level `sys.path.insert()` runs first and silently makes the later, unguarded
  `bimodal_harness` import in `test_oracle_interface.py` succeed too -- a side effect, not a
  real fix. On any other machine, including every GitHub Actions runner, that path never exists,
  the guarded file skips cleanly, and the unguarded file crashes at collection.
- **The oracle side of the workflow currently has zero `unstable`-marked tests anyway.** Per
  `TESTING_GUIDE.md` 8.9, the only test currently carrying `@pytest.mark.unstable` in the whole
  repository is `test_example_cases[BM_CM_1-example_case7]` in
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (the `code/` step, which
  passes every run). The `oracle/` step's own inline comment already documents this ("the oracle
  tree has no unstable-marked test right now -- expected and not a failure") and correctly
  special-cases pytest's exit code 5 ("no tests collected"). The workflow's design already
  anticipated the *marker-selection* case; it did not anticipate a *collection*-time crash from
  an unrelated file in the same directory, which happens before marker filtering can apply.
- **Recommendation**: fix the actual defect at its source -- add the same guarded-import pattern
  already established in `test_cross_oracle_differential.py` to `test_oracle_interface.py` (or
  factor the guard into a shared helper both files import). This is a one-file, low-risk change
  that makes the test module safely collectible in any environment, fixes `unstable-watch.yml`
  permanently, and closes a latent portability bug that happened to be invisible until task 159's
  workflow exercised full-directory collection for the first time. This is the best long-term fix
  because it removes the actual defect rather than routing around it.

## Context & Scope

The user is receiving nightly failure-notification emails from GitHub Actions for the
`unstable-watch.yml` workflow (added by task 159, commit `6d358c68`). The task asked for a
systematic diagnosis of the reported run (32813308100) and recent history, a determination of
whether this is one root cause or several, whether it reflects genuine ModelChecker defects vs.
infrastructure/workflow-authoring defects, local reproduction where feasible, and a recommended
long-term fix (this dispatch is research-only; no implementation was performed).

## Findings

### What the workflow does

`.github/workflows/unstable-watch.yml` is a `schedule`- and `workflow_dispatch`-only,
non-gating workflow (explicitly documented in its own header comment as never appearing in
another workflow's `needs:` and never part of branch protection). Each night at 05:00 UTC it:

1. Runs `PYTHONPATH=src pytest tests/ src/model_checker -m unstable -v --junitxml=/tmp/watch-code.xml`
   from `code/` (the "code/ tree" step).
2. Runs `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable -v --junitxml=/tmp/watch-oracle.xml`
   from the repo root (the "oracle/ tree" step).
3. Both steps use `continue-on-error: true` and treat pytest exit codes `0` and `5` (no tests
   collected) as success; anything else is a genuine problem.
4. A `classify` step parses both JUnit XML files, classifies any failing/erroring testcase as
   `TIMING` (matches a documented timing signature for a known `unstable` test, keyed by a
   node-id substring in `MAX_TIME_BY_NODEID_FRAGMENT`) or `NEW` (anything else, treated
   conservatively as a possible regression), queries `gh run list` for the workflow's own run
   history to compute a consecutive-green streak toward a 20-run promotion threshold (see
   `TESTING_GUIDE.md` 8.9), writes a step-summary table, and **exits non-zero only if any `NEW`
   classification was found** -- this is the only way the job (and thus the scheduled run) fails.

### Real failure data (13/13 runs, 100% reproduction of the same cause)

```
gh run list --workflow unstable-watch.yml --repo benbrastmckie/ModelChecker --limit 40 \
  --json databaseId,conclusion,createdAt,headBranch,event,displayTitle
```

returned 13 runs, `2026-08-13` through `2026-08-25` (the reported run), **all `conclusion:
failure`**. This is every run in the workflow's history to date -- it has never once gone green,
so the 20-consecutive-green promotion streak the workflow exists to accumulate has been stuck at
0 since creation.

Spot-checked three runs across the full date range with `gh run view <id> --log-failed`
(reported run 32813308100, oldest run 31673340774 from 2026-08-13, and a middle run 32219796996
from 2026-08-19): **all three show the identical failure signature**, byte-for-byte the same
error text:

```
collecting ... collected 513 items / 1 error / 513 deselected / 0 selected

==================================== ERRORS ====================================
_____ ERROR collecting oracle/bimodal_logic/tests/test_oracle_interface.py _____
ImportError while importing test module '.../oracle/bimodal_logic/tests/test_oracle_interface.py'.
Hint: make sure your test modules/packages have valid Python names.
Traceback:
  .../importlib/__init__.py:90: in import_module
    return _bootstrap._gcd_import(name[level:], package, level)
  oracle/bimodal_logic/tests/test_oracle_interface.py:37: in <module>
    from bimodal_harness.oracle.protocol import OracleProvider
E   ModuleNotFoundError: No module named 'bimodal_harness'
------------------ generated xml file: /tmp/watch-oracle.xml -------------------
=========================== short test summary info ============================
ERROR oracle/bimodal_logic/tests/test_oracle_interface.py
!!!!!!!!!!!!!!!!!!!! Interrupted: 1 error during collection !!!!!!!!!!!!!!!!!!!!
======================= 513 deselected, 1 error in 0.89s =======================
##[error]Process completed with exit code 2.
```

followed by the classify step's own diagnosis of exactly this situation:

```
##[error]oracle.bimodal_logic.tests.test_oracle_interface failed in a way that does not match
its documented timing signature (duration=0.00s, outcome=error). Investigate before assuming
this is the known instability -- see TESTING_GUIDE.md section 8.9.
##[error]Process completed with exit code 1.
```

The `code/` tree step (the one that actually exercises the real `unstable`-marked test,
`test_example_cases[BM_CM_1-example_case7]`) **passes on every run checked** (`1 passed, 2393
deselected in 16.39s` on the reported run). The failure is isolated entirely to the `oracle/`
tree step, and entirely to this one collection error.

**Conclusion: this is one root cause, not several.** There is no timing flakiness, no dependency
drift, no matrix/runner/action-version problem, and no genuine ModelChecker regression anywhere
in this history.

### Root cause: an unconditional, unguarded cross-repository import

`bimodal_harness` is not part of this project. It is not declared in `code/pyproject.toml`, not
installed by `unstable-watch.yml`'s `pip install z3-solver networkx pytest pytest-timeout
typing-extensions` step (nor by any other workflow's install step), and does not exist anywhere
in this repository (`grep -rl bimodal_harness` over tracked, non-archived source returns nothing
under `code/` or `oracle/` except the two files discussed below). It is a separate package that
lives in a sibling checkout on the repository owner's own machine:
`/home/benjamin/Projects/BimodalHarness/src/bimodal_harness`.

Two files in `oracle/bimodal_logic/tests/` reference it, with materially different robustness:

**`test_cross_oracle_differential.py` (lines 1236-1253) -- the correct, guarded pattern:**

```python
def _try_import_bimodal_harness() -> tuple[bool, Any]:
    bh_src = Path("/home/benjamin/Projects/BimodalHarness/src")
    if bh_src.exists() and str(bh_src) not in sys.path:
        sys.path.insert(0, str(bh_src))
    try:
        import bimodal_harness  # noqa: F401
        return True, bimodal_harness
    except ImportError:
        return False, None

_BH_AVAILABLE, _BH_MODULE = _try_import_bimodal_harness()
```

`TestBimodalHarnessIntegration.setup_method` checks `_BH_AVAILABLE` and calls
`pytest.skip("BimodalHarness not available at /home/benjamin/Projects/BimodalHarness")` when it
is absent. This file's own module docstring documents the design intent explicitly: "Self-
contained primitive formula enumerator (no BimodalHarness dependency for CI)" plus "Optional
BimodalHarness integration for temporal-only formula comparison." **This file was deliberately
written to degrade gracefully in CI.**

**`test_oracle_interface.py` (line 37) -- the unguarded, broken pattern:**

```python
from bimodal_harness.oracle.protocol import OracleProvider
from bimodal_harness.oracle.registry import OracleRegistry
```

This is a bare, top-level, module-scope import with no existence check, no `try/except`, and no
`pytest.skip()` fallback. Any pytest session that imports this module without `bimodal_harness`
already importable crashes at **collection** time -- before any test in the module can run, and
critically, **before marker-based deselection (`-m unstable`) has a chance to exclude anything**,
since pytest must successfully import a module before it can inspect its tests' markers.

### Why this was invisible until task 159's workflow

- `differential-tests.yml` never triggers the bug: its two pytest invocations name
  `test_cross_oracle_differential.py` (and specific classes within it) explicitly by path,
  never the containing directory, so `test_oracle_interface.py` is never collected by that
  workflow at all. Its own step name -- "Run differential tests (non-slow, no BimodalHarness)"
  -- shows the author was already actively avoiding exactly this dependency.
- `tests.yml` (the main gating suite) does not touch `oracle/` at all.
- `unstable-watch.yml` (task 159) is the **first and only** CI workflow to run pytest against the
  whole `oracle/bimodal_logic/tests/` directory, which is what first exposed the collection-time
  crash in CI.
- Locally, on the repository owner's own machine, running the same directory-wide command
  (`pytest oracle/bimodal_logic/tests/ -m unstable -v`) does **not** reproduce the crash, which
  is what makes this defect easy to miss without checking CI directly. This was confirmed
  experimentally in this research: targeting `test_oracle_interface.py` directly reproduces the
  exact CI error locally (`ModuleNotFoundError: No module named 'bimodal_harness'`), but
  collecting the whole `oracle/bimodal_logic/tests/` directory locally succeeds with **zero**
  errors, because `test_cross_oracle_differential.py` (alphabetically first, `c` < `o`) is
  collected first, its module-level `_try_import_bimodal_harness()` finds the real
  `/home/benjamin/Projects/BimodalHarness/src` directory on this machine, inserts it into
  `sys.path`, and that mutation persists in the same pytest process for the rest of collection --
  so `test_oracle_interface.py`'s later bare import inherits a working `sys.path` purely as an
  accidental side effect of a different file's own defensive code. On any machine (or CI runner)
  without that sibling checkout, there is no such side effect, and the crash is deterministic and
  unconditional.

### Local reproduction summary

| Command | Result |
|---|---|
| `pytest oracle/bimodal_logic/tests/test_oracle_interface.py --collect-only` (isolated) | **Reproduces the CI failure exactly**: `ModuleNotFoundError: No module named 'bimodal_harness'` |
| `pytest oracle/bimodal_logic/tests/ -m unstable --collect-only` (whole directory, as the workflow runs it) | Does not fail locally -- masked by `test_cross_oracle_differential.py`'s `sys.path` side effect (see above) |
| `pytest oracle/bimodal_logic/tests/ -m unstable` (whole directory, no `bimodal_harness` on path at all) | Would fail identically to CI |

This confirms the defect is real, present in the committed source (not an environment artifact of
the GitHub runner), and is masked locally only by an incidental ordering/side-effect quirk rather
than by any deliberate compatibility shim.

### Is this a ModelChecker code defect or a workflow/infrastructure defect?

**Workflow/test-authoring defect, not a code regression and not solver/timing flakiness.** No
`unstable`-marked test in `oracle/` exists today (confirmed: the only `@pytest.mark.unstable` /
`UNSTABLE_EXAMPLES` site in the whole repository is in
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`), so the "oracle tree"
step of `unstable-watch.yml` should be running zero tests and exiting 5 every single night --
exactly as its own inline comment anticipates. Instead, it never gets that far, because an
unrelated file in the same directory (`test_oracle_interface.py`) cannot even be imported outside
the original author's own machine. This is a portability bug in a committed test file, exposed by
(but not caused by) `unstable-watch.yml`'s directory-wide collection scope.

## Decisions

- Treat this as a single root cause requiring a single fix, not several independent failure
  modes. All 13/13 checked runs match the exact same signature; there is no evidence of any
  second failure mode in this workflow's history.
- Recommend fixing the actual defect (the unguarded import in `test_oracle_interface.py`) rather
  than only narrowing `unstable-watch.yml`'s collection scope, because narrowing the workflow
  would leave the underlying portability bug in place for the next contributor or CI job that
  touches this directory, and would only be a band-aid for the specific symptom reported here.

## Recommended Long-Term Solution

**Primary fix (recommended): guard the `bimodal_harness` import in `test_oracle_interface.py`
using the same pattern already established and working in `test_cross_oracle_differential.py`.**

Concretely: replace the two bare top-level imports at `test_oracle_interface.py:37-38` with a
call to the existing `_try_import_bimodal_harness()`-style helper (either import it directly from
`test_cross_oracle_differential.py`, or -- cleaner -- factor it into `oracle/conftest.py` or a new
small shared module under `oracle/bimodal_logic/tests/`, since two files now need it), gate the
tests in this module that actually require `OracleProvider`/`OracleRegistry` behind a
`pytest.skip()` when unavailable (mirroring `TestBimodalHarnessIntegration.setup_method`'s
existing pattern), and keep any BimodalHarness-independent tests in the file collectible and
runnable regardless.

Trade-offs considered:

- **Fix only `test_oracle_interface.py` (recommended)**: low risk, one well-precedented change,
  fixes the defect at its actual source, makes the file portable to any machine (a correctness
  improvement independent of this workflow), and requires no changes to
  `unstable-watch.yml` itself. Verifiable by running `pytest
  oracle/bimodal_logic/tests/test_oracle_interface.py --collect-only` with `bimodal_harness`
  absent from `sys.path` and confirming clean collection (skips instead of an import crash).
- **Narrow `unstable-watch.yml`'s oracle step to name specific files instead of the whole
  directory** (mirroring `differential-tests.yml`'s existing precedent): would also fix tonight's
  failure, and is a reasonable defensive addition, but treated alone it is a band-aid -- it
  papers over the fact that `test_oracle_interface.py` is not safely collectible in any
  environment without BimodalHarness, which will resurface the moment any other future workflow,
  local contributor, or IDE test-discovery run tries to collect that directory (or that file
  directly) without the sibling checkout present. Worth doing in addition to the primary fix as
  defense-in-depth, but not as a substitute for it.
- **Convert the `oracle/` step's failure into a non-fatal/soft-fail signal**: rejected. The
  workflow's non-gating contract is already correctly scoped at the *workflow* level (`schedule`
  + `workflow_dispatch` only, never in `needs:`, never a required check); making the *step itself*
  silently tolerant of collection errors would hide a real, fixable defect (this one) behind the
  same soft-fail mechanism meant for genuine solver-timing noise, defeating the classify step's
  whole purpose of telling `TIMING` and `NEW` apart.
- **Retire or pause the workflow**: rejected. The workflow's design (JUnit-based classification,
  run-history-derived streak, promotion surfacing) is sound and does exactly what
  `TESTING_GUIDE.md` 8.9 specifies; it has simply never had the chance to run cleanly because of
  this one collection-time bug. Once fixed, it should go green on its very next scheduled run
  (the `code/` step already passes every time, and the `oracle/` step will correctly hit its
  already-handled exit code 5 with zero `unstable`-marked tests present).
- **Install `bimodal_harness` in CI** (e.g., vendor it or add it as a CI-only dependency):
  rejected. `bimodal_harness` is explicitly an external/optional integration
  (`test_cross_oracle_differential.py`'s own docstring calls it "Optional BimodalHarness
  integration"), the oracle tree is excluded from the wheel entirely
  (`differential-tests.yml`'s own comment), and there is no indication this project intends
  `bimodal_harness` to be a real CI-installed dependency. Making it one would be a larger,
  riskier, and unmotivated change compared to simply guarding the import as its sibling file
  already does.

**Expected outcome after the primary fix**: the next scheduled `unstable-watch` run passes;
consecutive-green streak begins accumulating from 1 rather than remaining stuck at 0
indefinitely.

## Risks & Mitigations

- **Risk**: factoring the guard into a shared helper touches two files instead of one, slightly
  raising review surface. **Mitigation**: keep the shared helper minimal (an existence check plus
  try/except) and add a unit test asserting `test_oracle_interface.py` collects cleanly with
  `bimodal_harness` forced unavailable (e.g. via `monkeypatch` on `sys.modules` or by asserting
  the skip path), so this exact regression cannot recur silently.
- **Risk**: skipping BimodalHarness-dependent tests in `test_oracle_interface.py` under CI could
  reduce real test coverage there. **Mitigation**: this is already the accepted trade-off for
  `TestBimodalHarnessIntegration` in the sibling file; the module's other classes (protocol
  compliance, 52-example regression via the public API, enriched round-trips, etc., per its own
  docstring) do not appear to depend on BimodalHarness and should remain fully collectible and
  running -- confirm during implementation exactly which classes need the import and gate only
  those.

## Context Extension Recommendations

- **Topic**: cross-repository/optional test dependencies. **Gap**: `TESTING_GUIDE.md` documents
  the `unstable` marker (8.9) and timeout-skip/xdist-serial conventions (8.6, 8.8) in detail, but
  has no documented convention for "this test file depends on an external, developer-local
  package" beyond the one working example in `test_cross_oracle_differential.py`. **Recommendation**:
  once the primary fix lands, consider adding a short subsection (or a pointer comment at both
  call sites) naming the shared guard helper as the required pattern for any future
  BimodalHarness-touching test file, so this class of defect cannot recur a third time.

## Appendix

### Commands used

```
gh run view 32813308100 --repo benbrastmckie/ModelChecker --log-failed
gh run list --workflow unstable-watch.yml --repo benbrastmckie/ModelChecker --limit 40 \
  --json databaseId,conclusion,createdAt,headBranch,event,displayTitle
gh run view 31673340774 --repo benbrastmckie/ModelChecker --log-failed
gh run view 32219796996 --repo benbrastmckie/ModelChecker --log-failed
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_oracle_interface.py --collect-only -q
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable --collect-only -q
```

### Files examined

- `.github/workflows/unstable-watch.yml`
- `.github/workflows/differential-tests.yml`
- `.github/workflows/tests.yml` (grep only)
- `oracle/bimodal_logic/tests/test_oracle_interface.py`
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `oracle/conftest.py`
- `code/docs/core/TESTING_GUIDE.md` section 8.9
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (grep for
  `pytest.mark.unstable`)
- `specs/159_fix_bimodal_flake_and_unstable_category/` (prior task that created the workflow)
