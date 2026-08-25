# Research Report: Eliminate Wall-Clock-Sensitive Test Flakes and Undiagnosable Hangs

## Scope

Root-cause investigation for three defect families surfacing identically in both
`.github/workflows/tests.yml` (Python 3.10-3.12 matrix, PyPI z3-solver) and the `flake-check` job
(nixpkgs-native Z3 toolchain, `flake.nix`'s `checks.default`), both of which run the same
invocation shape: `pytest ... -m "not packaging and not performance and not unstable" -n 6`.

## 1. Solver-Budget Flakes: UNKNOWN Conflated With UNSAT

### Where the conflation happens

`code/src/model_checker/models/structure.py`'s `solve()` (lines 235-292) already does the right
thing internally: it distinguishes `SolverResult.is_sat`, `is_unsat`, and the UNKNOWN fallthrough
(lines 266-285), and treats *any* UNKNOWN — regardless of `reason_unknown()` string — as
`is_timeout=True`. `_process_solver_results()` (lines 133-159) stores this correctly:
`self.timeout = timeout` (line 148) is a real, populated attribute on every `ModelDefaults`
instance. `re_solve()` (lines 294-330, used by the iterate package) has the identical, correctly
commented UNKNOWN-handling.

The break is one layer up, in `code/src/model_checker/builder/example.py`'s `BuildExample`:

- `get_result()` (lines 199-220) returns `{"model_found": self.model_structure.z3_model_status,
  "runtime": ..., "model_structure": ...}` — no `timeout` key anywhere.
- `_get_model_structure_data()` (lines 222-242) repeats the same omission.
- `check_result()` (lines 336-344) compares `z3_model_status` (== the boolean `is_satisfiable`
  from the solver tuple) against the settings `"model"` expectation — again with no timeout
  branch.

Since `z3_model_status` is `False` both when Z3 proved UNSAT *and* when Z3 returned UNKNOWN, every
consumer of `get_result()["model_found"]` sees an indistinguishable `False` for "no countermodel
exists" and "we ran out of time." `ModelStructure.timeout` (the correctly-populated flag) is
simply never read by `builder/example.py`.

### Observed instance

`code/src/model_checker/builder/tests/unit/test_example.py::test_iteration_via_iterate_api`
(lines 365-439) builds a bimodal example with explicit `"max_time": 30` (line 384, chosen
specifically because the bimodal default is 1s and the real solve is slower — see the in-file
comment at lines 380-383), then asserts `self.assertTrue(result["model_found"], ...)` at line 414.
A 30.62s call against `max_time=30` produces exactly the UNKNOWN-as-False case above: the test
fails as "no model found" when the true cause is "the solver ran 0.62s past budget," which
`result["model_found"]` cannot express.

### Reference implementation already in this repo

`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s `run_differential_scan()`
(around lines 1690-1806) is the pattern to imitate, not invent from scratch:
- It tracks `agreements`, `disagreements`, and `timeout_count` as three **mutually exclusive**
  counters (lines 1692-1694, 1725-1737): `if record["mc_result"] == "TIMEOUT" or
  record["reference_result"] == "TIMEOUT": timeout_count += 1` is checked *before* the
  agree/disagree branch, so a timeout can never be miscounted as either.
- The returned report dict carries `timeout_count` as an independent field (line 1783), and a
  `conclusive = total - timeout_count` derived value (line 1794) — timeout is subtracted out of
  the denominator, never folded into the pass/fail signal.
- Tests on this report shape explicitly assert the three-way partition
  (`test_cross_oracle_differential.py` lines 1953-2013): `agreements + disagreements +
  timeout_count == total`, and a dedicated regression test (lines 1996-2013, described as
  "exact inversion the either-side ... " in the surrounding comment) locks in that a
  reference-side timeout is counted as `timeout_count`, not silently treated as a decided
  disagreement.

Applying this shape to `BuildExample` means: `get_result()` / `_get_model_structure_data()` should
surface `model_structure.timeout` as its own key (e.g. `"timeout": bool`) alongside
`"model_found"`, and any test/consumer that currently asserts on `model_found` alone for a
solver-bound example should branch on `timeout` first (skip/xfail/report-inconclusive) before
treating a `False` `model_found` as a semantic "no countermodel" result. `check_result()` likely
needs an analogous three-way return (match / mismatch / inconclusive) rather than the current
boolean.

### Deterministic Z3 rlimit budgets

No `rlimit` mechanism exists anywhere in the production solver path today. Every "rlimit" hit in
the codebase (`grep -rn rlimit code/ oracle/`) is a code comment recording an *observed*
measurement from ad hoc profiling (e.g. `theory_lib/bimodal/examples.py:333,441`,
`theory_lib/bimodal/semantic/core.py:1302,1562,1591-1593`) — never a call that sets or reads
`rlimit` programmatically. `Z3SolverAdapter` (`code/src/model_checker/solver/z3_adapter.py`) has
`set_timeout()` (line 144, wall-clock only, via `self._solver.set("timeout", ms)`) but no
`set_rlimit()`/`set_param("rlimit", ...)` counterpart, and `SolverProtocol`/`TrackedSolverProtocol`
(`code/src/model_checker/solver/protocols.py`) declare no rlimit-related method. `rlimit` is a
genuinely new capability to add, not a dormant one to wire up.

Z3's `rlimit` (set via `Solver().set("rlimit", N)`, resource-unit budget, deterministic and
machine-load-independent, unlike `timeout` which is wall-clock) is the natural mechanism.
`ExampleSettings` (`code/src/model_checker/settings/types.py` lines 60-67) is the existing
TypedDict that `max_time` already flows through end-to-end (settings dict -> `ModelDefaults.solve()`
-> `solver.set_timeout()`); adding an optional `rlimit` field there and a parallel
`solver.set_rlimit()`/`set("rlimit", ...)` call in `solve()`/`re_solve()` mirrors that existing
plumbing rather than inventing a second configuration path. This is a design option to hand to
planning, not a settled decision — an alternative is a test-local-only mechanism (a fixture/helper
that calls the Z3 solver object directly in the specific solver-heavy tests named by the task)
that never touches the shared settings schema. The report flags the trade-off rather than picking
for the planner: schema-level integration is more invasive but reusable across every theory;
test-local is narrower blast radius but doesn't help application code, only test determinism.

### Adjacent, smaller-blast-radius surface (same defect shape, not explicitly in scope)

`code/src/model_checker/utils/testing.py`'s `TestResultData`/`run_enhanced_test()` (lines 58-140)
independently computes `model_found = model_structure_obj.z3_model is not None` (line 140) with no
timeout field either — the same conflation, in a second, older test-helper surface used by some
theory-level example test suites. Only one non-test caller of `BuildExample.get_result()` exists in
production code (`print_model()` at line 260, which doesn't key off `model_found` directly), so the
blast radius of adding a `timeout` key to the dict is confined to test consumers.

## 2. Timing-Assertion Design Flakes

### The exact failure

`code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py`,
`TestPerformanceAndScalabilityScenarios::test_repeated_project_operations_maintain_consistent_performance`
(lines 353-389):

```python
for iteration in range(5):
    start_time = time.time()
    project_generator = BuildProject('bimodal')
    project_dir = project_generator.generate(f'{project_name}_{iteration}')
    operation_time = time.time() - start_time
    operation_times.append(operation_time)
    ...
max_time = max(operation_times)
min_time = min(operation_times)
self.assertLess(max_time, 10.0, "No single operation should take more than 10 seconds")
if min_time > 0:
    time_variation_ratio = max_time / min_time
    self.assertLess(time_variation_ratio, 5.0, f"... ratio: {time_variation_ratio:.2f}")
```

`BuildProject.generate()` is pure filesystem work (project scaffolding) — no Z3, no solver
involvement. The bug is structural, not load-related: the loop keeps every iteration including the
first (cold-cache, cold-import, cold-filesystem-metadata) one, then divides `max/min` with **no
floor on `min_time`** other than a `> 0` guard. As the codebase gets faster, `min_time` (typically a
later, warm iteration) shrinks while `max_time` (typically the first, cold iteration) stays roughly
fixed — the ratio *grows* as the implementation improves. Observed: ratio 17.4 against the 5.0
bound, while the companion absolute bound (`max_time < 10.0`) passed comfortably — proof the
operation itself was fine and only the ratio's shape was defective.

`test_multiple_project_generation_completes_within_reasonable_time` (lines 312-351, same class) has
a safer absolute-only bound (`total_time < 30.0` for 10 projects) with no ratio assertion, and is
not implicated in the observed failure, but sits unmarked in the same class.

### Fix shape

Two changes, orthogonal:
1. **Discard the cold first iteration** before computing any statistic — measure iterations 1..4
   (or re-run with a discarded warm-up pass), not 0..4.
2. **Replace the unbounded ratio with an absolute or median-plus-slack budget.** E.g. assert every
   iteration's time is under a fixed absolute ceiling, and/or assert
   `max(warm_times) < median(warm_times) + fixed_slack_seconds` rather than a pure ratio, which is
   the failure mode TESTING_GUIDE.md 8.5's own worked example currently models this exact
   anti-pattern on (see below) and needs correcting alongside the test.

### Documentation currently modeling the wrong pattern

`code/docs/core/TESTING_GUIDE.md` section "8.5 Performance Testing" (lines 570-585) shows:

```python
def test_iteration_completes_within_time_limit():
    start = time.time()
    result = iterate_models(formula, max_size=10)
    duration = time.time() - start
    assert duration < 5.0, f"Iteration took {duration}s, should complete in <5s"
```

This single-shot absolute-bound example is not itself wrong, but the guide has no worked example
of the *repeated-operation* case (cold-start discard + ratio-vs-absolute choice), which is exactly
where the observed flake originated. Section "8.6 Solver Timing Budgets and Machine Variance"
(lines 587-633) already documents the UNKNOWN/timeout conflation from Sub-family 1 in detail (the
"Why this matters more than ordinary slowness" paragraph is a close match to this task's own
framing) and explicitly says (line 623) "Wall-clock assertions are load-sensitive... Give such
assertions generous tolerances, or move them behind an opt-in marker" — but stops short of a
concrete cold-start/ratio-vs-absolute recipe. This is the natural section to extend with a new
subsection (e.g. "8.5a Repeated-Operation Timing: Discard Cold Starts, Avoid Unbounded Ratios")
once the fix lands, per the task's "Add ... TESTING_GUIDE documentation" requirement.

## 3. Undiagnosable Hangs: No Per-Test Timeout Guard

### Confirmed gap

- `.github/workflows/tests.yml` line ~83 (the `pytest tests/ src/model_checker -m "not packaging
  and not performance and not unstable" -n 6 -q` invocation) passes no `--timeout` flag.
- `flake.nix`'s `checks.default` derivation's `checkPhase` runs the textually-identical marker
  expression (`pytest src/model_checker tests -m "not packaging and not performance and not
  unstable" -n 6 -q`) — also no `--timeout`.
- `code/pyproject.toml`'s `[tool.pytest.ini_options]` `addopts = "--durations=0 -v
  --import-mode=importlib"` — no `--timeout` default either, so nothing upstream compensates.
- `pytest-timeout>=2.0.0` **is** already a declared dependency
  (`code/pyproject.toml` line 51, comment: "`@pytest.mark.timeout(...)` hang guards in
  `tests/integration/`") and is installed in both toolchains: `pip install ... pytest-timeout ...`
  in `tests.yml`'s "Install test dependencies" step, and `pytest-timeout` in `flake.nix`'s
  `devPython`/`checks.default` package list (with an explanatory comment at
  `flake.nix` lines 82-86 about `compare_bimodal_baseline.sh` needing it). The plugin is present
  but never invoked with a suite-wide default in either CI path.
- By contrast, `.github/workflows/differential-tests.yml` already passes explicit `--timeout`
  values on both of its invocations (`--timeout=1500` at line ~64, `--timeout=300` at line ~78),
  but neither specifies `--timeout-method`, so both fall back to pytest-timeout's default method
  (`signal` on Unix) — which cannot reliably interrupt/diagnose a hang blocked inside a C
  extension call (e.g. a stuck Z3 call), unlike `thread` mode, which runs a watcher thread that
  dumps every thread's stack via `faulthandler` regardless of what the main thread is blocked in.
  This is exactly why the task specifies `--timeout-method=thread` for the two files in scope
  rather than the plain `--timeout` differential-tests.yml already has.
- Prior precedent in this repo for the `--timeout=N --timeout-method=thread` invocation shape:
  `specs/archive/129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md`
  (lines 134, 143, 359) used `--timeout=180 --timeout-method=thread` (and confirmed
  `pytest-timeout` 2.4.0 installed) for exactly this diagnostic purpose during a prior triage.

### Observed incident this closes

Per the task description: CI run `32897405646`'s Python 3.12 job reached 94% progress, produced
zero output for 17 minutes, then was killed by the job-level `timeout-minutes: 20` in `tests.yml`
— with only "orphaned pytest and six python workers" visible in the cleanup log, no indication of
which test or worker actually hung. A job-level timeout is a backstop that ends the job; it carries
no diagnostic information about *what* hung. A per-test `--timeout` with `--timeout-method=thread`
converts this into a named test plus a full stack dump at the moment of the hang.

### Fix shape

Add `--timeout=<budget> --timeout-method=thread` to both:
- `tests.yml`'s pytest invocation (the `general-tests` job), and
- `flake.nix`'s `checks.default` `checkPhase` pytest invocation,

using the same budget in both (per the cross-cutting sync requirement below). The budget needs to
be chosen comfortably above the slowest individual test's observed runtime under `-n 6` load — this
report does not measure that figure; it is a planning-stage input (candidate reference points: the
128s-vs-thin-headroom methodology `differential-tests.yml`'s own comment documents for its
`--timeout=1500` choice, and the `--timeout=180`/`300` figures used in the prior task-129 triage
for a comparable general suite scope).

## 4. Cross-Cutting: The Marker Gap and xdist Oversubscription

### Marker gap, precisely counted

`code/pyproject.toml` registers `performance` as a marker (line 91:
`"performance: Tests that verify performance characteristics"`), and both CI invocations already
deselect it (`-m "not packaging and not performance and not unstable"`). But only **one** test in
`src/model_checker` actually carries `@pytest.mark.performance`:
`code/src/model_checker/builder/tests/test_refactoring_target_behavior.py::test_performance_improvement`
(marker at line 311, test at line 312, its own `assertLess(init_time, 0.01, ...)` at line 328).

Grepping for real wall-clock **bound assertions** (`self.assertLess`/`self.assertGreater` against a
time/elapsed/duration variable, excluding the marked test above and excluding mocked/no-real-clock
cases like `models/tests/unit/test_structure.py`) finds exactly **five more unmarked files** — six
files total asserting wall-clock bounds, matching the task's "roughly six" figure:

| File | Assertion(s) | Notes |
|---|---|---|
| `builder/tests/e2e/test_project_edge_cases.py` | `total_time < 30.0` (line 340); `max_time < 10.0` (382); `time_variation_ratio < 5.0` (388) | Whole `TestPerformanceAndScalabilityScenarios` class (lines 297-389) unmarked; this is the class that produced the observed flake |
| `builder/tests/integration/test_performance.py` | `loading_time < 0.1` (259); `serialization_time < 0.001` (281) | Comments describe these as "hang guard[s]" with ~20x headroom, not tight performance budgets, but still unmarked and still real wall-clock measurements |
| `builder/tests/unit/test_project_version.py` | `detection_time < 1.0` (127) | Unmarked |
| `builder/tests/unit/test_serialize.py` | `serialize_time < 2.0` (433) | Unmarked |
| `builder/tests/unit/test_progress_bar_ordering.py` | `0.15 < frozen_elapsed < 0.6` (423-424), built on a real `time.sleep(0.3)` (416) | Unmarked; genuinely contention-sensitive since it depends on the scheduler actually granting the sleeping thread ~0.3s within a tight window |
| `builder/tests/test_refactoring_target_behavior.py` | `init_time < 0.01` (328) | The one marked file — included here only as the complete-set anchor |

Because `-m "not performance"` only removes the one marked test, the entire
`TestPerformanceAndScalabilityScenarios` class — including the exact test that produced the
observed 17.4-ratio failure — still lands in the same `-n 6` xdist worker pool as the solver-heavy
suite on every CI run. Marking the remaining five files' timing tests `@pytest.mark.performance` is
what would have kept this class off a contended runner in the first place.

### xdist isolation precedent already in this repo

`oracle/conftest.py` defines a custom `xdist_serial` marker (lines 51-63) specifically for tests
"whose Z3 solve budget has under ~2x headroom, which CPU contention under pytest-xdist can push
past budget." `oracle/run-oracle-suite.sh` (lines ~167-181) implements the consuming two-pass
pattern: pass 1 runs `pytest ... -n 6 -m "not xdist_serial and not slow"` (parallel), pass 2 runs
`pytest ... -m "xdist_serial and not slow"` with **no `-n` flag at all** (serial, zero sibling
workers). This is the established in-repo precedent for "isolate timing-sensitive tests from `-n 6`
oversubscription" — a marker plus a second, unparallelized invocation pass — rather than a novel
mechanism. `xdist_serial` itself is currently declared only in `oracle/conftest.py`, not in
`code/pyproject.toml`; extending it (or an analogously-named marker) to `code/pyproject.toml` and
wiring a second serial pass into `tests.yml`/`flake.nix` is one concrete design option for the
planner, following this exact precedent.

GitHub-hosted `ubuntu-latest` runners are 4-vCPU — `-n 6` is already deliberately oversubscribed
relative to that (tests.yml's own comment block above the pytest invocation explains `-n 6` was
chosen to match a documented bimodal CPU-contention flake under `-n auto`, and states this value is
shared with `flake.nix` "for cross-toolchain coverage of the same tests"). Timing-sensitive tests
sitting inside that same `-n 6` pool are structurally exposed to exactly this oversubscription,
independent of the ratio-assertion design bug in Sub-family 2 — fixing the assertion shape alone
does not remove the contention exposure for the tighter-budget files in the table above (especially
`test_performance.py`'s 0.1s/0.001s bounds and `test_progress_bar_ordering.py`'s sleep-based
window).

### Sync requirement between tests.yml and flake.nix

The two files already keep their `-m` marker expression and `-n 6` worker count in careful,
comment-documented sync (`flake.nix`'s own comments explicitly reference `tests.yml`'s reasoning
multiple times, e.g. around the `unstable` marker and the `-n 6` choice). Neither currently sets a
`--timeout`/`--timeout-method` flag, so today's "sync" is vacuous on that dimension by omission
rather than by an enforced invariant — nothing currently checks that the two invocations agree.
Any fix must add the identical `--timeout`/`--timeout-method` values (and identical marker
expression changes, e.g. an `and not <new-marker>` addition if the isolation mechanism above is
adopted) to both files in the same change, and per the task's explicit ask, back it with a
regression guard.

### Regression-guard precedent

`code/tests/packaging/test_parity.py` is the closest existing precedent for "make an
already-documented cross-file invariant executable": it turns a comment-only claim ("`MANIFEST.in`
and `pyproject.toml`'s package-data allowlist stay in sync") into an assertion over the two
artifacts' actual contents. No existing test currently parses `tests.yml`/`flake.nix` against each
other or against `pyproject.toml`'s registered markers — `find`/`grep` across `code/tests/` and
`code/scripts/` for anything referencing `tests.yml` or `flake.nix` turned up nothing. A new test
module (parsing both CI files' pytest invocation lines as text or via `yaml.safe_load` for
`tests.yml`, and a targeted string/regex extraction for `flake.nix`'s Nix string) modeled on
`test_parity.py`'s comparison style is the natural way to satisfy "tests.yml and flake.nix must
stay in sync on marker expression, worker count, and timeout flags" as an executable regression
guard, alongside a second guard asserting `BuildExample.get_result()` always carries a `timeout`
key (Sub-family 1) and/or that `TestPerformanceAndScalabilityScenarios`'s tests all carry
`@pytest.mark.performance` (Sub-family 2/cross-cutting) so the marker gap cannot silently reopen.

## 5. TESTING_GUIDE.md Structure for the Documentation Requirement

Relevant existing sections to extend rather than duplicate:
- **8.5 Performance Testing** (lines 570-585) — needs a repeated-operation/cold-start-discard
  worked example (Sub-family 2's fix).
- **8.6 Solver Timing Budgets and Machine Variance** (lines 587-633) — already documents the
  UNKNOWN/timeout conflation narrative closely; needs updating once `timeout` is surfaced in
  `BuildExample` results to describe the *fixed* state (currently describes the problem, written
  as if `max_time`-tuning is the only available remedy, with no mention of a `timeout` flag
  consumers can check) and to introduce the new `rlimit` option if adopted.
- **8.9 The `unstable` Marker** (lines 804-871) is the established template for how this repo
  documents a marker's meaning, entry criteria, and CI wiring — the right structural model for a
  new subsection documenting whatever isolation marker (new or reused `xdist_serial`) and the new
  `--timeout`/`--timeout-method` convention end up being adopted, including "where the deselection
  is wired" (mirroring lines 858-865's per-workflow inventory style).
- A new subsection is warranted for the `--timeout`/`--timeout-method=thread` convention itself
  (Sub-family 3), parallel in style to 8.6, referencing the task-129 precedent invocation and the
  observed run-32897405646 incident as the motivating case, matching how 8.6 opens with a concrete
  measured incident before stating the rule.

## Key File/Line Index

| Concern | File | Lines |
|---|---|---|
| UNKNOWN correctly classified as timeout (already fixed) | `code/src/model_checker/models/structure.py` | `solve()` 235-292, `re_solve()` 294-330, `_process_solver_results()` 133-159 |
| Timeout flag dropped before reaching results dict | `code/src/model_checker/builder/example.py` | `get_result()` 199-220, `_get_model_structure_data()` 222-242, `check_result()` 336-344 |
| Observed failing test | `code/src/model_checker/builder/tests/unit/test_example.py` | `test_iteration_via_iterate_api` 365-439, esp. assertion at 414 |
| Reference three-way timeout/agree/disagree pattern | `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` | `run_differential_scan` ~1690-1806; regression tests 1953-2013 |
| No rlimit mechanism anywhere | `code/src/model_checker/solver/z3_adapter.py` (`set_timeout` 144), `protocols.py` (no rlimit method), `settings/types.py` (`ExampleSettings` 60-67) | n/a |
| Unbounded ratio assertion (observed flake) | `code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py` | `TestPerformanceAndScalabilityScenarios` 297-389, ratio assertion 386-389 |
| TESTING_GUIDE anti-pattern example to correct/extend | `code/docs/core/TESTING_GUIDE.md` | 8.5 (570-585), 8.6 (587-633), 8.9 (804-871) |
| No `--timeout` in either CI job | `.github/workflows/tests.yml` (~line 83), `flake.nix` (`checkPhase`, ~line 164) | n/a |
| `pytest-timeout` already declared/installed | `code/pyproject.toml` line 51; `tests.yml` install step; `flake.nix` `devPython` 80-87 | n/a |
| `--timeout` present but no `--timeout-method=thread` precedent to diverge from | `.github/workflows/differential-tests.yml` | ~64, ~78 |
| Prior `--timeout=N --timeout-method=thread` usage in this repo | `specs/archive/129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md` | 134, 143, 359 |
| Only `@pytest.mark.performance` test in `src/model_checker` | `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py` | marker 311, test 312-328 |
| Five more unmarked wall-clock-asserting files | see table in section 4 | — |
| `performance` marker registration | `code/pyproject.toml` | line 91 |
| Existing xdist-isolation precedent (`xdist_serial`) | `oracle/conftest.py` (51-63), `oracle/run-oracle-suite.sh` (~167-181) | — |
| Regression-guard style precedent | `code/tests/packaging/test_parity.py` | whole file |

## Open Design Decisions for Planning

1. **rlimit plumbing depth**: full `ExampleSettings`/solver-abstraction integration (reusable,
   more invasive) vs. test-local-only helper (narrow, faster, doesn't help production callers).
2. **Timeout-key shape in `BuildExample` results**: a new boolean `"timeout"` key alongside
   `"model_found"` (minimal) vs. a three-way enum/result object (more explicit, larger call-site
   churn across `check_result()` and its consumers) — and whether `utils/testing.py`'s parallel
   `TestResultData` gets the same fix in the same pass or is deferred as a separate follow-up.
2a. Whichever shape is chosen, `check_result()`'s current boolean return needs a decision on how a
   timeout is reported to its callers (raise, return `None`/sentinel, or a third enum value) since
   it currently only ever returns `True`/`False`.
3. **Isolation mechanism for remaining timing-sensitive tests**: reuse/extend `xdist_serial` and
   adopt the oracle's two-pass parallel/serial pattern in `tests.yml`+`flake.nix`, vs. simply
   folding all six timing files under `@pytest.mark.performance` and accepting they run outside the
   gating `-n 6` pass entirely (simpler, but means they get zero default-suite coverage unless a
   separate non-gating invocation is added, mirroring how `unstable`-watch runs `unstable`-marked
   tests on their own schedule).
4. **`--timeout` budget value**: needs an empirical measurement of the slowest test under `-n 6` in
   both toolchains before a number can be chosen with confidence; this report does not attempt that
   measurement.
5. **Regression-guard scope**: one consolidated test module covering all three sync/marker
   invariants, or three separate targeted guards (workflow-file sync; `timeout`-key-present;
   `performance`-marker-coverage) — `test_parity.py`'s single-module-per-invariant-family style is
   the closer stylistic precedent for the latter.
