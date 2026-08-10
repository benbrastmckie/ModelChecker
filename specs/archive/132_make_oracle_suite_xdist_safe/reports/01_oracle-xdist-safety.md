# Research: Making the Oracle Differential Suite Safe Under pytest-xdist

## Summary

The five xdist-only failures are not caused by any genuine shared state between worker
*processes* — there is none to find. Every affected test drives its own private
`Z3OracleProvider()` instance created in `setup_method`, and the one piece of "global" state the
suite touches (`z3.z3._main_ctx`, swapped by `isolated_z3_context()`) is a process-local Python
module attribute that cannot leak across `pytest-xdist` worker processes (`-n 6` forks/spawns
independent OS processes, each with its own `z3` module instance). The actual mechanism is
**CPU-contention-induced Z3 solve-time inflation tripping tight `max_time`/`timeout_ms` budgets**,
which the oracle pipeline (correctly, per its own design) reports as `None` (no countermodel)
rather than as an error — exactly the "wrong answer, not an error" hazard already documented in
`code/docs/core/TESTING_GUIDE.md` section 8.6 ("The variance tracks machine load, not test
order"). Every one of the five reported failures traces to a solve whose configured budget has
under ~2x headroom over its typical solo wall-clock time; running 6 workers simultaneously
competing for this machine's cores inflates individual solve times enough to occasionally cross
that budget. `xdist_group` is the wrong mechanism for this specific problem (it only guarantees
worker-affinity for tests that must run together, not freedom from *other* workers' CPU
contention); the effective fix is a new custom mark plus a two-invocation split — a parallel
`-n 6` pass excluding the marked tests, and a small serial pass for them. Separately, `differential`
and `slow` are already registered as pytest markers, but in `code/pyproject.toml`, a file that
sits outside the ini-file discovery path pytest uses when the CLI invocation targets `oracle/`
from the repository root — that discovery gap, not a missing declaration, is why the warnings
fire.

## 1. What is actually shared between the affected tests, and does xdist break it?

**Nothing is shared across processes.** Each affected test class instantiates its own provider:

- `oracle/bimodal_logic/tests/test_soundness_regression.py:667-668` —
  `TestStateIsolationRegression.setup_method`: `self.provider = Z3OracleProvider()`.
- `oracle/bimodal_logic/tests/test_soundness_regression.py:1014-1015` —
  `TestOracleMFormulaBoundarySafe.setup_method`: same pattern.
- `oracle/bimodal_logic/tests/test_oracle_interface.py:725-726` —
  `TestEnrichedRoundTrip.setup_method`: same pattern.
- `oracle/bimodal_logic/tests/test_boundary_regression.py:454` —
  `test_regression_all_active_examples` wraps its single call in
  `with isolated_z3_context(): ...` per-parametrized-case (no shared provider at all here; each
  case gets a fresh `run_test(...)` invocation).

The only cross-cutting piece of infrastructure is `isolated_z3_context()`
(`code/src/model_checker/utils/context.py:19-65`), which swaps the C-level pointer
`z3.z3._main_ctx` to a brand-new `z3.Context()` for the duration of each call and restores it
afterward, plus resetting a module-level `AtomSort` cache
(`code/src/model_checker/syntactic/atoms.py`, `reset_atom_sort`). Both of these are **plain
Python module attributes inside one interpreter process**. `pytest-xdist -n 6` runs six
independent worker *processes* (confirmed: `pytest-xdist` 3.8.0 in this devShell uses its
standard `execnet`-based subprocess workers, not threads) — a module attribute in worker A's `z3`
import is a completely different memory location than the same attribute in worker B's `z3`
import. There is no code path by which one worker's `find_countermodel()` call can perturb
another worker's `_main_ctx` or `AtomSort` cache. Grepped `oracle/bimodal_logic/provider.py` and
all four affected test files for `tempfile`, `os.environ`, `set_param`, shared cache files, or any
other candidate cross-process channel: **none found**. Confirmed no `oracle/conftest.py` and no
session-scoped fixtures of any kind exist under `oracle/` (only a benign empty
`tests/__init__.py`).

**The real shared resource is the machine's CPU**, and the coupling is at the OS scheduler, not
in this codebase. `TESTING_GUIDE.md` section 8.6 already documents this exact class of bug for
the same solver stack: "Z3 solve times for the *same* formula vary widely between runs on the
same machine... roughly a 20x spread with no change to the code under test. The variance tracks
machine load" — and "when a solve exceeds `max_time`, the result is reported as
`model_found == False` rather than as an error... A test whose `max_time` sits near its typical
solve time does not fail loudly — it silently inverts its semantic conclusion under load."
Running `-n 6` is itself "machine load" from the perspective of any one worker's Z3 solve.

**Per-test confirmation, each traced to a tight budget:**

| Test | Budget mechanism | Solo measured wall-clock (this session) | Headroom |
|------|------------------|------------------------------------------|----------|
| `test_regression_all_active_examples[BM_CM_1-...]` | `BM_CM_1_settings['max_time'] = 15` (`code/src/model_checker/theory_lib/bimodal/examples.py:319-326`, comment: "~8s with isolated Z3 context") | 12.39s (includes pytest/isolation overhead) | ~1.2x — the tightest of the five |
| `test_100_calls_mixed_temporal_depths` | `Z3OracleProvider.find_countermodel(formula)` called with **no `timeout_ms` override** -> default `timeout_ms: int = 5000` (`oracle/bimodal_logic/provider.py:169-173`), across 100 sequential calls | single-call baseline 1.57s (measured via the sibling depth-1 test below; this test repeats the same 4-formula rotation 25x) | ~3.2x per-call in isolation, but 100 back-to-back solves multiply the exposure window |
| `test_sat_unsat_interleaving_stability` | same default `timeout_ms=5000`, 100 calls (50 pairs) | same per-call baseline | same |
| `test_oracle_m_formula_depth1_boundary_safe` | same default `timeout_ms=5000`, single call on `F_P` at `M=max(1+2,3)=3` | 1.57s measured this session | ~3.2x |
| `test_enriched_vs_primitive_sat_agreement[some_past]` | `TEMPORAL_SOLVE_TIMEOUT_MS = 180000` (widened by the sibling ternary-SAT-fix task; `oracle/bimodal_logic/tests/test_oracle_interface.py:738-741`) | 67.11s measured this session | ~2.7x — the widened budget already gives this one real margin (see section 6) |

None of these numbers, taken alone on an idle machine, look dangerous. All five sit in the same
"budget near typical solve time" zone TESTING_GUIDE 8.6 warns about once six workers are
simultaneously asking Z3 to solve on a 24-core box (`nproc` = 24 here; `flake.nix:113` pins the
sibling bimodal `checks.default` to `-n 6` specifically, with a comment noting `-n auto` is
"avoided due to a documented CPU-contention flake" for that same suite — this repository has
already hit this class of bug once before, for a different test tree).

## 2. Is `xdist_group` the right mechanism, or is `--dist loadfile`/`loadscope` sufficient?

**Neither is a fix for this bug**, and both are answers to a different question than the one this
failure mode asks.

- `@pytest.mark.xdist_group(name=...)` (with `--dist loadgroup`) guarantees that every test
  sharing a group name executes **on the same worker**, so they never run concurrently *with each
  other*. That is the correct tool when tests share worker-affine state (a session-scoped
  fixture, a shared temp file, a database transaction) — which section 1 established does not
  exist here. Putting the five tests in one `xdist_group` would stop them from ever landing on
  two different workers at the same instant, but it does **nothing** about the five *other*
  workers concurrently grinding through the remaining ~545 tests, which is the actual source of
  CPU pressure. The group's one worker is still contending with five siblings for the same 24
  cores.
- `--dist loadfile` / `--dist loadscope` only change how *unmarked* tests are bucketed onto
  workers (by file or by class/module scope, instead of the default individual-item load
  balancing). They do not reduce the number of workers running concurrently and so do not touch
  the contention mechanism either.

**Recommendation**: introduce a new custom mark — call it `xdist_serial` — applied to the tests
in section 4, and run the suite as **two separate invocations** rather than one `-n 6` session:

```bash
# Pass 1: everything except the contention-sensitive tests, in parallel.
pytest oracle/ -n 6 -m "not xdist_serial"

# Pass 2: the contention-sensitive tests, with zero other pytest workers running.
pytest oracle/ -m "xdist_serial"
```

This is the only construct that actually removes the six-way CPU contention for the small
tight-budget set: pass 2 runs with no sibling pytest workers competing for cores at all (other
processes on the machine notwithstanding — see section 5). This is the same result task 127's
own triage already demonstrated empirically: "Re-ran the 5 failures not on the plan's watch list
together in one serial (no `-n`) invocation: `5 passed in 179.26s (2:59)`" — a combined serial
re-run of exactly this class of test cleared instantly. `xdist_group` is optional and harmless as
a belt-and-suspenders addition inside pass 1 (in case someone runs the full suite as one `-n 6`
invocation without splitting), but it is not sufficient on its own.

## 3. Where do custom marks get registered, and what config does `oracle/` actually use?

**Confirmed empirically** (not assumed): invoking `pytest oracle/bimodal_logic/tests/test_cli.py
--collect-only` from the repository root prints:

```
rootdir: /home/benjamin/Projects/ModelChecker
plugins: xdist-3.8.0
```

with **no `inifile:` line** — pytest found no `pytest.ini`, `pyproject.toml` with
`[tool.pytest.ini_options]`, `tox.ini`, or `setup.cfg` anywhere in its search path for this
invocation. `differential` and `slow` *are* already registered, but only in
`code/pyproject.toml:90-91` (`[tool.pytest.ini_options].markers`) — a file that lives under
`code/`, which is **not an ancestor directory of `oracle/`**. pytest's rootdir/inifile discovery
walks upward from the common ancestor of the invocation args; since the repo root
(`/home/benjamin/Projects/ModelChecker`) has no ini file of its own and `code/pyproject.toml` is
a sibling-not-ancestor of `oracle/`, a `pytest oracle/` invocation from the repo root never
reaches it. This reproduces the exact warning:

```
oracle/bimodal_logic/tests/test_cross_oracle_differential.py:906: PytestUnknownMarkWarning:
Unknown pytest.mark.differential - is this a typo?
```

`find oracle -maxdepth 2 -iname pyproject.toml -o -iname "requirements*.txt" -o -iname setup.py`
returns nothing — reconfirming the sibling task's finding that `oracle/` has no dependency
manifest of its own. It relies entirely on the invoking shell's `PYTHONPATH` (`code/src` plus the
`BimodalHarness` sibling checkout) and whatever ini file happens to be discoverable from the
invocation's cwd — currently none.

**Fix**: add `oracle/conftest.py` with a `pytest_configure` hook:

```python
def pytest_configure(config):
    config.addinivalue_line(
        "markers", "differential: Tests that compare MC oracle against reference oracles",
    )
    config.addinivalue_line(
        "markers", "slow: Tests that are computationally expensive and skipped in CI",
    )
    config.addinivalue_line(
        "markers", "xdist_serial: Tests sensitive to CPU contention under parallel execution; "
                    "run these in a separate non-parallel pytest invocation (see oracle/README.md)",
    )
```

A `conftest.py` is the right container rather than a new `oracle/pytest.ini` or
`oracle/pyproject.toml`: pytest always loads `conftest.py` files found while walking down to each
collected test file, independent of rootdir/inifile resolution, so this works identically
whether the suite is invoked as `pytest oracle/`, `pytest
oracle/bimodal_logic/tests/test_cli.py`, or (hypothetically) as part of a combined `pytest code/
oracle/` session — and it preserves the property that `oracle/` carries no manifest of its own
(no new `[project]`/`[build-system]` file, no risk of a second, competing `pyproject.toml`
confusing tooling that scans for one). A bare `pytest.ini` would also work and is slightly more
discoverable to a human skimming the tree, but would be pytest's first-found inifile for any
invocation rooted at or under `oracle/`, silently changing rootdir semantics for any future
`oracle/`-scoped `addopts`; `conftest.py` avoids that side effect by registering only what is
asked for (marks) with no ini-file precedence implications.

## 4. Minimal marker set to match serial verdicts

Marking only the exact five previously-observed failures would reproduce this run's specific
outcome but not the underlying invariant ("no test whose budget sits near its typical solve time
runs under `-n` contention"). Two of `TestStateIsolationRegression`'s four methods
(`test_temporal_propositional_interleaving`, `test_no_semantics_reference_leak_with_temporal`)
share the *exact same* class-level `setup_method` and the *exact same* unmodified
`timeout_ms=5000` default as the two methods that did fail — they simply didn't happen to trip
the boundary in that particular `-n 6` run. Task 127's own summary warns explicitly against this
kind of survivorship bias: "The pre-declared watch list was wrong in both directions... any future
oracle-suite triage must re-verify... rather than trusting a prior classification." Recommend
marking the whole class, not just the two methods that already failed once:

- `oracle/bimodal_logic/tests/test_soundness_regression.py:641` —
  `class TestStateIsolationRegression:` (mark the class, covering all 4 methods: both previously
  failing ones and the two same-risk siblings).
- `oracle/bimodal_logic/tests/test_soundness_regression.py:1023-1031` —
  `TestOracleMFormulaBoundarySafe.test_oracle_m_formula_depth1_boundary_safe` only (not the whole
  class): `test_oracle_m_formula_depth0_boundary_safe` solves a trivial depth-0 atom with ample
  margin, and `test_oracle_m_formula_depth2_returns_none` *asserts* `result is None` — contention
  cannot flip that verdict since a spurious timeout still produces `None`, the expected value.
- `oracle/bimodal_logic/tests/test_oracle_interface.py:733-747` —
  `TestEnrichedRoundTrip.test_enriched_vs_primitive_sat_agreement[some_past]` (the single
  parametrize case; see section 6 for why this one is borderline post-widening, and a
  recommendation to mark it anyway pending repeated-sample confirmation).
- `oracle/bimodal_logic/tests/test_boundary_regression.py:447-467` —
  `test_regression_all_active_examples[BM_CM_1-...]` only, by parametrize id. **Do not** mark the
  whole `TestExampleRegression` class: most of its 43 active examples have ample margin, and
  blanket-serializing all of them would erase most of the `-n 6` wall-clock benefit for
  negligible safety gain. `BM_CM_1` (`max_time=15`) is one of several examples in the 5-15s
  budget band (`code/src/model_checker/theory_lib/bimodal/examples.py` shows sibling
  `max_time` values of 5, 10, and 15 scattered across nearby examples); a full per-example margin
  audit across all 43 is a larger, separate effort explicitly out of this research's scope (see
  Non-Goals in the delegation), but is worth flagging as a **known residual risk**: other
  examples with similarly tight `max_time` could still surface as new, unmarked xdist artifacts
  in a future `-n 6` run even after this fix lands, following exactly the same "a watch list built
  from one observation points away from the real failures" pattern task 127 already hit once.

Do **not** mark or otherwise "fix" the `all_future` case in
`test_enriched_vs_primitive_sat_agreement` — task 131's summary already recorded it as a genuine,
independent-of-parallelism timeout (195.47s / 187.63s isolated, both exceeding even the widened
180000ms budget) that happens to still pass because both sides agree (`None == None`). That is a
pre-existing masked-timeout defect, not an xdist artifact, and is explicitly out of scope for
both that task and this one.

## 5. What `-n` value is safe/optimal?

**Keep `-n 6`** for the parallel pass; do not reduce it further, and do not use `-n auto`.

- This repository has already made and validated this exact choice for a sibling suite:
  `flake.nix:95-96,101,113` pins `checks.default` to
  `pytest src/model_checker/theory_lib/bimodal/tests -n 6 -q`, with a comment explicitly noting
  `-n auto` (which would mean 24 workers on this 24-core machine) "is avoided due to a documented
  CPU-contention flake." `-n 6` was chosen there as a deliberate contention ceiling, not an
  arbitrary default, and the reasoning transfers directly: more workers means more simultaneous Z3
  solves competing for the same physical cores, which is precisely the mechanism section 1
  diagnoses.
- Task 131's own handoff to this line of work independently reached the same conclusion: "Use
  `-n 6`, not `-n auto`... since this task's entire failure mode was wall-clock contention against
  a solver budget, `-n auto` risks re-creating the same problem under a different name."
- Once the tight-budget tests from section 4 are pulled into their own serial pass, `-n 6` for
  the remaining ~540+ tests is safe by construction: whatever residual contention exists among
  the *unmarked* tests was already implicitly validated by the two runs on record (task 127's
  full `-n 6` run produced exactly 7 failures, all 7 attributable to the tests this report
  addresses or to the two genuinely-failing tests task 127 and 131 already separately triaged —
  no *other* test in the 550-test suite has been observed to fail under `-n 6` and pass serially).
- Reducing below 6 would only lengthen the parallel pass's wall-clock (currently 44:33 at `-n 6`
  for the full 550, per task 127) for no corresponding safety benefit, since the actual fix is
  exclusion of the handful of tight-budget tests, not blanket concurrency reduction.

## 6. The `some_past` case, and the effect of the widened timeout

The delegation asked whether the recently-widened `TEMPORAL_SOLVE_TIMEOUT_MS = 180000`
(`oracle/bimodal_logic/tests/test_oracle_interface.py:29`, introduced by the sibling ternary-SAT
fix task) changes `test_enriched_vs_primitive_sat_agreement[some_past]`'s status as an xdist
artifact. It does, materially:

- The prior task's own measurement table recorded `some_past` at **64.13s combined** (enriched +
  primitive) against the *old* 60000ms **per-call** budget — already over the nominal single-call
  ceiling before the widening, which is exactly why that task widened it.
- Re-measured this session against the *new* 180000ms budget, in isolation:
  `1 passed in 67.11s` for the whole parametrized case. 67.11s against a 180s ceiling is a ~2.7x
  margin — comfortably inside the same "2x+ headroom, leave unchanged" bar task 131 itself applied
  to other sites it explicitly chose not to widen (e.g. `test_mixed_and_box_next` at 17.53s/14.21s
  against 60000ms was left alone as ">=2x headroom").
- **This means `some_past` is now much less likely to be a pure `-n 6` parallelism artifact than
  it was when task 127's baseline run observed it failing** (that failure was recorded before
  task 131's widening landed). By the same margin standard task 131 already used elsewhere in this
  file, it is now borderline-safe rather than clearly at-risk.
- That said, "borderline-safe" is not the same as "proven safe under six-way contention" — a 2.7x
  margin is smaller than the ~3.2x margin measured for the depth-1 default-timeout tests in
  section 1, and section 1's own numbers show contention can still bite tests with a few-x margin.
  Given the cost of including one more parametrize case in the serial pass is small (this single
  test id, not the whole `TestEnrichedRoundTrip` class), section 4 recommends marking it
  `xdist_serial` anyway, pending the "5-10x repeated isolated runs" re-confirmation step task 131
  itself already recommended as a follow-up before any full-suite baseline is promoted. This is a
  belt-and-suspenders inclusion, not a claim that the widening failed to help — it demonstrably did
  (2.7x margin now vs. sub-1x before).
- Do not conflate this with the `all_future` case in the same class (section 4): `all_future`
  exceeds even the widened budget outright and is a separate, already-documented, non-xdist defect.

## Recommended changes for the implementation phase

1. Add `oracle/conftest.py` with a `pytest_configure` hook registering `differential`, `slow`
   (already-intended, currently orphaned by the ini-discovery gap — section 3), and a new
   `xdist_serial` mark.
2. Apply `@pytest.mark.xdist_serial` to:
   - `TestStateIsolationRegression` (class-level, all 4 methods) in
     `test_soundness_regression.py`.
   - `TestOracleMFormulaBoundarySafe.test_oracle_m_formula_depth1_boundary_safe` (method-level)
     in the same file.
   - `test_enriched_vs_primitive_sat_agreement[some_past]` in `test_oracle_interface.py` — since
     pytest marks apply to the whole parametrized function, not one case, use
     `pytest.param(..., marks=pytest.mark.xdist_serial)` on the `some_past` entry inside
     `ENRICHED_PRIMITIVE_PAIRS`'s construction (or an equivalent per-case marking idiom) rather
     than marking the entire `test_enriched_vs_primitive_sat_agreement` function, so the other
     10 parametrize cases keep running under `-n 6`.
   - `test_regression_all_active_examples[BM_CM_1-...]` in `test_boundary_regression.py` — same
     per-parametrize-case marking idiom applies (`regression_examples` is a dict driving
     `@pytest.mark.parametrize`; either wrap `BM_CM_1`'s tuple in `pytest.param(..., marks=...)`
     before building the parametrize list, or use a small `pytest_collection_modifyitems` hook in
     the new `oracle/conftest.py` that adds the mark to items whose test id contains `BM_CM_1`).
3. Document (in `oracle/README.md` or wherever CI/manual invocation instructions live) the
   two-pass invocation from section 2: `-n 6 -m "not xdist_serial"` then `-m "xdist_serial"`
   (no `-n`).
4. Do not touch `all_future`, do not attempt to widen or fix its timeout here (out of scope, per
   task 131's own finding).
5. Flag, but do not resolve in this task, the residual risk noted in section 4: other examples in
   `examples.py` with 5-15s `max_time` budgets similar to `BM_CM_1` could surface as new,
   currently-unmarked xdist artifacts in a future run.

## References

- `oracle/bimodal_logic/provider.py:169-173` — `Z3OracleProvider.find_countermodel` default
  `timeout_ms: int = 5000`.
- `code/src/model_checker/utils/context.py:19-65` — `isolated_z3_context()`, the process-local
  `z3.z3._main_ctx` swap.
- `oracle/bimodal_logic/tests/test_soundness_regression.py:641-740` — `TestStateIsolationRegression`.
- `oracle/bimodal_logic/tests/test_soundness_regression.py:1004-1041` — `TestOracleMFormulaBoundarySafe`.
- `oracle/bimodal_logic/tests/test_oracle_interface.py:29-31,722-747` — `TEMPORAL_SOLVE_TIMEOUT_MS`,
  `TestEnrichedRoundTrip`.
- `oracle/bimodal_logic/tests/test_boundary_regression.py:431-467` — `TestExampleRegression`.
- `code/src/model_checker/theory_lib/bimodal/examples.py:313-326` — `BM_CM_1_settings`
  (`max_time=15`, comment documenting the ~8s measured solve time this margin was set against).
- `code/pyproject.toml:82-91` — `[tool.pytest.ini_options]`, the existing `markers` list that is
  unreachable from `oracle/`-rooted invocations.
- `code/docs/core/TESTING_GUIDE.md` section 8.6 ("Solver Timing Budgets and Machine Variance").
- `flake.nix:95-96,101,113` — the sibling `-n 6` (not `-n auto`) precedent and its documented
  contention-flake rationale.
- `specs/127_close_oracle_suite_regression_baseline/summaries/01_close-oracle-regression-baseline-summary.md`
  — the triage that produced this task, including the "5 failures pass together serially in
  179.26s" finding this report's recommendation reproduces by design.
- `specs/131_fix_oracle_ternary_sat_regression/reports/01_oracle-ternary-sat-regression.md` and
  its summary — the sibling timeout-widening fix, its margin-based "headroom" bar reused in
  section 6, and the still-open `all_future` finding this report explicitly declines to touch.
