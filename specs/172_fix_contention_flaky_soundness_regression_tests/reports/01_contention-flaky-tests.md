# Research: contention-flaky soundness regression tests (oracle bimodal_logic)

## Scope

Three tests in `oracle/bimodal_logic/tests/test_soundness_regression.py` fail under the
gating suite's parallel pass (`-n 6`) but pass in isolation, per the measured 2026-08-26
two-pass run cited in the task description:

- `TestBoundaryVacuity::test_depth1_countermodel_has_required_fields`
- `TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output`
- `TestGuardedCompositionality::test_nullity_with_temporal_formula_output`

All three call `Z3OracleProvider.find_countermodel()` on `F_P` (`some_future(atom p)`,
`temporal_depth=1`) with no `timeout_ms` override, so they inherit the provider's
`timeout_ms=5000` default. Under `-n 6` they hit `OracleTimeoutError` at
`oracle/bimodal_logic/provider.py:292`; serially all three pass in 4.53s total (~1.5s
each) — roughly a 3.3x headroom over the 5s budget, which six-way contention erodes.

## Finding 1: this is the exact class 8.6/8.12/8.13 already name, with an existing in-file precedent

`code/docs/core/TESTING_GUIDE.md` section 8.12 (`xdist_serial`) describes precisely this
shape: "a real wall-clock timing assertion that has adequate headroom under normal
conditions, but which CPU contention under pytest-xdist's `-n` worker pool can push past
budget." `oracle/conftest.py` mirrors the marker for the oracle suite's own
parallel/serial split, and `oracle/run-oracle-suite.sh` already runs pass 1 with
`-n 6` deselecting `xdist_serial` and pass 2 serially selecting it.

`test_soundness_regression.py` already contains a directly analogous, already-fixed
sibling at line 1092-1097:

```python
@pytest.mark.xdist_serial
# ~3.2x measured headroom over the default timeout_ms=5000, but CPU
# contention under pytest-xdist can still erode that margin (see
# code/docs/core/TESTING_GUIDE.md section 8.6): run serially, never
# under -n (oracle/run-oracle-suite.sh's second pass).
def test_oracle_m_formula_depth1_boundary_safe(self):
    """depth=1 formula: oracle uses M=max(1+2,3)=3, boundary_safe=True."""
    result = self.provider.find_countermodel(F_P)
    ...
```

This is the **same formula** (`F_P`), the **same default budget** (`timeout_ms=5000`),
and the **same measured headroom** (~3.2x there, ~3.3x in the task's fresh measurement)
as the three failing tests. The class-level precedent at line 664
(`TestStateIsolationRegression`, marked `@pytest.mark.xdist_serial` at the class level)
documents the identical rationale for four methods that share the unmodified
`timeout_ms=5000` default.

**Recommendation: adopt remedy (a) — mark exactly these three tests
`@pytest.mark.xdist_serial`, using the same per-method decorator + inline comment
style as the existing `test_oracle_m_formula_depth1_boundary_safe` precedent** (each
method sits in a class with other fast, depth-0 or exception-only-path methods, so a
class-level mark would over-serialize; match the precedent's per-method style, not the
`TestStateIsolationRegression` class-level style).

## Finding 2: option (b)/(c) (`max_rlimit`) is not warranted here — TESTING_GUIDE 8.13 already worked through this exact tradeoff

Section 8.13 ("The Example Solve-Budget Floor") documents that `max_rlimit` was
*evaluated and deliberately rejected* for the motivating `CL_TH_12`/`CL_TH_13` flake —
a case with the same shape (a near-budget solve destabilized by CI contention). The
reasoning transfers directly:

> "An `rlimit` bound can only ever cause an inconclusive result, never prevent one. It
> has no mechanism to rescue a solve; it only supplies an additional way to fail."

For these three tests, moving them to the serial pass (`xdist_serial`) already fully
removes the `-n`-pool contention that causes the failure — there is no residual
wall-clock risk left for `max_rlimit` to address once a test is not competing with five
other workers. Adding `max_rlimit` on top would only add a second, independent way for
the test to fail (an rlimit-exhausted `OracleTimeoutError`) without adding any
correctness benefit, and 8.13 explicitly names this as the wrong tradeoff. `max_rlimit`
is warranted "where a wall-clock budget cannot be widened far enough to be safe" — not
the case here, since `xdist_serial` sidesteps the load variance entirely rather than
trying to out-budget it.

**Recommendation: do not pass `max_rlimit` at these three call sites.** Record this
decision (with the 8.13 citation) rather than silently omitting it, per the task's
explicit "decide explicitly with reasons recorded" instruction.

## Finding 3: pass-2 budget headroom is not a concern

Pass 2 is currently 677.08s (15 tests) against a stated ~1800s (30 min) budget mentioned
in `.github/workflows/tests.yml`/`oracle/run-oracle-suite.sh`'s own headroom framing (the
task description cites "677.08s...confirm it stays inside" an 1800s budget). Each of the
three tests measured ~1.5s serially; adding all three to pass 2 adds roughly 4.5s,
taking pass 2 to ~682s — trivial against the 1800s ceiling. No further verification
beyond the required full two-pass run is needed to confirm this stays inside budget.

## Finding 4: a fourth call site with an identical risk profile exists in the same file, in scope but not in the reported failure list

`TestBoundaryVacuity::test_depth1_boundary_safe_is_true` (line ~396-408, same file, same
class as `test_depth1_countermodel_has_required_fields`) also calls
`self.provider.find_countermodel(F_P)` with no `timeout_ms` override — byte-for-byte the
same risk profile as the three reported failures (same formula, same default budget,
same unmarked status). It did not appear in the task's measured failure list, which is
consistent with contention-driven flakiness being probabilistic (worker/CPU scheduling
noise) rather than deterministic-per-call, not evidence that it is safe.

This test is inside the task's `file_scope` (same file), so nothing prevents fixing it
alongside the three named tests. Flagging it explicitly for the plan/implementation
stage to decide whether to include it — the task's own CONSTRAINTS section requires
verification via the real two-pass driver rather than narrowed selection, and leaving a
same-class, same-file, unmarked sibling in place risks a second round of exactly this
report.

## Finding 5: on whether `timeout_ms=5000`'s default deserves a floor guard analogous to `test_example_budget_floor.py`

Surveyed every `find_countermodel()` call site under `oracle/` (grep across
`oracle/**/*.py`, ~110 call sites total):

- **Most call sites already pass an explicit, generous `timeout_ms`** — named constants
  like `TEMPORAL_SOLVE_TIMEOUT_MS`, or literals `30000`/`60000`/`240000` — in
  `test_oracle_interface.py` and `test_cross_oracle_differential.py`. These already
  learned the lesson 8.6/8.13 teach; they are not at risk.
- **Bare (no-`timeout_ms`) calls concentrate in two places**: `test_soundness_regression.py`
  (this task's target file) and `test_oracle_provider.py` (NOT in this task's
  `file_scope`).
- Within `test_soundness_regression.py`, every other bare-default call site is either
  (a) a depth-0 formula (`ATOM_A`, `TAUTOLOGY`) — fast (sub-100ms observed elsewhere in
  this tree), no measured or plausible contention risk, or (b) already inside a class
  or method carrying `xdist_serial` (`TestStateIsolationRegression`,
  `test_oracle_m_formula_depth1_boundary_safe`), or (c) inside `TestKnownBoundaryUnsafe`,
  whose five tests all *assert* `pytest.raises(OracleTimeoutError)` — contention can only
  make the expected timeout *more* likely, never turn a pass into a failure, so these
  are not flaky by construction regardless of load.
- In `test_oracle_provider.py` (out of `file_scope`), `test_future_sat_returns_dict`
  calls `find_countermodel(FUTURE_SAT_JSON)` (`some_future(atom A)`, `temporal_depth=1`)
  with the bare default — the same risk class, unmarked. This is evidence the class
  extends beyond the three reported failures and beyond this task's `file_scope`, but it
  cannot be fixed inside this task without violating `file_scope`.

**Why a floor guard shaped like `test_example_budget_floor.py` does not fit this
population, and the recommendation is against building one here:**

`test_example_budget_floor.py`'s guard works because the risk is a *per-call-site
literal* (`'max_time': N` inside a dict literal) that can be raised independently at
each site with zero cost to other callers. `timeout_ms=5000` here is a *shared function
default* on `Z3OracleProvider.find_countermodel()` — raising the default itself would
change behavior for every caller, including the many call sites that already pass their
own explicit, deliberately-chosen budgets (`cli.py`, `probe_solve_cost.py`,
`scan_runner.py`, and the dozens of already-overridden test call sites), none of which
this task's evidence says are broken. The actual risk factor is not the default's
*value* but the *combination* of (unmarked bare call) x (formula with
`temporal_depth>=1`, since depth-0 formulas are consistently fast) — and unlike a `dict`
literal's `max_time` key, `temporal_depth` is not staticaly readable from the call site
without resolving the formula argument (a module-level JSON dict, often built via
helper functions like `fold_formula`/`json_to_prefix` in other files), which the AST
scan technique `test_example_budget_floor.py` uses cannot do without also risking false
positives on the `TestKnownBoundaryUnsafe`-style raises-timeout-on-purpose tests, whose
bare calls are correct as written.

**Decision: do not add an AST floor guard for oracle `timeout_ms` call sites in this
task.** The three (or four, per Finding 4) known instances are better and more cheaply
fixed with the existing, purpose-built `xdist_serial` marker mechanism (8.12), which is
exactly what the sibling precedent at line 1092 already demonstrates. The `test_oracle_provider.py`
instance found in Finding 5 is out of `file_scope` for this task; record it as a
candidate for a narrowly-scoped follow-up task (e.g. via `/spawn`) rather than pulling
it into this task's file_scope.

## Summary of recommended remedy

1. Mark the three named tests `@pytest.mark.xdist_serial`, matching the existing
   `test_oracle_m_formula_depth1_boundary_safe` precedent's per-method decorator +
   inline comment style (cite the measured ~3.3x headroom and the 5000ms budget).
2. Decide, and include in the plan/summary, whether to also mark
   `test_depth1_boundary_safe_is_true` (Finding 4) — same file, same risk profile, in
   scope, not in the reported failure list.
3. Do not touch `provider.py`'s `timeout_ms`/`max_rlimit` defaults or call the three
   tests with `max_rlimit` (Finding 2) — record the 8.13-grounded reason explicitly.
4. Do not add a floor-guard test to `code/tests/ci/test_example_budget_floor.py` for
   this population (Finding 5) — record the reason explicitly (population doesn't fit
   the literal-scan guard shape; the marker mechanism already covers it more cheaply).
   `test_example_budget_floor.py` itself needs no code change.
5. Verify with the full `bash oracle/run-oracle-suite.sh` two-pass run, not a narrowed
   selection, per the task's CONSTRAINTS. Expect pass 1 to drop from 3 failures to 0,
   pass 2 to grow from 15 to 18 (or 19 if Finding 4 is included) tests and from 677.08s
   to roughly 682-686s, comfortably inside the ~1800s budget.

## Files read

- `oracle/bimodal_logic/tests/test_soundness_regression.py` (full file, 1152 lines)
- `oracle/bimodal_logic/provider.py` (full file)
- `code/tests/ci/test_example_budget_floor.py` (full file)
- `code/docs/core/TESTING_GUIDE.md` sections 8.6, 8.8, 8.12, 8.13
- `oracle/bimodal_logic/tests/test_oracle_provider.py` (targeted grep + excerpt)
- Grep survey of all `find_countermodel(`/`timeout_ms` occurrences across `oracle/`
