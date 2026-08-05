# Research Report: The `find_countermodel` Return-Value Contract

- **Task**: 133 - fix_oracle_self_consistency_disagreements
- **Date**: 2026-08-05
- **Scope**: `oracle/bimodal_logic/provider.py`'s `Z3OracleProvider.find_countermodel` return
  contract, every caller of it inside `oracle/` and `code/`, and the test-suite migration this
  implies.
- **Supersedes**: the "widen the budget" diagnosis in
  `plans/01_oracle-self-consistency.md` (committed at `f91960d6`). That change is a mitigation of
  a symptom, not a fix of the defect. This report establishes the defect and the safe fix, per
  direction from the user.

## Executive Summary

`find_countermodel()` returns `None` for two semantically opposite outcomes — "the formula is
provably valid" and "the solver gave up without deciding" — and this conflation is not
incidental: it is baked into `Z3OracleProvider.find_countermodel()` itself
(`oracle/bimodal_logic/provider.py:255`), and it is *already the documented external protocol*
for any BimodalHarness oracle provider (`~/Projects/BimodalHarness/docs/oracle-interface-standards.md:195`:
"If UNSAT/UNKNOWN: return None"). The one piece of information needed to fix it —
`structure.timeout: bool`, already computed and already distinguished from
`structure.z3_model_status: bool` inside `code/src/model_checker/models/structure.py` — is
discarded at exactly the point `find_countermodel()` collapses both branches into `return None`.

The safe fix is narrow: raise a dedicated exception when `structure.timeout` is `True`, and leave
`None` meaning *only* "genuine UNSAT" (unchanged for every non-boundary formula in the suite).
This is a fail-fast, no-partial-compatibility-layer change consistent with CLAUDE.md's project
principles, and it is also the design the test harness already half-implements:
`_run_differential_comparison`'s `except Exception: mc_result = "TIMEOUT"`
(`test_cross_oracle_differential.py:414`) has been dead code since it was written, waiting for
`find_countermodel` to actually raise on timeout.

Blast radius inside this repo is real but bounded: 1 production call site (`cli.py`), 1
in-package call site (`validate_self`), and roughly a dozen call sites across four test files —
concentrated in tests that already carry `if result is not None:` skip-guards or existing
`xfail(strict=True)` markers documenting this exact root cause. The committed
`SELF_SCAN_SOLVE_TIMEOUT_MS = 60000` should be reduced sharply (or reverted to something near the
5000ms default) once the contract is fixed, because a correct contract no longer needs a large
budget to avoid corrupting the disagreement count — it needs the budget only to keep the
inconclusive-result rate low enough for the test to stay meaningful.

## A. What the contract should be

### A.1 The information already exists, one layer down

`code/src/model_checker/models/structure.py` already distinguishes three solver outcomes and
never collapses them before `find_countermodel()` gets a chance to:

- `solve()` (`structure.py:210-267`) calls `self.solver.check()` and switches on the Z3 result:
  - SAT -> `_create_result(False, model, True, start_time)` (`structure.py:242-243`)
  - UNSAT -> `_create_result(False, unsat_core, False, start_time)` (`structure.py:245-246`)
  - UNKNOWN -> `_create_result(True, None, False, start_time)` (`structure.py:260`), with an
    in-code comment (`structure.py:248-259`) explicitly warning that `reason_unknown()` is *not*
    reliably the literal string `"timeout"` (Z3 often reports `"canceled"` or MBQI-related
    strings) and that any UNKNOWN must be treated as inconclusive, "regardless of the specific
    reason string" — i.e. this file already had its own conflation bug (UNKNOWN silently
    misread as UNSAT) and was already hardened against it.
- `_process_solver_results()` (`structure.py:108-134`) unpacks that 4-tuple into
  `self.timeout: bool` and `self.z3_model_status: bool` as two **separate** attributes on the
  structure object. Note that whenever `timeout=True`, `z3_model_status` is unconditionally
  `False` too (every UNKNOWN branch sets `is_satisfiable=False`), which is exactly why
  `provider.py`'s current `if structure.timeout or not structure.z3_model_status:` reads as one
  `return None` branch — the two predicates are never in conflict, they are just merged.

So the fix does not need to invent a new signal. It needs to stop discarding one that already
exists at `provider.py:255`:

```python
# Current (provider.py:254-257):
if structure.timeout or not structure.z3_model_status:
    self._semantics = None
    return None
```

should become (sketch, not a diff to apply — this is research, not implementation):

```python
if structure.timeout:
    self._semantics = None
    raise <TimeoutException>(...)   # new signal: inconclusive, not "valid"
if not structure.z3_model_status:
    self._semantics = None
    return None                      # unchanged: genuine UNSAT / valid formula
```

### A.2 The unit conversion is correct — rule this out explicitly

The delegation context asked whether the ms/seconds round-trip composes correctly. It does:
`provider.py:233` sets `settings['max_time'] = timeout_ms / 1000.0` (ms -> seconds).
`structure.py:69` stores it unchanged as `self.max_time` (seconds). `structure.py:237`
(`solve()`) does `self.solver.set_timeout(int(max_time * 1000))` (seconds -> ms). Round-trip:
`timeout_ms=5000 -> max_time=5.0s -> set_timeout(int(5.0*1000))=5000`. No off-by-1000 bug, no
truncation bug at any budget used in this codebase (the `int()` truncation only bites below 1ms
resolution). `re_solve()` (`structure.py:286`) performs the identical seconds->ms conversion
against the already-in-seconds `self.max_time`. **This is not where the defect lives.** The
defect is entirely in what `find_countermodel()` does with `structure.timeout` after the solve
completes, not in how the budget got there.

### A.3 Existing sentinel/exception conventions to reuse the *shape* of, not the *class* of

`oracle/bimodal_logic/` has no `errors.py` of its own and is not part of the `model_checker`
package proper (confirmed: no `pyproject.toml`/`setup.cfg`/`setup.py` under `oracle/`, per the
existing `_ENTRY_POINT_XFAIL_REASON` in `test_oracle_interface.py:1138-1150` — the package is
deliberately PYTHONPATH-only, never pip-installed). It should not reach into
`code/src/model_checker/theory_lib/errors.py`'s `Z3TimeoutError` (a theory_lib-specific class,
unused anywhere in production code today — `grep` confirms zero non-test call sites) purely to
borrow a class; that would create an odd cross-package dependency for a one-off timeout signal.
But the **shape** of that convention is exactly right and should be mirrored locally:

- `code/src/model_checker/theory_lib/errors.py:230` `Z3TimeoutError(timeout_seconds, **kwargs)` —
  message + a `context` dict carrying `timeout_seconds`, plus a `suggestion` field.
- `code/src/model_checker/iterate/errors.py:151` `IterationTimeoutError` — same domain-specific
  timeout-exception pattern, actively raised and tested (`iterate/tests/**`).
- `code/src/model_checker/models/errors.py:28` `ModelSolverError` — already raised by
  `structure.solve()` itself, but only for a `RuntimeError` from the solver
  (`structure.py:262-264`), never for the UNKNOWN/timeout branch. This is the closest
  in-package precedent and the strongest argument that "solver gave up" deserves an exception,
  not a sentinel — `ModelSolverError` already treats *other* solver failure modes this way.

Recommendation: add a small `oracle/bimodal_logic/errors.py` with one class (naming is an
implementation-phase decision, e.g. `OracleTimeoutError(Exception)`), carrying at minimum the
formula's `temporal_depth`/`M`/`timeout_ms` as context (mirroring the `Z3TimeoutError` shape),
raised from `find_countermodel()` when `structure.timeout` is `True`. This keeps `None` meaning
*exclusively* "proven no countermodel" — an unambiguous, unchanged meaning for every caller that
never touches a boundary-straddling formula — while making "inconclusive" a loud, unmissable,
un-ignorable event rather than a silently-wrong return value. This is the fail-fast principle in
CLAUDE.md applied directly: "Early validation of inputs, Immediate error reporting, Clear error
messages."

**Unsupported `frame_class` is a separate, pre-existing `None` case** (`provider.py:203-204`) and
is out of scope for this fix — it is a real "not applicable" case, already documented, already
exercised by 3 passing tests (`test_unsupported_frame_class_returns_none`,
`test_unsupported_frame_class_dense`, `test_unsupported_frame_class_arbitrary`), and does not
share the SAT/UNSAT/TIMEOUT three-way ambiguity this report is about. Leave it alone.

## B. Blast radius

### B.1 Production and library call sites (2, both need the same one-line change)

| Call site | Current pattern | Required change |
|---|---|---|
| `oracle/bimodal_logic/provider.py:292` `validate_self()` | `if result is None: return False` | Decide (implementation-phase question, not settled here): let the new exception propagate uncaught (loudest, most fail-fast — a spot-check that can't get a verdict is a tooling problem, not "the oracle is unsound"), or catch it and still return `False`. Either is defensible; propagating is more consistent with the rest of this fix. |
| `oracle/bimodal_logic/cli.py:91-96` | `if result is None: output = {"result": "valid", ...}` | This is a **real user-facing correctness bug today**: a CLI invocation whose solve times out currently prints `{"result": "valid", "countermodel": null}` — a false claim of validity — and exits 0. Must catch the new exception and emit a distinct `{"result": "inconclusive", ...}` (or similar) with a non-zero, non-1 exit code (1 is already used for argument/JSON errors) so scripts consuming this CLI can tell "valid" from "we don't know." |

### B.2 In-repo test call sites

Every test file under `oracle/bimodal_logic/tests/` that calls `find_countermodel` was audited
for the `is None` / `is not None` idiom. They fall into three buckets:

**Bucket 1 — unaffected (hard `is None`/`is not None` assertions on non-boundary formulas).**
The overwhelming majority: `test_oracle_provider.py` (`TestFindCountermodelContract` and later
classes, ~20 assertions), most of `test_soundness_regression.py` (~25 assertions), and
`test_oracle_interface.py`'s `TestKnownFormulaBaseline`-style tests. These use small, simple
formulas (`SIMPLE_SAT_JSON`, `atom(A)`, `F(p)`, tautologies) that resolve well inside any
reasonable budget and are not near the boundary. **No behavior change** under the fix — `None`
still means the same thing it always did for these formulas.

**Bucket 2 — must be migrated (currently encode the *old*, ambiguous contract as correct
behavior):**

- `test_oracle_interface.py:1099-1106` `test_timeout_handling` — asserts
  `result is None` for `timeout_ms=1`, i.e. it currently *tests that a timeout looks like a
  valid formula*. Must become `pytest.raises(<TimeoutException>)`.
- `test_oracle_interface.py:1263` `test_deeply_nested_enriched` — asserts
  `isinstance(result, (dict, type(None)))`, explicitly "just ensure no crash" for a formula that
  may or may not resolve. Must wrap in `try/except` and accept the new exception as a third valid
  outcome, or the test will crash the moment the contract changes.
- `test_oracle_interface.py:1010-1030` (`test_boundary_safe_true_for_all_examples`),
  `:1023-1030` are actually the same block — `if result is not None:` guards that currently
  silently skip *both* genuine-UNSAT-for-a-supposedly-SAT-formula *and* timeout cases without
  distinguishing them (their own docstrings say "non-timeout" but the code can't tell). These
  need explicit `try/except` so a timeout is skipped-and-logged (matching stated intent) while an
  unexpected genuine UNSAT for a formula the test believes is SAT becomes a real, loud failure
  instead of a silent no-op — this is a **latent-bug-detection improvement**, not just
  busywork.
- `test_oracle_interface.py:995-996`, `:1011` — same `if result is not None:` pattern in
  `test_time_bound_formula` / `test_temporal_depth_correct_in_output`, same treatment.
- `test_oracle_provider.py:372` and `:531` — same permissive pattern
  (`test_folded_json_for_enriched_input`, `test_boundary_safe_consistency`); low risk (small
  formulas) but should be migrated for consistency and to stop masking anything.
- `test_cross_oracle_differential.py` reference-function closures at lines 1373, 1400, 1420,
  1478, 1503-1504, 1528, 1544, and `_run_differential_comparison` itself (line 407-415): every
  `ref_fn`/inline closure that does `"SAT" if result is not None else "UNSAT"` needs to catch the
  new exception and map it to `"TIMEOUT"`, matching what `_run_differential_comparison` already
  does on its own `mc_output` side. **Critically**, `_generate_differential_report`
  (line 1231-1232) calls `reference_fn(formula_json)` *outside* any try/except — today that's
  safe because `find_countermodel` never raises for a timeout, but the moment it does, every
  `ref_fn` that doesn't handle the exception itself will crash the whole report generation
  instead of recording a `"TIMEOUT"` entry. This is the single most important migration point:
  get it wrong and the fix regresses report generation from "silently wrong" to "hard crash on
  first boundary formula," which is *directionally* correct (loud beats silent) but is not the
  intended, informative three-way classification the report/timeout_count fields already exist
  to hold.

**Bucket 3 — currently green, self-consistency-shaped, latent risk (not currently `xfail`, not
currently observed failing, but structurally identical to the bug this task is about):**

- `test_cross_oracle_differential.py:1495-1520` `TestCIGate::test_temporal_only_self_consistency`
  — calls `find_countermodel` **twice** on each of 30 temporal-only complexity<=5 formulas at the
  **default** (unwidened) 5000ms budget, and compares `result1 is not None` against
  `result2 is not None`. This is the exact same double-solve/boundary-straddle shape as
  `test_complexity_5_scan_self_consistent` (the test task 133 was originally filed against), just
  with a 30-formula sample instead of 274 and no committed budget widening. It runs in **normal
  CI** (`TestCIGate`'s docstring: "These tests run in normal CI on every bimodal code change").
  It is not currently `xfail`'d and its evidence trail (`differential-disposition.md`) does not
  mention it, meaning either it has not yet drawn an unlucky sample, or it has and nobody
  connected it to this root cause. **This test must be included in the migration scope**: once
  `find_countermodel` raises on timeout, this test's two calls need the same
  try/except-and-classify treatment as the complexity-5 scan, or it will begin crashing
  (correctly, but uninformatively) instead of comparing.

### B.3 The five pre-existing `xfail(strict=True)` tests in `test_cross_oracle_differential.py`

Lines 786, 961, 1039, 1152, and 1460 all carry `reason=` strings that already name this exact
root cause (root-caused under an earlier task, documented in
`specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/differential-disposition.md`).
Once the contract is fixed, these five tests' *failure mode* changes: today they fail via a soft
`assert not failures` (a `list` of formulas that returned `None` when a countermodel was
expected); after the fix, the first boundary-straddling formula in each loop will instead raise
the new exception mid-loop, still counting as an `xfail`'d failure (pytest's default `xfail`
catches any exception, not just `AssertionError`) but destroying the "count of exactly N
failing formulas" diagnostic the current soft-assert produces. **Recommendation for the
follow-on plan**: rewrite these five loops to catch the new exception per-formula and bucket
results into `resolved-and-wrong` vs. `inconclusive`, so the tests can be un-`xfail`'d in favor of
an assertion that only fails on `resolved-and-wrong` results (a real soundness bug) and reports
(without failing on) the inconclusive-at-default-budget count. This converts five tests from
"permanently expected to fail" into either passing outright or failing only when something is
actually, provably wrong — which is a strictly better end state than the current disposition,
and was explicitly out of scope for the earlier task that filed them as `xfail` ("Raising the
default timeout suite-wide is explicitly out of scope for this task" —
`differential-disposition.md` line ~76). This task's contract fix removes the reason that
scoping boundary existed: the fix no longer requires raising any default timeout budget
suite-wide, because inconclusive results stop being silently wrong.

### B.4 Out-of-repo consideration (informational only — confirmed non-blocking)

`~/Projects/BimodalHarness/docs/oracle-interface-standards.md` documents `find_countermodel(...)
-> dict | None` as *the* formal cross-repo protocol for any registered oracle provider
(`provider_id = "bmlogic_z3_base_v1"` in `provider.py:150` matches the harness's own example
verbatim), and its own "Tiered Oracle Architecture" section explicitly designs around "if Tier 1
returns `None` (UNSAT or timeout), Tier 2 receives the remaining budget" — i.e. the harness's
*planned* design also currently treats UNSAT-or-timeout as one signal. However, this is
confirmed **non-blocking for this task**: `oracle/` ships with zero packaging metadata and is
never entry-point-registered with BimodalHarness in this deployment model (confirmed by the
already-`xfail`'d `test_entry_point_registered` / `test_entry_point_loads_correct_class` in
`test_oracle_interface.py:1156-1180`, whose reason string states "no package declares the
`bimodal_harness.oracle_providers` entry-point group ... entry_points(group=...) is
unconditionally empty in this deployment model, deterministically, on every run"). So today,
nothing in BimodalHarness actually calls into *this* provider's `find_countermodel` in
production; only this repo's own test suite does. If this provider is ever wired into
BimodalHarness for real, the external protocol doc would need a coordinated update alongside it
— flagged here so a future task doesn't rediscover the same tension, but it does not enlarge this
task's blast radius today.

## C. Test-suite impact summary

| Category | Count (approx.) | Action |
|---|---|---|
| Non-boundary `is None`/`is not None` assertions (Bucket 1) | ~45 across 3 files | None — unaffected |
| Tests directly encoding the old ambiguous contract as correct (Bucket 2) | ~11 across 2 files | Must migrate to `try/except`/`pytest.raises` |
| `ref_fn`/`_run_differential_comparison` closures needing exception-to-`"TIMEOUT"` mapping | 8 closures + `_generate_differential_report`'s uncaught `reference_fn()` call | Must migrate — highest-risk miss (crash vs. classify) |
| Currently-green, CI-running, structurally-identical latent-risk test (Bucket 3) | 1 (`test_temporal_only_self_consistency`) | Must migrate alongside the scan test it mirrors |
| Pre-existing `xfail(strict=True)` tests rooted in this exact cause | 5 | Should be rewritten to bucket "inconclusive" vs. "wrong," not merely left `xfail`'d |
| Pre-existing `xfail(strict=True)` tests, unrelated (entry-point packaging) | 4 | Untouched — different root cause entirely |

### On the committed `SELF_SCAN_SOLVE_TIMEOUT_MS = 60000`

This should be revisited, not left as-is. It was sized purely to relocate the boundary far enough
out that the *old*, ambiguous contract wouldn't misclassify a timeout as UNSAT within the scan's
274-formula sweep — i.e., it was chosen to compensate for the defect this report identifies, not
because 60s of genuine solve time is actually needed per formula. Evidence against keeping it:

- At 548 solves (274 formulas x 2, per the delegation context), a 60000ms worst case is ~9.1
  hours — already measured to exceed the plan's own 2h30m abort ceiling, and an isolated run was
  killed after 56 minutes with no output.
- `test_soundness_regression.py`/`test_oracle_interface.py`'s own timeout constants
  (`TEMPORAL_SOLVE_TIMEOUT_MS = 180000` for one, `ATEMPORAL_SOLVE_TIMEOUT_MS = 10000` for
  another, most ad hoc uses at `30000`/`60000` for single formulas, not 274-formula sweeps) show
  the suite already treats "wide margin for a handful of known-slow individual formulas" very
  differently from "wide margin applied to every formula in a large sweep."

Once `find_countermodel` raises instead of silently misreporting, the scan's budget no longer
needs to out-run the boundary — it only needs to be large enough that the *rate* of inconclusive
results stays low enough for the test to remain a meaningful signal rather than mostly reporting
"inconclusive." A budget close to the pre-existing 5000ms default (or a modest multiple of it,
e.g. 10000ms, matching `ATEMPORAL_SOLVE_TIMEOUT_MS`'s existing precedent) is very likely
sufficient and keeps total worst-case wall clock for 548 solves in the single-digit-minutes range
instead of hours. The exact number is an implementation-phase tuning decision, not something to
fix by research alone — but "keep 60000ms unchanged" should not be the default going forward.

## D. What `test_complexity_5_scan_self_consistent` should assert

The delegation context's framing is exactly right: **"zero disagreements among conclusive
results" is not the same claim as "zero inconclusive results,"** and the test should assert only
the former.

Recommended shape (conceptual, not literal code — an implementation-phase concern):

1. For each formula, run both solves (`ref_fn`'s and the direct `_run_differential_comparison`
   call), catching the new timeout exception on **both** sides independently.
2. Classify each formula into one of:
   - **agree**: both sides conclusive (SAT/SAT or UNSAT/UNSAT) and matching — expected, common
     case.
   - **disagree**: both sides conclusive but mismatched (SAT vs UNSAT) — a real soundness bug;
     this is the only category the test should fail on.
   - **inconclusive**: either side raised the timeout exception — informational, not a failure
     by itself, because two independent solves of a formula sitting near the wall-clock boundary
     legitimately can land on opposite sides of "finished" vs. "didn't," under real machine-load
     jitter, without either solve being *wrong*. This is the report's `timeout_count` field,
     already present in `_generate_differential_report`'s return value
     (`test_cross_oracle_differential.py:1252`) and already dead/unreachable — this fix makes it
     live.
3. Assert `disagreements == 0` (unchanged assertion target, but now over a well-defined,
   non-ambiguous category).
4. Additionally assert (or at minimum report loudly) that the inconclusive rate stays bounded —
   e.g. `inconclusive_count < some_small_fraction * total_formulas` — so the test cannot silently
   degrade into "always inconclusive, technically passing" if some future change starves the
   budget. This directly answers the "distinguish zero disagreements from zero inconclusive
   results" framing: the test should tolerate the latter (bounded) while never tolerating the
   former.

This gives task 127's downstream regression baseline a result that means what it says: a pass
means "no soundness disagreement was found among formulas the solver actually decided," not "no
disagreement was found because most of the sweep silently timed out and got counted as
agreement."

## Files examined (grounding index)

- `oracle/bimodal_logic/provider.py` (full file) — the contract itself, `find_countermodel`
  (lines 169-275), `validate_self` (277-295).
- `code/src/model_checker/models/structure.py` (lines 1-330) — `solve()`/`re_solve()`/
  `_process_solver_results()`, the `timeout`/`z3_model_status` distinction and the ms/seconds
  round-trip.
- `oracle/bimodal_logic/cli.py` (full file) — the one production consumer of `result is None`.
- `oracle/bimodal_logic/tests/test_oracle_provider.py`, `test_oracle_interface.py`,
  `test_soundness_regression.py`, `test_cross_oracle_differential.py` — every `find_countermodel`
  call site and every `is None`/`is not None` idiom, enumerated above.
- `code/src/model_checker/models/errors.py`, `code/src/model_checker/theory_lib/errors.py`
  (`Z3TimeoutError`, lines 200-234), `code/src/model_checker/iterate/errors.py`
  (`IterationTimeoutError`) — existing timeout-exception conventions in this codebase.
- `~/Projects/BimodalHarness/docs/oracle-interface-standards.md` and
  `~/Projects/BimodalHarness/src/bimodal_harness/oracle/protocol.py` — external protocol
  definition and confirmation that this provider is not currently entry-point-registered there.
- `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/differential-disposition.md`
  and `.../oracle-suite-disposition.md` — prior root-cause documentation of the same defect,
  scoped to `xfail` rather than fix-forward for reasons that no longer apply once the contract
  changes.
- `specs/133_fix_oracle_self_consistency_disagreements/plans/01_oracle-self-consistency.md` and
  commit `f91960d6` — the prior mitigation this report supersedes.
