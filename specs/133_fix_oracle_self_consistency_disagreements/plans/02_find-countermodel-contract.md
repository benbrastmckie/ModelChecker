# Implementation Plan: The `find_countermodel` Timeout/UNSAT Contract

- **Task**: 133 - fix_oracle_self_consistency_disagreements
- **Status**: [NOT STARTED]
- **Effort**: 8 hours attended (plus ~2-2.5 hours unattended background wall clock in Phase 7)
- **Dependencies**: None. Blocks task 127 (oracle-suite regression baseline), which in turn blocks task 126.
- **Research Inputs**:
  - `specs/133_fix_oracle_self_consistency_disagreements/reports/02_find-countermodel-contract.md` (authoritative)
  - `specs/133_fix_oracle_self_consistency_disagreements/reports/01_oracle-self-consistency.md` (superseded diagnosis; mechanism observations retained)
  - `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_5s_partial.log` and `evidence/scan_instrumented.py`
- **Artifacts**: plans/02_find-countermodel-contract.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/plan-format-enforcement.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
  - `code/docs/core/TESTING_GUIDE.md` (mandatory TDD; section 8.6 on solve-budget sizing)
- **Type**: python

## Supersedes v1

`plans/01_oracle-self-consistency.md` remains on disk as the superseded record. Do not delete or
edit it. It is retained because its Phase 1 was implemented and committed (`f91960d6`), and this
plan must undo part of that commit — a reader needs the original to understand what is being
reverted and why.

**What changed in the diagnosis.** v1 concluded that `test_complexity_5_scan_self_consistent`
failed because the oracle's 5000 ms solve budget sat *inside* one formula's solve-time band, and
fixed it by widening that one test's budget to `SELF_SCAN_SOLVE_TIMEOUT_MS = 60000`. That
observation was correct but the conclusion drawn from it was incomplete. Widening the budget
relocates the boundary; it does not remove the mechanism that makes crossing the boundary
*silently wrong*. Every formula whose true solve time straddles whatever budget is chosen remains
exposed to the same verdict inversion, and the scan's disagreement count remains a load-dependent
quantity rather than a semantic one.

**Three pieces of evidence gathered after v1 was written force the re-aim:**

1. `evidence/scan_5s_partial.log` shows budget-exhausted solves returning `UNSAT` at exactly the
   wall-clock budget (`UNSAT(5.1s)` against a 5000 ms budget, on line after line) while the
   instrumented run's own `T=` (timeout) counter never leaves 0. The solver's give-up is being
   laundered into a proven UNSAT. This is not one boundary-straddling formula; it is the
   normal case for roughly half the sweep.
2. At 60000 ms, 548 solves (274 formulas x 2) have a ~9.1 hour worst case. An isolated run was
   killed after 56 minutes having emitted nothing. `oracle/run-oracle-suite.sh` does **not**
   deselect `slow`, so the scan runs inside the gating suite — the v1 budget makes the whole
   suite unrunnable, which blocks the very downstream baseline v1 was written to unblock.
3. A serial instrumented run at the original 5000 ms budget reached 155/274 with **zero**
   disagreements. The failure is intermittent and load-dependent, not deterministic. A single
   green run therefore proves nothing about the fix, and v1's exit criterion (one green two-pass
   suite run) was weaker than it read.

**What this plan does instead.** It fixes the contract: `find_countermodel()` stops collapsing
"provably valid (UNSAT)" and "solver exhausted its budget (UNKNOWN)" into the same `None`. The
signal already exists — `structure.timeout` is computed and deliberately kept separate from
`z3_model_status` at `code/src/model_checker/models/structure.py:108-134` — and is discarded at
`oracle/bimodal_logic/provider.py:255`. After the fix, `None` means exclusively "genuine UNSAT",
and inconclusive is a loud, unmissable exception. The budget then becomes a tuning parameter for
*how much of the sweep is decidable*, not a correctness-critical constant, and can be reduced to
a value that keeps the suite runnable.

**The ms/seconds conversion path is correct and is NOT implicated.** `provider.py:233` sets
`max_time = timeout_ms / 1000.0`; `structure.py:69` stores it in seconds; `structure.py:237` does
`set_timeout(int(max_time * 1000))`. The round trip is exact at every budget this codebase uses.
Do not "fix" it. Any phase that touches it is out of scope.

## Overview

`Z3OracleProvider.find_countermodel()` returns `None` for two semantically opposite outcomes. This
plan makes the two outcomes distinguishable by raising a dedicated `OracleTimeoutError` when
`structure.timeout` is true, leaving `None` to mean only "proven no countermodel"; then migrates
every caller and every test that encoded the old ambiguous contract as correct behavior. Per
CLAUDE.md's no-backwards-compatibility policy this is a clean break with no compatibility layer,
so the migration is enumerated exhaustively below and every call site is assigned to a phase.
Definition of done: the contract is three-valued at the API boundary, `bimodal-logic check` no
longer reports `{"result": "valid"}` for a solve it never completed, the complexity-5 scan asserts
zero disagreements *among conclusive results* with a measured floor on conclusiveness, and
`oracle/run-oracle-suite.sh` completes with a runtime a downstream baseline task can actually
consume.

### Research Integration

`reports/02_find-countermodel-contract.md` is authoritative and its conclusions are not
re-derived here. Load-bearing findings carried in:

- The defect is the `return None` at `provider.py:255` discarding `structure.timeout`, not the
  budget and not the unit conversion.
- The recommended fix is a dedicated exception local to `oracle/bimodal_logic/`, mirroring the
  *shape* of `Z3TimeoutError` / `IterationTimeoutError` / `ModelSolverError` without reaching
  across into `model_checker` for a class.
- `_run_differential_comparison`'s `except Exception: mc_result = "TIMEOUT"`
  (`test_cross_oracle_differential.py:414`) is dead code that has been waiting for exactly this
  exception since it was written. The `timeout_count` field in `_generate_differential_report`'s
  return value (line 1252) is likewise dead and becomes live.
- The highest-risk migration point is `_generate_differential_report`'s `reference_fn(formula_json)`
  call at line 1232, which sits **outside** any try/except. Getting this wrong regresses report
  generation from "silently wrong" to "hard crash on the first boundary formula".
- Unsupported `frame_class` returning `None` (`provider.py:203-204`) is a separate, legitimate
  "not applicable" case with three passing tests. Leave it alone.
- BimodalHarness documents the same conflation as its external protocol, but this provider is not
  entry-point-registered there (confirmed by the already-`xfail`'d `test_entry_point_registered` /
  `test_entry_point_loads_correct_class`). No live cross-repo consumer breaks. Informational only.

### Call-site inventory (verified against HEAD)

Every site below is assigned to a phase. Nothing in this table may be left unmigrated.

| Site | Location | Phase |
|---|---|---|
| The contract itself | `provider.py:255` | 1 |
| `validate_self` | `provider.py:277-295` (call at :292) | 1 |
| CLI `result is None` -> `{"result": "valid"}` | `cli.py:91-98` | 2 |
| `test_timeout_handling` (asserts `None` at `timeout_ms=1`) | `test_oracle_interface.py:1100-1106` | 3 |
| `test_deeply_nested_enriched` (`isinstance(result, (dict, type(None)))`) | `test_oracle_interface.py:841-847` | 3 |
| `if result is not None:` permissive guards | `test_oracle_interface.py:780, 996, 1011, 1030` | 3 |
| `validate_self` tests (expect `False`, may now raise) | `test_oracle_interface.py:868-944` | 3 |
| `if result is not None:` permissive guards | `test_oracle_provider.py:372, 531` | 3 |
| `ref_fn` closures `"SAT" if result is not None else "UNSAT"` | `test_cross_oracle_differential.py:1286, 1373, 1400, 1420, 1528, 1544` | 4 |
| `_run_differential_comparison` (`except Exception` becomes live) | `test_cross_oracle_differential.py:405-415` | 4 |
| `_generate_differential_report`'s uncaught `reference_fn()` | `test_cross_oracle_differential.py:1232` | 4 |
| `test_temporal_only_self_consistency` (Bucket 3, currently green, in normal CI) | `test_cross_oracle_differential.py:1495-1520` | 4 |
| `test_complexity_5_scan_self_consistent` + budget constant | `test_cross_oracle_differential.py:48-57, 1391-1412` | 5 |
| Five `xfail(strict=True)` tests rooted in this cause | `test_cross_oracle_differential.py:786, 961, 1039, 1152, 1460` | 6 |
| Bucket 1: ~45 hard `is None`/`is not None` assertions on small non-boundary formulas | `test_oracle_provider.py`, `test_soundness_regression.py`, `test_oracle_interface.py` | none — unaffected by design; regression-checked in 7 |

Note the research's "8 `ref_fn`/differential-report closures" resolves on inspection to **6**
literal `"SAT" if result is not None else "UNSAT"` closures plus `_run_differential_comparison`
and `_generate_differential_report`'s uncaught `reference_fn()` call — the same set, counted
differently. The six line numbers above are the verified list.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:

- Make `find_countermodel()` three-valued at its API boundary: countermodel dict / `None` (proven
  UNSAT) / `OracleTimeoutError` (solver did not decide).
- Fix the live user-facing CLI bug where a timed-out solve prints `{"result": "valid"}` and
  exits 0.
- Migrate every caller and every test in the inventory above, in one clean break with no
  compatibility layer.
- Make `test_complexity_5_scan_self_consistent` assert a claim that means what it says, and give
  the budget constant a value that keeps `oracle/run-oracle-suite.sh` runnable.
- Convert the five `xfail(strict=True)` tests rooted in this cause into tests that fail only on
  provable wrongness.
- Produce an exit criterion the downstream baseline task can rely on that is honest about what a
  green run does and does not prove.

**Non-Goals**:

- **Touching the ms/seconds conversion path.** Verified correct (see "Supersedes v1"). Out of
  scope.
- **Changing the `frame_class` unsupported-value `None`** at `provider.py:203-204`. Legitimate
  "not applicable", three passing tests depend on it.
- **`code/src/model_checker/jupyter/interactive.py:99`'s `find_countermodel`.** Unrelated
  function that merely shares a name. Do not touch it, and do not let a grep sweep pull it in.
- **Updating `~/Projects/BimodalHarness/docs/oracle-interface-standards.md`.** This provider is
  not entry-point-registered there; no live consumer breaks. Flagged in the research so a future
  task does not rediscover the tension.
- **Raising the *default* `timeout_ms=5000` on `find_countermodel`.** The whole point of the
  contract fix is that inconclusive results stop being silently wrong, which removes the pressure
  to widen defaults suite-wide.
- **Re-marking, fixing, or suppressing the four `xfail`'d entry-point/packaging tests.** Different
  root cause entirely.
- **Any destructive git operation** (`git checkout`/`git restore`/`git stash`/`git reset`) on the
  working tree, which carries unrelated pre-existing modifications from other sessions.

## Budget decision: reduce `SELF_SCAN_SOLVE_TIMEOUT_MS` from 60000 to 10000

**Decision: reduced to 10000 ms.** Not kept at 60000, not reverted to the 5000 ms inherited
default. This is stated here explicitly rather than left to Phase 5 to discover.

**Runtime consequence at 548 solves (274 formulas x 2):**

| Budget | Worst case (548 x budget) | Status |
|---|---|---|
| 60000 ms (v1, committed) | 9.13 hours | Rejected — suite unrunnable |
| 30000 ms | 4.57 hours | Rejected — still unrunnable in a gating suite |
| **10000 ms (this plan)** | **1.52 hours** | **Selected** |
| 5000 ms (inherited default) | 46 minutes | Rejected — inconclusive rate too high |

Worst case assumes every solve exhausts its budget; the measured expectation is lower (see
below).

**Why not keep 60000.** `oracle/run-oracle-suite.sh` pass 1 is `pytest "$repo_root/oracle" -n 6 -m
"not xdist_serial"` — it filters on `xdist_serial` only and does **not** deselect `slow`, so
`TestFullScanReport` runs inside the gating suite despite the `slow` marker's registered
description saying otherwise. A 9.1-hour worst case therefore lands on the suite that the
downstream baseline task must consume. An isolated run was killed after 56 minutes with no
output. 60000 ms is not a conservative choice; it is a suite-breaking one.

**Why not revert to 5000.** `evidence/scan_5s_partial.log` covers 45 formulas (90 solves) in 243
seconds — a 2.7 s/solve average against a 5.0 s ceiling, with the printed lines dominated by
`UNSAT(5.1s)`. Solve times are strongly bimodal (near-zero or at the ceiling), so ~50% of solves
are budget-exhausted at 5000 ms. Under the corrected contract those stop being counted as
agreements and start being counted as inconclusive, which would leave the scan reporting roughly
half its formulas as undecided. The test would technically pass while asserting almost nothing.
This is the specific degradation the conclusiveness floor in Phase 5 exists to prevent, and
setting the budget to 5000 ms would walk straight into it.

**Why 10000.** It matches an existing, deliberate precedent in this tree —
`test_oracle_interface.py:116`'s `ATEMPORAL_SOLVE_TIMEOUT_MS = 10000` — keeps the scan's worst
case inside 92 minutes, and doubles the decision window over the 5000 ms measurement. It is a
starting value, not a guess to be defended: Phase 5 measures the actual conclusive rate at 10000
ms on a bounded 30-formula sample and may move the constant within **[10000, 20000]** by the rule
stated in that phase. Above 20000 ms the plan's instruction is explicit: **do not widen further.**
Reduce the scan's enumeration or sample size instead, because past 20000 ms the worst case
(3.0 hours) re-creates the v1 problem the re-aim exists to escape.

**Do not add `@pytest.mark.xdist_serial` to `TestFullScanReport`.** The marker's registered
criterion (`oracle/conftest.py`) is "tests whose Z3 solve budget has under ~2x headroom", and
that criterion is itself a description of the defect this plan removes. Once a blown budget
raises instead of inverting a verdict, contention can no longer silently corrupt this test's
result — it can only increase the inconclusive count, which the test reports rather than fails
on. Adding the marker would move an hour of work from the parallel pass to the serial pass for
no gain.

## What `test_complexity_5_scan_self_consistent` must assert

The two claims are distinct and the test must not conflate them:

- **"Zero disagreements among conclusive results"** — the soundness claim. Both solves of a
  formula completed, and they returned opposite verdicts. This is a real bug and the test **must
  fail** on it, unconditionally, with no tolerance.
- **"Zero inconclusive results"** — a *performance* claim about the solve budget, not a soundness
  claim. Two independent solves of a formula sitting near the wall-clock boundary can legitimately
  land on opposite sides of "finished" vs. "didn't finish" under machine-load jitter without
  either solve being wrong. The test **must not** fail on this.

The required assertion shape:

1. Classify each formula by running both solves and catching `OracleTimeoutError` on **each side
   independently**:
   - `agree` — both sides conclusive and matching.
   - `disagree` — both sides conclusive and mismatched.
   - `inconclusive` — either side raised.
2. `assert report["disagreements"] == 0` — the unchanged assertion target, now over a
   well-defined, non-ambiguous category.
3. `assert conclusive_count >= MIN_CONCLUSIVE_SCAN_FORMULAS` — a **floor**, not a ceiling on
   inconclusives, expressed as an absolute formula count so the failure message is readable. This
   exists so the test cannot silently degrade into "everything was inconclusive, therefore zero
   disagreements, therefore pass" if a future change starves the budget. Its value is set from
   Phase 5's measurement, not guessed, and its definition comment must say that a drop below the
   floor is a budget/performance regression to investigate — not a semantic one.
4. Always emit `agreements` / `disagreements` / `timeout_count` to the test output regardless of
   pass or fail, so the conclusive rate is observable from a green run and not only from a red one.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The tree is intentionally RED between Phase 1 and Phase 4 — a clean break with no compatibility layer means callers break the moment the contract changes. A phase could be misread as failing. | H | H if unstated | Phase 1 names exactly which tests are expected to fail in the interim and why. Each phase's verification is scoped to what that phase fixed plus a named regression check, never to the whole suite. Commit at every green sub-step per `.claude/rules/git-workflow.md`. |
| `_generate_differential_report`'s `reference_fn()` call at line 1232 is left unguarded, so the first boundary formula crashes report generation instead of being classified. | H | M | Phase 4 makes this its primary objective and verifies it with a stub oracle that raises deterministically — no Z3, no wall-clock dependence, so the guard is proven in milliseconds rather than inferred from a long run. |
| Verification of the fix depends on a multi-hour scan, so phases cannot be proven and the plan stalls exactly as v1 did. | H | M | Phases 1-6 are provable in minutes, using either small formulas or a Z3-free stub oracle. Only Phase 7 runs long, in background, with a hard abort rule and a stated fallback. No phase's success criterion is "the full scan passed". |
| `validate_self` propagating the exception turns two currently-green tests into errors, because it calls `find_countermodel` at the default 5000 ms where ~50% of solves are budget-exhausted. | M | M | Anticipated, not discovered: Phase 3 owns those two tests explicitly and states both the expected outcome and the fallback (widen the budget those tests pass, or assert `pytest.raises`). |
| 10000 ms turns out to leave too much of the sweep inconclusive. | M | M | Phase 5 measures before committing to the floor value, and states the escalation rule and its hard ceiling (20000 ms) in advance so the next agent does not re-litigate it. |
| A single green run in Phase 7 is over-read as proof the disagreement count is stably zero. | M | H if unstated | The exit criterion in Phase 7 states in required verbatim language what the green run does and does not prove, and what would actually prove it. |
| Long commands are cut off by the 10-minute foreground Bash ceiling and misread as failures. | M | H if ignored | Every command expected to exceed 10 minutes MUST use `run_in_background: true`. A cut-off foreground command is a harness limit, not a test failure. |

## Environment contract (applies to every command in every phase)

Verified constraints, not suggestions:

- **Every python/pytest invocation MUST be wrapped in `nix develop --command ...`.** `pytest-xdist`
  is absent from the bare interactive python but present in the devShell, which also supplies
  pytest and z3.
- **`PYTHONPATH=code/src` is required.**
- **`run_in_background: true` is mandatory** for any command expected to exceed 10 minutes —
  in this plan, the Phase 5 calibration run and everything in Phase 7.
- The two-pass runner is `oracle/run-oracle-suite.sh`. It assumes it is already inside the
  devShell and does not invoke `nix develop` itself.
- Before launching a long timing-sensitive run, check for competing pytest processes
  (`ps aux | grep pytest`) per `code/docs/core/TESTING_GUIDE.md` section 8.6 — concurrent sessions
  measurably contend.
- **Files under `oracle/` and `code/` are deliverables, not specs artifacts.** Per
  `.claude/rules/no-task-references-in-deliverables.md`, no comment, docstring, or `reason=`
  string written into them may cite a task number. Cite durable anchors instead:
  `code/docs/core/TESTING_GUIDE.md` section 8.6, `provider.py:255`, or the behavior itself. Note
  that several existing `reason=` strings in `test_cross_oracle_differential.py` already violate
  this ("Root-caused (task 122): ..."); Phase 6 rewrites five of them and must not reproduce the
  citation style.
- **Mandatory TDD** per `code/docs/core/TESTING_GUIDE.md`: every phase that changes behavior
  writes the failing test first, observes it fail for the expected reason, then implements. A
  phase that implements before its test has not followed the process even if the end state matches.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 1 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 2, 3, 6 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint files
(`cli.py`/`test_cli.py` vs. `test_oracle_interface.py`/`test_oracle_provider.py`) and may run
concurrently. Phases 4, 5, and 6 all touch `test_cross_oracle_differential.py` and MUST be
sequential — that file is a single territory owned by one agent at a time.

---

### Phase 1: Raise on timeout instead of returning None [COMPLETED]

**Goal**: `find_countermodel()` distinguishes "solver did not decide" from "proven no
countermodel". `None` acquires a single, unambiguous meaning.

**Tasks**:

- [x] **RED first.** Add a test to `oracle/bimodal_logic/tests/test_oracle_provider.py`, in
      `TestFindCountermodelContract`, asserting that a deeply nested temporal formula at
      `timeout_ms=1` raises the new exception:
      `with pytest.raises(OracleTimeoutError): self.provider.find_countermodel(complex_formula, timeout_ms=1)`.
      Run it and confirm it fails with `Failed: DID NOT RAISE` — not with an `ImportError`. Write
      the import against the intended public path so the failure is about behavior, not wiring.
      **Deviation (sequencing only, not scope)**: to make the RED failure be `DID NOT RAISE`
      rather than `ImportError` as the plan requires, `errors.py` and the `__init__.py` export
      (the next two bullets) were created *before* writing the test — the import needs to resolve
      for "DID NOT RAISE" to be the observed failure. `provider.py` was edited only after RED was
      confirmed. All three bullets' content is unchanged from what is written below.
- [x] Create `oracle/bimodal_logic/errors.py` with a single class `OracleTimeoutError(Exception)`.
      Mirror the *shape* of `code/src/model_checker/theory_lib/errors.py:230`'s `Z3TimeoutError`:
      a formatted message plus a `context` dict carrying at minimum `timeout_ms`, `temporal_depth`,
      and `M`, and a `suggestion` string. Do **not** import or subclass `Z3TimeoutError` — this
      package ships no packaging metadata and must not acquire a cross-package dependency for a
      one-off signal.
- [x] Export it from `oracle/bimodal_logic/__init__.py`: add to the `from .errors import ...` line
      and to `__all__`.
- [x] **GREEN.** At `provider.py:254-257`, split the merged branch:
      ```python
      if structure.timeout:
          self._semantics = None
          raise OracleTimeoutError(...)   # inconclusive: solver did not decide
      if not structure.z3_model_status:
          self._semantics = None
          return None                      # unchanged: genuine UNSAT / valid formula
      ```
      The existing `finally: self._semantics = None` already covers the raise path; confirm the
      explicit assignment before `raise` is redundant-but-harmless rather than removing it, so the
      two branches read symmetrically.
- [x] Update `find_countermodel`'s docstring: the `Returns:` section must state that `None` means
      exclusively "the formula is valid (proven no countermodel)" or "unsupported frame class",
      and add a `Raises:` section for `OracleTimeoutError`.
- [x] **Decide `validate_self`: propagate, do not catch.** A spot check that cannot obtain a
      verdict is a tooling problem, not evidence the oracle is unsound, and silently returning
      `False` for it re-creates the exact conflation this phase removes one layer up. Leave
      `provider.py:291-295` structurally as-is (the exception propagates through the loop) and
      update its docstring with a `Raises:` section stating that an undecided spot check
      propagates rather than counting as a failure.
- [x] Verify no task-number citation was introduced into any file under `oracle/`.

**Timing**: 1 hour.

**Depends on**: none

**Files to modify**:

- `oracle/bimodal_logic/errors.py` (new)
- `oracle/bimodal_logic/__init__.py`
- `oracle/bimodal_logic/provider.py`
- `oracle/bimodal_logic/tests/test_oracle_provider.py`

**Expected RED elsewhere after this phase** (state this in the commit message so a later reader
does not mistake it for breakage): `test_oracle_interface.py::test_timeout_handling`,
`test_oracle_interface.py::test_deeply_nested_enriched`, the two `validate_self` tests, and any
CLI or differential test whose formula exhausts its budget. These are migrated in Phases 2-4.

**Verification** (fast — all formulas are small or fail in 1 ms):

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_oracle_provider.py::TestFindCountermodelContract \
  oracle/bimodal_logic/tests/test_oracle_provider.py::TestValidateSelf -q'
```

- Success criterion: exit 0. The new `pytest.raises` test passes; the ~20 existing Bucket 1
  assertions on `SIMPLE_SAT_JSON` / `SIMPLE_UNSAT_JSON` / tautologies still pass unchanged —
  that is the evidence that `None`'s meaning was narrowed, not broken.
- Import check: `nix develop --command bash -c 'PYTHONPATH=code/src python -c "from bimodal_logic import OracleTimeoutError; print(OracleTimeoutError)"'`
- `grep -rn "task [0-9]" oracle/bimodal_logic/errors.py oracle/bimodal_logic/provider.py` returns
  no new matches.

---

### Phase 2: Fix the live CLI correctness bug [NOT STARTED]

**Goal**: `bimodal-logic check` stops claiming a formula is valid when the solver never decided it.

**Tasks**:

- [ ] **RED first.** Add tests to `oracle/bimodal_logic/tests/test_cli.py` (a new
      `TestCLIInconclusive` class alongside the existing `TestCLIValidFormula` /
      `TestCLIInvalidFormula`) asserting that
      `main(["check", <deeply nested temporal formula JSON>, "--timeout", "1"])` (a) exits with
      code **2**, and (b) prints JSON whose `"result"` is `"inconclusive"`. Run and confirm both
      fail — today the call exits 0 with `{"result": "valid", "countermodel": null}`.
- [ ] **GREEN.** In `cli.py`, wrap the `provider.find_countermodel(...)` call at lines 91-95 in
      `try/except OracleTimeoutError`, emitting `{"result": "inconclusive", "countermodel": None}`
      and `sys.exit(2)`. Exit code 2 is chosen because 1 is already taken by argument/JSON/frame-class
      errors — a script consuming this CLI must be able to distinguish "we don't know" from both
      "valid" and "your input was bad".
- [ ] Update the module docstring's `Output format` and `Exit codes` blocks (lines 11-17) to
      document the third result value and exit code 2.
- [ ] Check the existing `test_result_is_string` assertion at `test_cli.py:223`
      (`output["result"] in ("valid", "invalid")`) and widen it to include `"inconclusive"`. It
      currently encodes the two-valued contract.

**Timing**: 45 minutes.

**Depends on**: 1

**Files to modify**:

- `oracle/bimodal_logic/cli.py`
- `oracle/bimodal_logic/tests/test_cli.py`

**Verification** (fast — the CLI tests use tiny formulas and a 1 ms timeout):

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cli.py -q'
```

- Success criterion: exit 0, zero failures, and the new inconclusive tests present in the count.
- Manual confirmation that the user-facing bug is gone:
  ```bash
  nix develop --command bash -c 'PYTHONPATH=code/src python -m bimodal_logic.cli check "{\"tag\": \"atom\", \"name\": \"A\"}" --timeout 1; echo "exit=$?"'
  ```
  Expect `{"result": "inconclusive", ...}` and `exit=2`, not `{"result": "valid", ...}` and `exit=0`.

---

### Phase 3: Migrate the interface and provider test suites [NOT STARTED]

**Goal**: Every test that encoded the old ambiguous contract as correct behavior now encodes the
new one, and the permissive `if result is not None:` guards stop masking genuine failures.

**Tasks**:

- [ ] `test_oracle_interface.py:1100-1106` `test_timeout_handling` — currently asserts
      `result is None` for `timeout_ms=1`, i.e. it tests that a timeout looks like a valid formula.
      Rewrite to `with pytest.raises(OracleTimeoutError):` and rename the docstring accordingly.
      This is the single clearest case of the old contract being asserted as correct.
- [ ] `test_oracle_interface.py:841-847` `test_deeply_nested_enriched` — `isinstance(result, (dict,
      type(None)))`, explicitly "just ensure no crash". Wrap in `try/except OracleTimeoutError` and
      accept the exception as a third valid outcome, so a genuinely inconclusive solve does not
      crash the test.
- [ ] `test_oracle_interface.py:780, 996, 1011, 1030` — four `if result is not None:` guards
      (`test_boundary_safe_true_for_all_examples`, `test_time_bound_formula`,
      `test_temporal_depth_correct_in_output`, and the sibling at 780). Replace each with an
      explicit `try/except OracleTimeoutError: continue` around the call, so that a timeout is
      skipped-and-noted (matching each docstring's stated intent, e.g. "for all active
      (non-timeout) SAT examples") while a `None` returned for a formula the test believes is SAT
      becomes a **loud failure** instead of a silent no-op. This is a latent-bug-detection
      improvement, not busywork: today these guards cannot tell the two apart.
- [ ] `test_oracle_provider.py:372, 531` — same permissive pattern in
      `test_folded_json_for_enriched_input` and `test_boundary_safe_consistency`. Same treatment.
      Low risk (small formulas) but migrate for consistency and to stop masking.
- [ ] `test_oracle_interface.py:868-944` — `test_validate_self_temporal_only` and
      `test_validate_self_all_formulas` both expect `False` and both call through to the default
      5000 ms budget, where roughly half of solves are budget-exhausted. Run them first and record
      what actually happens. If either now raises `OracleTimeoutError`, that is correct behavior
      under the Phase 1 decision, and the fix is to give the spot-check formulas an explicit wider
      budget so the test measures what its docstring claims (validity, not solver speed) — the
      docstrings name specific formulas F4/F7/F9/F10 as genuinely valid, and that claim must remain
      testable. Do **not** "fix" it by catching the exception and returning to a `False` assertion;
      that re-introduces the conflation at the test layer.
- [ ] Leave the ~45 Bucket 1 assertions untouched. They are unaffected by design.

**Timing**: 1 hour 15 minutes.

**Depends on**: 1

**Files to modify**:

- `oracle/bimodal_logic/tests/test_oracle_interface.py`
- `oracle/bimodal_logic/tests/test_oracle_provider.py`

**Verification** (node-id-scoped — `test_oracle_interface.py` as a whole carries a 180000 ms
`TEMPORAL_SOLVE_TIMEOUT_MS` and must not be run wholesale here):

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest \
  "oracle/bimodal_logic/tests/test_oracle_interface.py::TestErrorHandling" \
  "oracle/bimodal_logic/tests/test_oracle_interface.py::TestValidateSelfBehavior" \
  oracle/bimodal_logic/tests/test_oracle_provider.py -q'
```

(Resolve the exact class names by grepping for the enclosing `class` of lines 841, 1100, and 868
before running; the node ids above are indicative.)

- Success criterion: exit 0. If any command approaches the 10-minute foreground ceiling, re-run it
  with `run_in_background: true` — a cut-off command is not a failure.
- `grep -n "isinstance(result, (dict, type(None)))" oracle/bimodal_logic/tests/test_oracle_interface.py`
  returns nothing.
- `grep -c "if result is not None" oracle/bimodal_logic/tests/test_oracle_interface.py oracle/bimodal_logic/tests/test_oracle_provider.py`
  returns 0 for both.

---

### Phase 4: Make the differential harness three-valued [NOT STARTED]

**Goal**: Every path that turns a `find_countermodel` call into a `"SAT"`/`"UNSAT"` string handles
the third outcome, and `_generate_differential_report` classifies inconclusive results instead of
crashing on them. `timeout_count` becomes live.

**Tasks**:

- [ ] **RED first, with a stub oracle — no Z3.** Add a module-level test stub to
      `test_cross_oracle_differential.py`, e.g. a `_StubOracle` class whose `find_countermodel`
      returns a dict, returns `None`, or raises `OracleTimeoutError` according to the formula it is
      given. Add tests asserting that a report generated over three stub formulas yields exactly
      one `agreement`, one `disagreement`, and one `timeout_count`, and that
      `agreements + disagreements + timeout_count == total_formulas`. These run in milliseconds and
      are the mechanism by which every later phase is verified without a long scan. Confirm they
      fail today — the raising formula currently crashes report generation.
- [ ] Introduce a shared three-valued reference helper next to `_run_differential_comparison`:
      ```python
      def _reference_verdict(oracle, formula_json, timeout_ms=None) -> str:
          """Return "SAT", "UNSAT", or "TIMEOUT" for one reference-side solve."""
      ```
      It performs the same `try/except OracleTimeoutError` classification
      `_run_differential_comparison` already performs on the subject side. Every `ref_fn` closure
      becomes a one-line delegation to it.
- [ ] **The highest-risk change**: guard `_generate_differential_report`'s
      `ref_result = reference_fn(formula_json)` at line 1232 with `try/except OracleTimeoutError:
      ref_result = "TIMEOUT"`. A caller-supplied closure that does not classify internally must
      still produce a `"TIMEOUT"` entry rather than crashing the whole report. This guard is
      belt-and-braces on top of the closures below, and both are required — the closures make the
      common path informative, the guard makes the uncommon path survivable.
- [ ] Update the report's counting logic (lines 1238-1243) so a formula counts as
      `timeout_count` when **either** side is `"TIMEOUT"`, not only the subject side. Today the
      `elif record["agreement"]` branch would score a `TIMEOUT` reference against a `SAT` subject
      as a *disagreement*, which would turn every inconclusive formula into a false soundness
      alarm — the exact inversion of the bug being fixed.
- [ ] Migrate all six `"SAT" if result is not None else "UNSAT"` closures at lines **1286, 1373,
      1400, 1420, 1528, 1544** to delegate to `_reference_verdict`. Verify the count with grep
      afterwards.
- [ ] Migrate `test_temporal_only_self_consistency` (lines 1495-1520, Bucket 3). It runs in
      **normal CI** (`TestCIGate`'s docstring), is currently green, is not `xfail`'d, and is
      structurally identical to the complexity-5 scan — two independent solves of the same formula
      compared via `result is not None`. Wrap both calls, classify each side, and compare only when
      both are conclusive; count and report the inconclusive formulas without failing on them.
      Without this, the test begins crashing (correctly, but uninformatively) the moment the
      contract changes.
- [ ] Update the docstrings of `_run_differential_comparison` and `_generate_differential_report`
      to state that `"TIMEOUT"` is now reachable and what produces it.

**Timing**: 1 hour 30 minutes.

**Depends on**: 1

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`

**Verification** (the stub tests are instant; the three named classes use small formulas):

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate -q'
```

- Success criterion: exit 0, including the new stub-oracle classification tests, and
  `test_temporal_only_self_consistency` passing under the new classification.
- No unmigrated closures remain:
  ```bash
  grep -c 'is not None else "UNSAT"' oracle/bimodal_logic/tests/test_cross_oracle_differential.py
  ```
  must return `0`.
- `grep -n "_reference_verdict" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  returns the definition plus at least six call sites.

---

### Phase 5: Reduce the budget and rewrite the scan's assertion [NOT STARTED]

**Goal**: `test_complexity_5_scan_self_consistent` asserts zero disagreements among conclusive
results with a measured floor on conclusiveness, at a budget that keeps the gating suite runnable.

**Tasks**:

- [ ] **Calibrate before choosing the floor.** Run the existing instrumented harness on a bounded
      sample at the new budget, **with `run_in_background: true`** (bounded by construction to
      ~10 minutes at 30 formulas x 2 solves x 10 s worst case):
      ```bash
      nix develop --command bash -c 'PYTHONPATH=code/src python \
        specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_instrumented.py \
        --timeout-ms 10000 --limit 30 \
        --out specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl'
      ```
      Record the conclusive rate (formulas where neither solve hit the ceiling) and the wall clock.
      Note that this script predates the contract fix and classifies by elapsed time and exception;
      after Phase 1 its `except Exception -> "TIMEOUT"` branch becomes live, so its `T=` counter
      finally reports real numbers. That is itself a useful confirmation the fix works end to end.
- [ ] **Escalation rule, stated in advance so it is not re-litigated.** If the measured conclusive
      rate at 10000 ms is below **60%** of the sample, raise `SELF_SCAN_SOLVE_TIMEOUT_MS` to
      15000 and re-measure once; if still below 60%, raise to 20000 and re-measure once.
      **20000 ms is a hard ceiling** — at 548 solves its worst case is 3.0 hours, which re-creates
      the problem this re-aim exists to escape. If 20000 ms still leaves the sweep majority-
      inconclusive, do **not** widen further: record the measurement, set the floor from what was
      actually achieved, and note in the summary that the complexity-5 sweep is largely undecidable
      at any suite-compatible budget — which is a finding about the semantics' solve cost, not a
      failure of this task.
- [ ] Change `SELF_SCAN_SOLVE_TIMEOUT_MS` from `60000` to the calibrated value (default 10000) at
      `test_cross_oracle_differential.py:57`. **Rewrite its comment block (lines 48-56) entirely.**
      The existing comment argues for a 12x margin on the premise that a blown budget is reported
      as "no countermodel" — that premise is exactly what Phase 1 removed, so leaving the comment
      would leave a false rationale in the tree. The new comment must state: a blown budget now
      raises rather than inverting a verdict, so this budget controls only how much of the sweep is
      decidable; it must record the measured conclusive rate and the 548-solve worst case; and it
      must cite `code/docs/core/TESTING_GUIDE.md` section 8.6 as the durable anchor. **No task
      number.**
- [ ] Add `MIN_CONCLUSIVE_SCAN_FORMULAS` as a module-level constant beside it, set from the
      calibration measurement (conservatively: floor the measured rate to a round number and apply
      it to 274). Its comment must state that a drop below this floor is a budget/performance
      regression to investigate, **not** a semantic regression — the distinction the previous four
      triage efforts kept losing.
- [ ] **RED first.** Extend the Phase 4 stub-oracle tests with two cases pinned to the new
      assertion: (a) a stub producing one genuine disagreement among otherwise conclusive results
      must fail the assertion; (b) a stub producing only inconclusive results must fail on the
      conclusiveness floor, **not** pass vacuously. These prove the assertion has both teeth and
      the right teeth, in milliseconds, without touching Z3. Confirm they fail against the current
      assertion first.
- [ ] **GREEN.** Rewrite `test_complexity_5_scan_self_consistent` (lines 1391-1412) to the four-part
      shape in "What `test_complexity_5_scan_self_consistent` must assert" above: `ref_fn`
      delegates to `_reference_verdict` with the budget; `assert report["disagreements"] == 0` with
      a message naming the disagreeing formulas; `assert conclusive >= MIN_CONCLUSIVE_SCAN_FORMULAS`
      with a message that names it a budget regression; and an unconditional print of all three
      counts so a green run is still informative.
- [ ] Update the docstring to state the two distinct claims and which one the test fails on.

**Timing**: 1 hour 15 minutes attended, plus up to 30 minutes of bounded background calibration.

**Depends on**: 4

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl` (new
  measurement record; under `specs/**`, so task references are permitted there)

**Verification** (fast — the assertion's behavior is proven by stubs, never by the full scan):

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  -q -k "stub or classif or conclusive"'
```

- Success criterion: exit 0, with both new pinned cases present.
- The budget was actually reduced:
  ```bash
  grep -n "SELF_SCAN_SOLVE_TIMEOUT_MS\|MIN_CONCLUSIVE_SCAN_FORMULAS" \
    oracle/bimodal_logic/tests/test_cross_oracle_differential.py
  ```
  must show the new value (not 60000) at the definition plus its uses in `ref_fn` and the report
  call, and the floor constant defined and used.
- The stale rationale is gone: `grep -n "12x margin" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  returns nothing.
- **Do not run the full scan in this phase.** Its result is a Phase 7 concern.

---

### Phase 6: Rewrite the five xfail(strict=True) tests rooted in this cause [NOT STARTED]

**Goal**: Five tests that are permanently expected to fail become tests that fail only when
something is provably wrong.

**Tasks**:

- [ ] The five are at `test_cross_oracle_differential.py:786` (`test_known_invalid_return_countermodel`),
      `:961` (`test_temporal_only_agreement_complexity_3`), `:1039`
      (`test_temporal_only_agreement_complexity_5`), `:1152` (`test_spot_check_all`), and `:1460`
      (`test_oracle_baseline_agreement`). Each `reason=` string already names this root cause. Note
      that the three in the BimodalHarness-dependent classes skip entirely when BH is absent from
      the path, so a local green run may not exercise them — record which ones actually ran.
- [ ] For each, rewrite the per-formula loop to bucket results into **`resolved-and-wrong`** (the
      solver decided and the decision contradicts the baseline — a real soundness bug) and
      **`inconclusive`** (the solver did not decide). Assert only on `resolved-and-wrong`; report
      the `inconclusive` count in the assertion message and via an unconditional print, without
      failing on it.
- [ ] Remove the `@pytest.mark.xfail(strict=True)` decorator from every test that now passes. If a
      test still fails on `resolved-and-wrong` results, that is a genuine soundness finding: leave
      its `xfail` in place, **rewrite the `reason=` to describe the actual remaining failure**
      (resolved-and-wrong formulas, with counts), and record it in the summary as a real defect
      surfaced by the contract fix rather than a known-flaky marker. Do not leave a `reason=` that
      blames timeout conflation once timeout conflation no longer exists.
- [ ] **Rewrite the `reason=` strings without task-number citations.** The existing five all begin
      "Root-caused (task 122): ...", which violates
      `.claude/rules/no-task-references-in-deliverables.md`. Replace with durable anchors:
      `provider.py:255`, `code/docs/core/TESTING_GUIDE.md` section 8.6, or the observable behavior.
      Do not cite `specs/` paths from inside `oracle/` either.
- [ ] Leave the four `xfail`'d entry-point/packaging tests in `test_oracle_interface.py` alone.
      Different root cause.

**Timing**: 1 hour 15 minutes.

**Depends on**: 5

**Files to modify**:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`

**Verification**:

```bash
nix develop --command bash -c 'PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py \
  -q -m "not slow" -rxX'
```

- Success criterion: exit 0. `-rxX` makes the xfail/xpass disposition explicit in the output — the
  point of this phase is that the xfail count drops, so it must be readable. Record the before and
  after counts.
- **An `XPASS` under `strict=True` is a failure**, so any test left `xfail`'d that now passes will
  surface here rather than silently. That is the intended safety net.
- No task-number citations remain in the rewritten strings:
  ```bash
  grep -n "task [0-9]" oracle/bimodal_logic/tests/test_cross_oracle_differential.py
  ```
  must return nothing for the five rewritten `reason=` blocks.
- The `slow` scan is deselected here by `-m "not slow"`; it is verified in Phase 7.

---

### Phase 7: Full-suite verification and the downstream exit criterion [NOT STARTED]

**Goal**: Produce the result the downstream regression-baseline task needs, and state precisely
what it does and does not prove.

**Tasks**:

- [ ] Check for competing pytest processes (`ps aux | grep pytest`) before launching, per
      `code/docs/core/TESTING_GUIDE.md` section 8.6.
- [ ] Run the scan alone first, **with `run_in_background: true`**, so that a failure is
      attributable before the whole suite is committed to:
      ```bash
      nix develop --command bash -c 'PYTHONPATH=code/src pytest \
        "oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent" \
        -q -s --durations=0'
      ```
      `-s` is required so the unconditional count print reaches the log. Record the exit status,
      the duration, and the three counts.
- [ ] **Abort rule**: if this run exceeds **90 minutes** of wall clock, stop it, record the partial
      evidence, and apply the Phase 5 escalation ladder in reverse (reduce the budget one step)
      rather than waiting it out. Do not raise it. The v1 failure mode was waiting on a run that
      never emitted anything.
- [ ] Run the full two-pass suite, **with `run_in_background: true`**:
      ```bash
      nix develop --command bash oracle/run-oracle-suite.sh
      ```
      Record, from the script's own `== oracle suite summary ==` block: pass 1 status, pass 2
      status, overall exit code, and total wall clock.
- [ ] If any test *other* than the ones this plan migrated fails, report it with its node id and
      output and stop. Fixing it is out of scope.
- [ ] Write the exit criterion below into the implementation summary verbatim.

**Timing**: 45 minutes attended; ~2-2.5 hours unattended background wall clock.

**Depends on**: 2, 3, 6

**Files to modify**: none (verification only), unless the abort rule fires, in which case
`SELF_SCAN_SOLVE_TIMEOUT_MS` moves one step down.

**Verification**:

- Success criterion: `oracle/run-oracle-suite.sh` exits 0 with
  `pass 1 (parallel, -n 6, not xdist_serial): PASSED` and
  `pass 2 (serial, xdist_serial):             PASSED`.
- Recorded: total suite wall clock, and the scan's `agreements`/`disagreements`/`timeout_count`.

## Exit criterion for the downstream regression-baseline task

Task 127 needs a trustworthy green baseline from this suite, and task 126 waits on 127. State the
following verbatim in the implementation summary.

**Necessary and sufficient to unblock 127**: one complete `oracle/run-oracle-suite.sh` invocation
in which both passes report PASSED and the script exits 0, **with the scan's recorded
`disagreements` and `timeout_count` captured alongside it**. The counts are part of the deliverable,
not commentary — a green run whose counts were not recorded does not satisfy this criterion,
because without them the baseline cannot distinguish "the sweep agreed" from "the sweep was
undecided".

**What that green run proves**: at that moment, under that machine's load, no formula in the
complexity-5 sweep produced two *conclusive* solves that contradicted each other, and no other
test in the oracle suite failed. Because a budget-exhausted solve now raises instead of returning
`None`, an agreement in that run is a real agreement — which was not true of any previous green
run of this suite.

**What it does not prove**: that the disagreement count is stably zero across runs. Disagreements
were intermittent and load-dependent before the fix, and the fix removes the *silent* failure
mode, not the underlying wall-clock variance. Any formula whose two solves land on opposite sides
of the budget is now counted as inconclusive rather than as a disagreement — correct, but it means
a green run bounds the disagreement rate only over the conclusive subset.

**What would actually prove stability**: N independent full-scan runs under varying load with the
disagreement count zero in all N and the conclusive count stable within a stated tolerance. At
roughly an hour per run this is several hours of unattended wall clock and is deliberately not in
this plan's scope. If 127 needs a stability estimate rather than a single verdict, that is separate,
explicitly budgeted work — and it is now *worth* doing, which it was not before, because the count
being measured finally means something.

**Annotation the promoted baseline must carry**: record the calibrated
`SELF_SCAN_SOLVE_TIMEOUT_MS` value and the `MIN_CONCLUSIVE_SCAN_FORMULAS` floor alongside the
result. Record that a future failure of `test_complexity_5_scan_self_consistent` on the
*conclusiveness floor* is a budget/performance regression, while a failure on *disagreements* is a
semantic regression — these have different causes and different fixes, and conflating them is what
consumed four consecutive triage efforts in this line of work.

## Testing & Validation

- [ ] `pytest oracle/bimodal_logic/tests/test_oracle_provider.py::TestFindCountermodelContract
      ::TestValidateSelf` exits 0, including the new `pytest.raises(OracleTimeoutError)` test.
- [ ] `from bimodal_logic import OracleTimeoutError` succeeds.
- [ ] `pytest oracle/bimodal_logic/tests/test_cli.py` exits 0; manual CLI invocation with
      `--timeout 1` emits `{"result": "inconclusive", ...}` and exit code 2.
- [ ] `grep -c "if result is not None"` returns 0 for `test_oracle_interface.py` and
      `test_oracle_provider.py`.
- [ ] `grep -c 'is not None else "UNSAT"'` returns 0 for `test_cross_oracle_differential.py`.
- [ ] Stub-oracle classification tests pass, covering all three outcomes, the count invariant, a
      seeded disagreement failing the assertion, and an all-inconclusive report failing the
      conclusiveness floor rather than passing vacuously.
- [ ] `pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow" -rxX`
      exits 0 with a reduced xfail count and no `XPASS`.
- [ ] `grep -n "task [0-9]"` returns nothing new under `oracle/` (`no-task-references-in-deliverables`).
- [ ] `grep -n "12x margin"` returns nothing in `test_cross_oracle_differential.py`.
- [ ] Calibration measurement recorded in `evidence/scan_10s_sample.jsonl` with the conclusive rate
      stated in the summary.
- [ ] Full scan in isolation exits 0 within the 90-minute abort ceiling, with all three counts
      recorded.
- [ ] `oracle/run-oracle-suite.sh` exits 0 with both passes PASSED, total wall clock recorded.

## Artifacts & Outputs

- `oracle/bimodal_logic/errors.py` — new, `OracleTimeoutError`.
- `oracle/bimodal_logic/__init__.py` — exports the new exception.
- `oracle/bimodal_logic/provider.py` — the contract split at line 255; `find_countermodel` and
  `validate_self` docstrings updated with `Raises:` sections.
- `oracle/bimodal_logic/cli.py` — inconclusive result and exit code 2; docstring exit-code table.
- `oracle/bimodal_logic/tests/test_cli.py` — new inconclusive tests; widened result-enum assertion.
- `oracle/bimodal_logic/tests/test_oracle_provider.py` — new `pytest.raises` contract test; two
  permissive guards migrated.
- `oracle/bimodal_logic/tests/test_oracle_interface.py` — `test_timeout_handling` inverted;
  `test_deeply_nested_enriched` and four permissive guards migrated; two `validate_self` tests
  reconciled.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — `_reference_verdict` helper;
  six closures migrated; `reference_fn` guarded; either-side timeout counting; stub-oracle tests;
  `test_temporal_only_self_consistency` migrated; budget reduced to the calibrated value with a
  rewritten rationale; `MIN_CONCLUSIVE_SCAN_FORMULAS` floor; scan assertion rewritten; five
  `xfail(strict=True)` tests rewritten.
- `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl` —
  calibration measurement.
- `specs/133_fix_oracle_self_consistency_disagreements/summaries/02_find-countermodel-contract-summary.md`
  — implementation summary carrying the calibrated budget, the measured conclusive rate, the scan
  counts, the suite verdict, the exit criterion verbatim, and the before/after xfail counts.

## Rollback/Contingency

- The change is a clean break with no compatibility layer, by policy. Rolling back means reverting
  the contract split at `provider.py:255` and every migrated call site together — a partial
  rollback leaves the tree in the intentionally-RED intermediate state and is worse than either
  end. Roll back whole phases, in reverse order, or not at all.
- If the contract fix lands but the scan cannot be made runnable at any budget at or below the
  20000 ms ceiling, that does **not** justify reverting Phase 1. The contract fix stands on its own
  — it fixes a live user-facing CLI bug and makes every other test in the suite honest. The
  fallback is to reduce the scan's enumeration (complexity<=4, or a fixed sample of the 274) and
  record the reduced coverage in the baseline annotation, not to restore the ambiguous contract.
- If `SELF_SCAN_SOLVE_TIMEOUT_MS` needs to move after Phase 5, it is a one-line constant change
  plus a comment update; the assertion logic is independent of its value and is verified by stubs.
- **No destructive git operations.** The working tree carries unrelated pre-existing modifications
  and another session holds a lock on
  `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`. Do not run
  `git checkout`, `git restore`, `git stash`, or `git reset` to undo anything in this task; revert
  by editing the files listed above.
- `plans/01_oracle-self-consistency.md` stays on disk as the superseded record. Do not delete it as
  part of any rollback.
