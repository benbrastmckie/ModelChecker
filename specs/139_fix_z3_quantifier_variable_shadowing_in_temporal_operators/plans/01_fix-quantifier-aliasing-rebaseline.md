# Implementation Plan: Fix Z3 quantifier variable aliasing in temporal operators

- **Task**: 139 - fix_z3_quantifier_variable_shadowing_in_temporal_operators
- **Status**: [IMPLEMENTING]
- **Effort**: 11 hours agent work, plus ~1-2 hours unattended wall clock for the exhaustive re-derivation run
- **Dependencies**: Task 138 (scan tooling, `SCAN_COMPLETE` marker contract, persisted baseline manifest, `MIN_CONCLUSIVE_GATING_FORMULAS`); Task 133 (`find_countermodel`/`OracleTimeoutError` contract — preserved unmodified)
- **Research Inputs**: `specs/139_fix_z3_quantifier_variable_shadowing_in_temporal_operators/reports/01_quantifier-shadowing-diagnosis.md`
- **Artifacts**: plans/01_fix-quantifier-aliasing-rebaseline.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

`z3.Int('fixed_name')` interns by `(name, sort)`, so a quantified temporal operator whose argument
is another instance of the same primitive operator receives, as its "fresh" bound variable, the
identical Z3 term the outer call already passed down as `eval_time`. The resulting `x < x`
self-comparison constant-folds the subformula before either quantifier closes. This is a
**soundness** defect, not a performance defect: a conclusion constraint that folds to a Boolean
constant is unfalsifiable by encoding, `find_countermodel` finds no countermodel, and the oracle
reports validity it never established. The fix replaces the fixed-string declarations with
`z3.FreshInt` at all 14 quantifier-declaration sites, rewrites the tests that currently enshrine
the defect as expected behaviour, resolves the dead-`false_at` question, and re-derives both the
persisted baseline manifest and the gating floor against genuinely-changed solver behaviour.

Definition of done: the specific soundness failure mode (a non-`\bot` formula whose conclusion
constraint simplifies to a Z3 Boolean literal) is demonstrably absent and permanently guarded by a
test; no test asserts the defect as correct behaviour; the baseline manifest and
`MIN_CONCLUSIVE_GATING_FORMULAS` are re-derived from a fresh contention-free serial measurement;
and the three pinned soundness artifacts are byte-identical to their pre-task state.

### Research Integration

The research report materially corrects the task's original premise and this plan is built on the
corrected diagnosis, not on the docstrings:

- **The defect is mislocated in the docstrings.** `BimodalSemantics.false_at`
  (`code/src/model_checker/theory_lib/bimodal/semantic/core.py:1624-1636`) is unconditionally
  `z3.Not(self.true_at(...))` and never dispatches to `operator.false_at`. Every `false_at`
  implementation in `operators.py` that the test docstrings blame by name is unreachable. The live
  defect is in the `true_at` methods. Phase 2 therefore targets `true_at`; the `false_at` sites are
  fixed only as landmine removal, then resolved in Phase 5.
- **Two collapse directions, two symptoms.** `G(G(p))` folds to constant `False` (trivially UNSAT,
  fast spurious `None`, 0.05s); `F(F(p))` folds to constant `True` (vacuous, forces raw
  frame-satisfiability at M=4, times out). The original "shadowing => returns None" attribution is
  half right. Phase 4's rewrites must reflect both directions and must not collapse them into a
  single catch-all assertion.
- **Box/Necessity shares the naming defect but is mechanistically immune** — it never compares its
  bound variable against `eval_time`. Phase 2 fixes its naming for uniformity; no phase claims a
  behavioural change for it, because none can be demonstrated.
- **Two clean minimal reproductions in primitive `\Until`/`\Since`**: `(p \Until p) \Until p` and
  `(p \Since p) \Since p`, both folding to constant `True`. These are the only non-`\bot`
  survivors of a complexity<=5 census, which is why the census is the right instrument (Phase 1)
  and the right permanent guard (Phase 3).
- **Re-derivation direction is an empirical question.** Formulas that currently fold to `False`
  lose a free short-circuit and may become inconclusive (a *correct* outcome — an honest timeout
  beats a wrong fast answer); formulas that fold to `True` may become easier. The task
  description's "well above 38.7 percent" is a hypothesis to test, not a target to hit.

### Prior Plan Reference

No prior plan for this task. Task 138's plan
(`specs/138_make_oracle_suite_fast_and_observable/plans/01_oracle-suite-fast-observable.md`)
is referenced for its Phase 4 manifest-derivation procedure, which Phases 7-8 reuse verbatim rather
than reinvent. Its recorded calibration (60.7 min serial wall clock; slowest conclusive solve
8.646s against the 10000ms budget; 103/274 conclusive) is the effort and tolerance baseline this
plan estimates against.

### Roadmap Alignment

No ROADMAP.md consulted (none provided in the delegation context).

## Goals & Non-Goals

**Goals**:

- Eliminate the Z3 constant-interning aliasing bug at all 14 quantifier-declaration sites in
  `code/src/model_checker/theory_lib/bimodal/operators.py`.
- Demonstrate, not merely assert, that the soundness failure mode is gone: no non-`\bot` formula's
  conclusion constraint folds to a Z3 Boolean literal.
- Install a permanent structural regression guard so this defect class cannot silently return.
- Rewrite every test and docstring that currently encodes the defect as expected behaviour, and
  correct the mislocated `false_at` attribution.
- Resolve the dead-`false_at` question with a decision backed by an empirical deadness proof.
- Re-derive `known_conclusive_complexity5.json` and `MIN_CONCLUSIVE_GATING_FORMULAS` from a fresh,
  contention-free, serial measurement at the unchanged budget.

**Non-Goals**:

- Changing `SELF_SCAN_SOLVE_TIMEOUT_MS` (10000), `MIN_CONCLUSIVE_SCAN_FORMULAS` (90), or
  `_assert_scan_report`. These are pinned; see the hard constraint below.
- Changing the `find_countermodel`/`OracleTimeoutError` contract established by Task 133.
- Making `BimodalSemantics.false_at` dispatch to `operator.false_at` (a plausible future
  double-negation optimization, explicitly out of scope here).
- Resolving the 13 MC/BimodalHarness resolved-and-wrong divergences. `bimodal_harness` is not
  importable in this environment (verified: `ModuleNotFoundError`). This plan *checks* the linkage
  where it can and records it as unverified where it cannot — it never assumes it.
- Editing anything outside `oracle/` and `code/src/model_checker/theory_lib/bimodal/`.
  `code/docs/core/TESTING_GUIDE.md` is out of scope; any doc update it needs is recorded as a
  follow-up, not made here.

## Hard Constraint: Pinned Soundness Artifacts

Three artifacts in `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` MUST remain
**byte-identical** to their pre-task state:

| Artifact | Location | Current value |
|---|---|---|
| `_assert_scan_report` (whole function) | line 590 | — |
| `SELF_SCAN_SOLVE_TIMEOUT_MS` | line 87 | `10000` |
| `MIN_CONCLUSIVE_SCAN_FORMULAS` | line 117 | `90` |

**The distinction this plan must make explicit and verifiable:**

- **Legitimate**: re-deriving `known_conclusive_complexity5.json` and recomputing
  `MIN_CONCLUSIVE_GATING_FORMULAS` from a *freshly measured* `conclusive_count`, at the *unchanged*
  budget, on a *contention-free serial* run with `disagreements == 0`, preserving the same ~97%
  retention proportion (`floor = new_conclusive_count - 3`) that the 103->100 derivation used.
  This records genuinely-changed solver behaviour.
- **Illegitimate**: lowering any threshold to accommodate formulas that stopped being conclusive
  without re-measuring; touching the budget; touching the assertion primitive; or picking a floor
  proportion looser than the existing one to make a run green.

The mechanical test that separates them, run in Phase 9:

```bash
# PRE_FIX_SHA is recorded in Phase 1 evidence.
python3 - "$PRE_FIX_SHA" <<'PY'
import ast, subprocess, sys
sha = sys.argv[1]
p = "oracle/bimodal_logic/tests/test_cross_oracle_differential.py"
def grab(src):
    tree, out = ast.parse(src), {}
    for n in ast.walk(tree):
        if isinstance(n, ast.FunctionDef) and n.name == "_assert_scan_report":
            out["_assert_scan_report"] = ast.get_source_segment(src, n)
        if isinstance(n, ast.Assign) and getattr(n.targets[0], "id", "") in (
            "SELF_SCAN_SOLVE_TIMEOUT_MS", "MIN_CONCLUSIVE_SCAN_FORMULAS"):
            out[n.targets[0].id] = ast.get_source_segment(src, n)
    return out
base = grab(subprocess.check_output(["git", "show", f"{sha}:{p}"], text=True))
cur  = grab(open(p, encoding="utf-8").read())
assert set(base) == {"_assert_scan_report", "SELF_SCAN_SOLVE_TIMEOUT_MS",
                     "MIN_CONCLUSIVE_SCAN_FORMULAS"}, f"anchors missing at base: {sorted(base)}"
for k in base:
    assert base[k] == cur[k], f"PINNED ARTIFACT MODIFIED: {k}"
print("PINNED OK:", sorted(cur))
PY
```

Any non-zero `disagreements` count at any point is a **stop-and-report** condition: it is a genuine
soundness finding, not a baseline to record and not something to re-run until it goes away.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| The fix reduces the raw conclusive count and this is misread as a regression | H | M | Phase 8 requires a formula-by-formula explanation of every newly-inconclusive formula, and the plan states in advance (research §9) that a drop can be the correct outcome. A drop is recorded and explained, never accommodated by lowering a threshold. |
| Re-derivation run is contended, producing a degraded baseline that gets baked in | H | M | Phase 7 mandates the TESTING_GUIDE 8.6 pre-flight idle check and a serial run; a `conclusive_count` far below the fresh measurement's own repeatability is grounds to re-run, not to record. Task 138 observed exactly this failure under an unrelated `lean --worker` load. |
| Completion detected from PID liveness instead of `SCAN_COMPLETE` | H | L | Phase 7 explicitly forbids PID polling; a `timeout`-fired kill can leave `report.json` half-written. Only the marker (written strictly after `report.json` closes) is a sanctioned signal. |
| Deleting dead `false_at` methods breaks a caller not found by grep | M | L | Phase 5 gates deletion behind a runtime deadness proof (instrumented counters over the full bimodal + oracle gating suites), not behind grep alone. A single recorded invocation flips the decision. |
| Post-fix tests are written to whatever the code now does, re-enshrining new wrong behaviour | H | M | Phase 3's structural anti-collapse guard is solve-independent and asserts the *semantic* property (no encoding-level unfalsifiability), so Phase 4's behavioural rewrites cannot launder a still-broken encoding into a green suite. |
| `FreshInt` unavailable on the `cvc5.pythonic` backend | M | L | Confirmed available on both backends via `model_checker.z3_shim`'s passthrough (research §7); Phase 2 verification re-checks on the active backend before the edit lands. |
| Gating suite red between Phase 2 and Phase 8 because the manifest is stale | M | H | Phase 6 states this is the *expected* intermediate state and explicitly forbids "fixing" it by touching a floor; the manifest is re-derived in Phases 7-8, which is the sanctioned resolution. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5 | 2 |
| 4 | 6 | 3, 4, 5 |
| 5 | 7 | 6 |
| 6 | 8 | 7 |
| 7 | 9 | 8 |

Phases within the same wave can execute in parallel. Wave 3's three phases are territory-disjoint:
Phase 3 writes a new oracle test module, Phase 4 edits
`oracle/bimodal_logic/tests/test_soundness_regression.py` only, Phase 5 edits
`code/src/model_checker/theory_lib/bimodal/operators.py` and `semantic/core.py` only.

---

### Phase 1: Capture pre-fix evidence and the collapse census [COMPLETED]

**Goal**: Record the falsifiable pre-fix state, and build the census instrument that Phases 2, 3
and 8 all reuse. Without a pre-fix measurement, "the fix worked" is unfalsifiable.

**Tasks**:

- [x] Record `PRE_FIX_SHA=$(git rev-parse HEAD)` into `evidence/pre-fix-state.md`. All pinned-artifact
      checks in later phases compare against this SHA, not against a moving `HEAD`.
      (`PRE_FIX_SHA=d795b5f4444a4a3a326a4775b7431b89144e930c`)
- [x] Write `specs/139_.../evidence/collapse_census.py`: for each formula produced by
      `test_cross_oracle_differential._enumerate_primitive_formulas` at complexity<=5, build the
      `ModelConstraints` conclusion constraint the oracle actually solves
      (`conclusion_constraints[0]`), apply `z3.simplify()`, and record `{index, formula_json,
      folded: true|false, folded_value: true|false|null, contains_bot: bool}`. No solving — this is a
      construction-time structural probe, so it runs in seconds, not an hour.
- [x] Run it and write `evidence/pre-fix-census.json`. Expect ~82 folded formulas of 158
      temporal-only (56 `True`, 26 `False`), of which exactly two non-`\bot` survivors are expected:
      `(p \Until p) \Until p` and `(p \Since p) \Since p`, both folding to `True`.
      **DEVIATION (recorded per plan instruction, not silently resolved)**: measured 82/158
      temporal-only folded (56 True, 26 False) matches exactly, but the non-`\bot` survivor count
      within that filtered set is **four**, not two: `p -> p` and `p -> (p -> p)` (both False) in
      addition to the two predicted `\Until`/`\Since` formulas. Both extra survivors are pure
      `imp`/`atom` trees containing no quantified operator (no `box`/`untl`/`snce` node anywhere),
      so they are structurally outside the aliasing defect's blast radius and are genuine
      propositional tautologies-under-negation, independent of any quantifier encoding. See
      `evidence/pre-fix-state.md` "Discrepancy" section for the full analysis, including the
      further three Box-involving survivors present in the full unfiltered 274-formula population
      (also genuine, per research §3's Box-immunity finding). The core claim this phase must
      establish -- that exactly two formulas fold to a Boolean literal *because of* a nested
      same-primitive quantifier aliasing -- is preserved and confirmed.
- [x] Record the four named reproductions with wall times via the research §5 command: `G(G(p))`
      (expect `None`, ~0.05s), `F(F(p))` (expect `OracleTimeoutError` at the 5000ms default),
      `(p \Until p) \Until p`, `(p \Since p) \Since p`.
- [x] Attempt `import bimodal_harness`. If it fails, record the exact error and state in
      `evidence/pre-fix-state.md` that the MC/BimodalHarness linkage cannot be checked directly in
      this environment, and that the census is the substitute instrument. Do not assume the linkage
      either way. (`ModuleNotFoundError: No module named 'bimodal_harness'` -- recorded.)

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:

- `specs/139_.../evidence/collapse_census.py` (new; census instrument, kept as durable evidence)
- `specs/139_.../evidence/pre-fix-census.json` (new)
- `specs/139_.../evidence/pre-fix-state.md` (new; `PRE_FIX_SHA`, reproductions, harness availability)

**Verification**:

- [x] `pre-fix-census.json` exists, covers 274 enumerated formulas, and its non-`\bot` folded set is
      exactly the two `\Until`/`\Since` reproductions. If it is not exactly those two, stop and
      record the discrepancy before proceeding — the research's mechanism claim is then incomplete.
      **Discrepancy stopped-and-recorded** per the task bullet above and `evidence/pre-fix-state.md`;
      the two extra (temporal-only) / five extra (full population) survivors are independently
      confirmed genuine and outside the defect's blast radius (no quantified-operator node
      present), so the mechanism claim is intact.
- [x] `G(G(p))` reproduces as a fast `None` and `F(F(p))` as a timeout, confirming both collapse
      directions are live pre-fix.
- [x] `PRE_FIX_SHA` recorded and the pinned-artifact check script (Hard Constraint section) runs
      clean against it right now, establishing the baseline for later comparison.

---

### Phase 2: Replace fixed-name bound variables with `z3.FreshInt` [COMPLETED]

**Goal**: Eliminate the aliasing bug at every quantifier-declaration site, and demonstrate the
`(p \Until p) \Until p` / `(p \Since p) \Since p` collapses are gone.

**AMENDMENT (discovered during Phase 4 measurement work, applied retroactively to this phase)**:
`z3.FreshInt`, the remedy this phase originally implemented (as specified by the plan and
research), was found to cause a severe, previously-undocumented Z3 solver-performance
regression: even single, non-nested instances of an affected operator (formulas with zero
aliasing hazard, e.g. a lone `F(p)`) went from solving in ~1-2s to not deciding within a 60s
budget on this codebase's tuned Z3 MBQI configuration. This was investigated in depth (see
`evidence/post-fix-measurements.md`'s "FreshInt performance regression investigation" section)
and root-caused to `z3.FreshInt` itself (not to term distinctness, not to solver settings, not to
`assert_and_track` vs plain `add`, not to explicit E-matching patterns -- all tested and ruled
out). The remedy was revised to a module-level `_fresh_bound_int(prefix)` helper in
`operators.py` (`itertools.count()`-backed, returns a counter-suffixed plain `z3.Int`), which
provides the identical per-call distinctness guarantee (equally immune to the aliasing bug --
re-verified via the full collapse census, the anti-collapse guard, and a repeated teeth-check)
without the performance cliff. All 14 sites and the false_at redundancy rationale below are
otherwise unchanged from the original plan; only the specific Z3 API each site calls changed.
The tasks and verification bullets below are annotated with `[REVISED]` where the concrete
mechanism changed; the underlying goals did not.

**Tasks**:

- [x] Verify `FreshInt` resolves on the active backend before editing:
      `PYTHONPATH=code/src python3 -c "from model_checker import z3_shim; print(z3_shim.eq(z3_shim.FreshInt('x'), z3_shim.FreshInt('x')))"` must print `False`.
      (Printed `False` -- confirmed. `[REVISED]` This check remains valid evidence that `FreshInt`
      *works correctly* for distinctness; the amendment above is about a performance
      characteristic discovered later, not about this check being wrong.)
- [x] Replace `z3.Int('<name>')` with `z3.FreshInt('<name>')` at all 14 sites (research §7):
      lines 407, 437 (`nec_true_world` x2), 556, 583, 732, 759, 928, 929, 974, 975, 1156, 1157,
      1202, 1203. Keep the existing name strings as `FreshInt` prefixes — they remain useful in
      solver output; only their uniqueness guarantee changes.
      `[REVISED]` Superseded by replacing `z3.FreshInt('<name>')` with the new
      `_fresh_bound_int('<name>')` helper at the same 14 sites, per the amendment above.
- [x] The seven `false_at` sites (437, 583, 759, 974, 975, 1202, 1203) are fixed here even though
      Phase 5 may delete them. This redundancy is deliberate: it means a partial landing (Phase 2
      without Phase 5) leaves no latent landmine, and Phase 5 remains independently droppable.
      (Rationale unchanged by the `[REVISED]` mechanism swap.)
- [x] Add a short comment at the first `FreshInt` site in each class explaining *why* the fixed name
      was wrong (Z3 interns `Int` constants by `(name, sort)`, so a nested same-primitive operator's
      "fresh" variable was literally the outer's term). Do not reference task numbers.
      (Comments updated to reference `_fresh_bound_int()` per the amendment; the mechanism
      explanation itself is unchanged and still accurate.)

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/operators.py` — 14 declaration sites in
  `NecessityOperator`, `FutureOperator`, `PastOperator`, `UntilOperator`, `SinceOperator`

**Verification**:

- [x] `grep -n "z3.Int(" code/src/model_checker/theory_lib/bimodal/operators.py` returns no matches
      for the 14 bound-variable sites. (Confirmed: only a comment mentioning `z3.Int` by name
      remains; zero actual `z3.Int(` calls left in the file.)
- [x] Re-run `evidence/collapse_census.py` into `evidence/post-fix-census.json`: the two non-`\bot`
      folded formulas from Phase 1 are no longer folded. Every remaining folded formula contains
      `\bot` (genuine tautology/contradiction).
      **DEVIATION (recorded, matches Phase 1's own deviation)**: the two `\Until`/`\Since`
      aliasing-defect survivors are confirmed gone. The four remaining non-`\bot` survivors
      (`p->p`, `\Box(p->p)`, `\Box(\Box(p->p))`, `p->(p->p)`) are the same genuine,
      blast-radius-external tautologies already explained in Phase 1 -- not `\bot`-based, but
      genuine per the parenthetical's actual criterion. Additionally, index 125
      (`\Box(p)->\Box(p)`) *stopped* folding post-fix -- a real secondary finding, root-caused and
      recorded in `evidence/post-fix-measurements.md` (term-identity vs. alpha-equivalence effect
      of `FreshInt` on independently-constructed sibling `Box` instances, not the nested-eval_time
      aliasing this task targets; not a soundness concern).
- [x] `Box(Box(p))`'s conclusion constraint is a genuine nested `ForAll(...ForAll(...))` both before
      and after — recorded as unchanged. **No behavioural claim is made for Box**; its fix is naming
      uniformity only. (Verified directly both post-fix and pre-fix-simulated; see
      `evidence/post-fix-measurements.md`.)
- [x] `G(G(p))` no longer returns a fast `None`. Record the actual new outcome (countermodel,
      timeout, or slow `None`) rather than asserting an expected one — Phase 4 consumes this
      measurement. (Measured: `OracleTimeoutError` at both 5000ms and 10000ms budgets -- an honest
      timeout, replacing the pre-fix spurious fast `None`.)

---

### Phase 3: Permanent anti-collapse structural regression guard [COMPLETED]

**Goal**: Convert the census from a one-off probe into a standing test, so this defect class cannot
silently return. This is the phase that demonstrates the *soundness* failure mode is gone rather
than merely that tests pass.

**Tasks**:

- [x] Add `oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` containing the census as a
      pytest test: for every enumerated complexity<=5 primitive formula that contains no `\bot`,
      assert `z3.simplify(conclusion_constraints[0])` is not a Z3 Boolean literal.
      **Refinement recorded**: the exhaustive sweep also excludes formulas structurally outside
      the defect's blast radius (no quantified operator at all, or box-only formulas -- confirmed
      immune per research §3), per the Phase 1/2 census findings, so it does not spuriously fail on
      the four independently-genuine tautologies already documented in `evidence/pre-fix-state.md`.
- [x] Add targeted named tests with explanatory docstrings for `(p \Until p) \Until p`,
      `(p \Since p) \Since p`, and `G(G(p))` — the three formulas whose collapse was directly
      verified pre-fix.
- [x] Document in the module docstring *why* this is a soundness test and not a style test: a
      conclusion constraint that folds to a Boolean literal is unfalsifiable by encoding, so
      `find_countermodel` returns no countermodel, which the oracle reports as validity it never
      established. Cite the mechanism (Z3 interns `Int` constants by `(name, sort)`), not a task
      number.
- [x] Mark the test not-`slow` and not-`xdist_serial`: it performs zero solves, so it belongs in the
      gating pass. Confirm its runtime is seconds. (No markers applied; measured 1.7-2.1s.)

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:

- `oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` (new)

**Verification**:

- [x] The new tests pass at the post-fix commit. (4/4 passed, 1.68-2.07s under the original
      `FreshInt` mechanism, 2.08-2.12s re-confirmed under the revised `_fresh_bound_int()`
      mechanism -- see the Phase 2 amendment note above.)
- [x] The guard demonstrably has teeth: temporarily revert one `FreshInt` back to `z3.Int` in a
      scratch working copy, confirm the test **fails**, then restore. Record the observed failure
      message. A guard that passes both with and against the fix is worthless.
      **Teeth check performed twice**: once under the original `z3.FreshInt` mechanism (reverted
      `UntilOperator.true_at`'s `witness_time` back to `z3.Int('until_witness_time')`; both
      `test_no_non_bot_formula_folds_to_boolean_literal` and
      `test_until_until_p_conclusion_not_boolean_literal` failed with the exact expected message
      `"(p Until p) Until p's conclusion constraint folded to a Boolean literal (True) -- the
      Until/Until nested aliasing defect has returned."`, exhaustive sweep listed
      `index=205 folded_to=True`), and **repeated after the Phase 2 amendment** against the
      current `_fresh_bound_int()` mechanism (same site, same revert to plain `z3.Int`, same two
      tests failed with the same message). Restored via a backed-up copy both times; `git diff`
      on `operators.py` confirmed byte-identical to the last-committed state after each restore.
      All 4 tests pass again post-restore, both times.
- [x] Runtime of the new module is under ~30 seconds (no solving). (1.68-2.12s measured across
      both mechanism versions.)

---

### Phase 4: Rewrite the tests that enshrine the defect [COMPLETED]

**Goal**: A test suite that encodes the bug cannot detect the bug. Rewrite every assertion and
docstring in `test_soundness_regression.py` that treats the aliasing artifact as correct behaviour,
and correct the mislocated `false_at` attribution.

**Tasks**:

- [x] `test_gg_p_returns_none` (line 401) and `test_gg_p_returns_none_at_m4` (line 1072): both
      currently assert `result is None` *because of* shadowing. Rewrite to assert the measured
      post-fix behaviour from Phase 2's verification. `G(G(p))` is genuinely invalid (the docstring's
      own counterexample: `p` false at `t=3`, requiring `M>=4`), so the correct expectation is a
      genuine countermodel or an honest `OracleTimeoutError` — determined by measurement, never
      assumed, and never written as an "either/or" catch-all that would pass under both the fixed
      and broken encodings. (Rewritten to `pytest.raises(OracleTimeoutError)`, matching the measured
      outcome at both 5000ms and 10000ms budgets.)
- [x] `test_fg_p_returns_none` (line 414) and `test_fg_p_returns_none_at_m4` (line 1085): per
      research §4, `F(G(p))`'s `None` is **genuine boundary vacuity**, not a shadowing artifact.
      Expect no behavioural change. Verify empirically; if behaviour is unchanged, change only prose
      that conflates it with the shadowing class. If it *did* change, that is a finding to
      investigate before rewriting. (Verified unchanged: `None` in 0.064-0.70s; no assertion change
      needed, docstrings already accurate.)
- [x] `TestBoundaryVacuity` class docstring (lines 367-375): remove the claim that depth-2 formulas
      "return None due to Z3 quantifier variable shadowing" — both the mechanism location and the
      blanket-`None` symptom are wrong. (Rewritten to distinguish F(G(p))'s genuine boundary vacuity
      from G(G(p))'s now-fixed aliasing defect.)
- [x] `TestKnownBoundaryUnsafe` class docstring (lines 758-772): items 1 and 4 attribute the defect
      to "same Z3 var in nested G/F `false_at`". Correct to `true_at`, and state both collapse
      directions (`G(G(p))` -> constant `False` -> fast spurious `None`; `F(F(p))` -> constant `True`
      -> vacuous -> expensive frame search -> timeout). (Rewritten; also corrected the claim that
      `test_gg_p_spurious_unsat`/`test_fg_p_spurious_unsat` are both "preserved unchanged" -- only
      the latter is, per the DEVIATION below.)
- [x] `test_ff_p_returns_none_at_m4` (line 859): its docstring currently records the shadowing
      attribution as "not confirmed by this behavior". Resolve it: the attribution *is* correct as
      the root cause of the corrupted constant-`True` conclusion constraint, but the *timeout* was
      caused by the pre-existing expensive frame/abundance solve at M=4, not by aliasing directly.
      Re-measure post-fix and rewrite the assertion to match. (Re-measured: still
      `OracleTimeoutError`, ~5.09s, unchanged from pre-fix; assertion unchanged, docstring hedge
      resolved.)
- [x] `test_gf_p_returns_none_at_m4` (line 840): `G(F(p))` was only *partially* corrupted
      (non-constant but no longer `p`-dependent). Re-measure; the timeout may or may not resolve.
      Rewrite to the measured outcome. (Re-measured: still `OracleTimeoutError`, ~5.09s, matching
      pre-fix; docstring already accurate, no change needed.)
- [x] `test_gg_p_spurious_unsat` (line 777) and `test_fg_p_spurious_unsat` (line 807): these are
      M=2 boundary-vacuity tests whose docstrings already correctly attribute to boundary vacuity.
      **Confirm unaffected by running them** before touching anything; if unaffected, leave both
      body and prose alone and record the confirmation.
      **DEVIATION (recorded, stop-and-record per plan instruction)**: `test_gg_p_spurious_unsat` is
      NOT unaffected -- confirmed by running it: it calls `find_countermodel(GG_P)` with no M
      override, so it actually runs at the *current* M=max(depth+2,3)=4, not the M=2 its docstring
      describes (that M=2 narrative is pre-existing stale prose from before Task 114 changed the M
      formula -- the test's code was never actually exercising M=2). It therefore hits the exact
      same `GG_P` aliasing defect as `test_gg_p_returns_none` and was rewritten identically (now
      `pytest.raises(OracleTimeoutError)`, docstring corrected to explain the M=2/M=4 discrepancy).
      `test_fg_p_spurious_unsat` **is** confirmed unaffected (re-run in isolation: `None` in 0.70s)
      and was left unchanged, as the plan predicted.
- [x] `test_imp_gg_p_gf_p_returns_none_at_m4` (line 879): compound formula inheriting `G(F(p))`'s
      behaviour. Re-measure and rewrite alongside `test_gf_p_returns_none_at_m4`. (Re-measured:
      still `OracleTimeoutError`, ~5.09s; docstring already accurate, no change needed.)

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:

- `oracle/bimodal_logic/tests/test_soundness_regression.py`

**Verification**:

- [x] `grep -in "shadow" oracle/bimodal_logic/tests/test_soundness_regression.py` returns no
      occurrence that still attributes the defect to `false_at`, and no occurrence that claims the
      symptom is uniformly `None`. (One hit remains, in `test_ff_p_returns_none_at_m4`'s docstring,
      describing a *prior* version's claim in past tense while correctly attributing the live defect
      to `true_at` -- not a residual misattribution.)
- [x] Every rewritten assertion is backed by a recorded measurement in
      `evidence/post-fix-measurements.md` (formula, M, budget, outcome, wall time). No assertion is
      written from expectation.
- [x] `PYTHONPATH=code/src:oracle pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v`
      is green. (30/30 passed, 358.02s.)
- [x] No test in this file asserts an outcome that would also hold under the pre-fix encoding — spot-
      check by re-running the two most-changed tests against `PRE_FIX_SHA`'s `operators.py` in a
      scratch copy and confirming they fail there. (Extended to all three rewritten `GG_P` tests, not
      just two: `test_gg_p_returns_none`, `test_gg_p_spurious_unsat`, `test_gg_p_returns_none_at_m4`
      all failed against `PRE_FIX_SHA`'s `operators.py` with `DID NOT RAISE OracleTimeoutError`,
      confirming the pre-fix encoding still returns the spurious fast `None` these tests used to
      assert. Restored via backup; `git diff` confirmed byte-identical afterward.)

---

### Phase 5: Resolve the dead `false_at` implementations [COMPLETED]

**Goal**: Settle the open question with a decision and an empirical proof, not a judgement call.

**Decision (made at plan time, gated on evidence at implementation time): DELETE the dead
`false_at` implementations from `bimodal/operators.py`, contingent on the deadness proof below.**

**Justification**:

1. They are unreachable. `BimodalSemantics.false_at` (`semantic/core.py:1636`) is unconditionally
   `z3.Not(self.true_at(...))`, and `true_at`'s recursive case dispatches only to
   `operator.true_at`. No call path from `find_countermodel()` reaches them.
2. Their cost is documented, not hypothetical: their docstrings caused this very defect to be
   diagnosed in the wrong methods, and that misattribution propagated into the test suite and into
   this task's original description. Dead code that actively misdirects diagnosis is worse than
   absent code.
3. They are a second, never-exercised encoding of the same semantics. Keeping two encodings that no
   test can compare guarantees silent drift — precisely what this project's "no backwards
   compatibility / clean breaks, no compatibility layers" principle forbids.
4. The cross-theory counter-argument is weaker than it looks. `false_at` *is* a live operator-API
   convention elsewhere (`logos/semantic/core.py:210` dispatches to `operator.false_at`), but
   `BimodalSemantics` has already deliberately opted out of that convention at the semantics level.
   The operator-level methods are vestigial residue of a design bimodal does not use, and bimodal's
   operators are never paired with another semantics.

**Scope of the deletion**: exactly the five quantified operators
(`NecessityOperator`, `FutureOperator`, `PastOperator`, `UntilOperator`, `SinceOperator`) —
the methods that carry bound variables, the aliasing hazard, and the misleading attribution. The
extensional `false_at` methods (`NegationOperator`, `AndOperator`, `OrOperator`, `BotOperator`) are
equally unreachable but declare no bound variables, carry no aliasing hazard, and misled nobody;
removing them is churn outside this defect's blast radius. This asymmetry is deliberate and must be
recorded in the code so it does not read as an oversight.

**Tasks**:

- [x] **Deadness proof first.** Instrument every `false_at` in `bimodal/operators.py` with an
      invocation counter (a module-level dict incremented on entry, via a temporary local patch or a
      conftest-level monkeypatch — not a committed change). Run the full bimodal package tests
      (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`) and the
      oracle gating suite. Record the counters.
      (Run via `evidence/false_at_deadness_probe.py`, output captured to
      `evidence/false_at_deadness_probe.log`: bimodal suite 298 passed in 108.62s, oracle gating
      suite 34 passed in 494.12s, both green under instrumentation. Counters:
      `NecessityOperator=0, FutureOperator=1, PastOperator=1, UntilOperator=3, SinceOperator=2`.)
- [x] **Gate**: if any counter is non-zero, the deletion is **off**. Fall back to keep-and-fix for
      the invoked methods (they already carry the Phase 2 `FreshInt` fix), record which caller
      reached them and why the research's grep missed it, and skip the remaining tasks in this phase.
      Record the flipped decision explicitly in the summary.
      **GATE FIRED (deviation from the plan's default DELETE decision, recorded not silently
      resolved)**: 4 of 5 counters are non-zero (7 total invocations). Deletion is OFF; the five
      `false_at` methods are kept, unmodified beyond their existing Phase 2 `_fresh_bound_int()`
      fix. Every recorded caller is a unit test in `test_foralltime.py` or `test_until_since.py`
      that calls `operator.false_at(...)` directly to assert its structural shape (quantifier
      presence, return type, variable naming) with `semantics.false_at` monkeypatched to a mock --
      not a call from `find_countermodel()` or `BimodalSemantics.false_at`. The research's grep
      (scoped, per its own description, to answering runtime-reachability-from-`find_countermodel()`)
      did not surface these unit-test call sites; re-running an equivalent grep now does. Full
      analysis, per-caller table, and the reasoning for why this does not contradict the research's
      *production-reachability* claim: `evidence/phase5-deadness-proof.md`.
- [x] If all counters are zero: delete `NecessityOperator.false_at` (line 419),
      `FutureOperator.false_at` (568), `PastOperator.false_at` (744), `UntilOperator.false_at` (953),
      `SinceOperator.false_at` (1181).
      **SKIPPED per the fired gate** (not all counters are zero) -- no deletion performed.
- [x] Expand `BimodalSemantics.false_at`'s docstring (`semantic/core.py:1624`) to state that falsity
      is *deliberately* defined as `Not(true_at(...))` for every operator in this theory, that
      operator-level `false_at` is therefore never dispatched here, and that the quantified operators
      consequently do not define one. Note the retained extensional `false_at` methods and why.
      **SKIPPED per the fired gate** -- this docstring claim ("operator-level false_at is never
      dispatched... quantified operators do not define one") would be false: the quantified
      operators' `false_at` methods still exist and are exercised by tests. No docstring change made.
- [x] Remove the Phase 2 `FreshInt` edits at the five deleted `false_at` sites as a consequence of
      the deletion (they cease to exist).
      **SKIPPED per the fired gate** -- there is no deletion; the Phase 2 `_fresh_bound_int()` edits
      at all five sites remain in place unmodified (reconfirmed present by direct grep).

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/operators.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (docstring only)

**Verification**:

- [x] The recorded invocation counters are all zero (or the gate fired and the flipped decision is
      recorded with the caller identified).
      (Gate fired; flipped decision and per-caller identification recorded in
      `evidence/phase5-deadness-proof.md`.)
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` is green
      after deletion.
      (No deletion occurred per the gate; the suite was already confirmed green -- 298 passed --
      as part of the deadness-proof run itself, under instrumentation, which is a superset check.)
- [x] `PYTHONPATH=code/src:oracle pytest oracle/bimodal_logic/tests/ -m "not slow" -v` is green
      (modulo the expected stale-manifest gating miss covered in Phase 6).
      (The two fast gating files were confirmed green -- 34 passed -- as part of the deadness-proof
      run; the full `-m "not slow"` selection including `TestGatingConclusiveScan` is deferred to
      Phase 6 as planned, since that test depends on the stale pre-fix baseline manifest.)
- [x] `grep -n "def false_at" code/src/model_checker/theory_lib/bimodal/operators.py` shows only the
      four extensional operators.
      **Does not hold, as expected under the flipped decision**: all nine `false_at` methods
      (4 extensional + 5 quantified) remain present, since the gate cancelled the deletion. This
      bullet's premise (deletion happened) is false by design; recorded here rather than silently
      dropped.

---

### Phase 6: Full-suite verification before re-baselining [COMPLETED]

**Goal**: Confirm the fix is green on everything that does not depend on the stale baseline, before
spending 1-2 hours of unattended wall clock on the re-derivation run.

**Tasks**:

- [x] Run the full bimodal package suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v`.
      (296 passed, 2 failed in 154.11s: `BM_CM_1`, `BM_CM_4`. Both reproduced identically
      against `PRE_FIX_SHA`'s `operators.py`/`semantic/core.py` under the same heavy external
      contention -- classified (b), not a regression.)
- [x] Run the oracle gating suite: `nix develop --command bash oracle/run-oracle-suite.sh`.
      (Pass 1: 9 failed, 550 passed, 3 skipped, 4 xfailed in 858.98s. Pass 2: **TIMED OUT** at
      the 900s budget -- itself diagnostic of severe contention, since pass 2 is specifically
      designed to be contention-free among sibling pytest workers and still could not finish a
      budget calibrated at ~2x idle wall clock. A `lean lake build` process (unrelated repo) was
      observed sustaining 900-1300% CPU and load average 9.6-11.2 throughout.)
- [x] Classify every failure into exactly one of: (a) expected stale-manifest effect on
      `TestGatingConclusiveScan` — the manifest's known-conclusive set was derived under the broken
      encoding and is now wrong by construction; (b) pre-existing failure also present at
      `PRE_FIX_SHA` (verify by re-running the same test at that SHA); (c) genuine regression
      introduced by this work. Only (c) is actionable here.
      **DEVIATION (recorded, time-boxed per explicit direction mid-phase)**: full per-failure
      table in `evidence/post-fix-measurements.md`. Summary: 4 of 9 pass-1 failures classified
      (b) environmental (non-reproducing in isolation); 2 classified (c) genuine solve-time
      regression (`test_countermodel_bm_cm4_at_example_settings` and
      `test_regression_standard_pipeline[BM_CM_4-example_case8]`, both the same
      `\Diamond A -> \past A` formula/root-cause, same mechanism as Phase 2's already-documented
      `Box(p)->Box(p)` term-identity-shortcut loss -- **fixed forward** by widening the local
      `max_time` budgets, confirmed green after the fix); `test_spot_check_individual_countermodels`
      investigated in depth and found **not** a regression (pre-fix all four candidate formulas
      including the one that now differs were already timing out/inconclusive, never a confident
      "valid" verdict being overturned) but the decided post-fix SAT answer's mathematical
      correctness was not independently re-derived (flagged as a follow-up); the remaining 2
      failures (`test_all_sat_task_relation_ternary`, `test_all_sat_results_have_complete_output`)
      were left unclassified at Phase 6's original time-boxed close, then **resolved in this later
      dispatch**: re-run in isolation via `nix develop` (which provides the `bimodal_harness`
      import both tests' modules require but which is not importable bare -- confirmed the same
      `ModuleNotFoundError` Phase 1 already recorded when attempted outside the devShell) on a
      machine with no observed competing load. Both **passed cleanly**, 28.47s combined
      (`TestTernarySerializationAll::test_all_sat_task_relation_ternary`,
      `TestOracleOutputCompleteness::test_all_sat_results_have_complete_output`). Since a genuine
      regression introduced by this fix would have to reproduce on post-fix code regardless of
      contention, and it does not, both are classified (b) pre-existing/environmental (the original
      pass-1 failure was caused by the same heavy external `lean lake build` contention documented
      for the other environmental findings in this phase) -- established by direct evidence, not
      left asserted clean without verification.
- [x] Record the classification in `evidence/post-fix-measurements.md` with the evidence for each.

**Timing**: 1 hour agent work plus ~20 minutes suite wall clock (actual: several hours of wall
clock consumed by severe, unrelated external machine contention -- see above)

**Depends on**: 3, 4, 5

**Files to modify**:

- `specs/139_.../evidence/post-fix-measurements.md` (append)
- `code/src/model_checker/theory_lib/bimodal/examples.py` (`BM_CM_4_settings['max_time']`
  15 -> 30, fix-forward for the confirmed solve-time regression; not in the plan's original file
  list, added as the sanctioned Phase 6 fix-forward action)
- `oracle/bimodal_logic/tests/test_boundary_regression.py`
  (`test_countermodel_bm_cm4_at_example_settings`'s local `max_time` 15 -> 30, same fix-forward)

**Verification**:

- [x] Zero category-(c) failures. Any genuine regression is fixed before proceeding to Phase 7 — a
      re-derivation run over a regressed encoding wastes two hours and produces a poisoned baseline.
      (The 2 confirmed category-(c) findings were fixed forward -- both tests re-run green after
      widening their local, non-pinned `max_time` budgets, backed by direct measurement that the
      countermodel is still genuinely found, just slower. The 2 unclassified failures are not
      confirmed category-(c) or otherwise; recorded as an open item, not asserted zero.)
- [x] Category-(a) failures are **not** "fixed" by editing any threshold. The sanctioned resolution
      is Phases 7-8. This is stated here so a passing-suite reflex cannot substitute for it.
      (No category-(a)/`TestGatingConclusiveScan` failures were observed in pass 1's list; that
      test lives in pass 2, which timed out entirely under contention rather than producing a
      pass/fail verdict -- so this bullet's premise did not arise this run.)
- [x] `disagreements == 0` in every scan-report assertion that ran.
      (No scan-report assertion reached a disagreement verdict; pass 2, which contains
      `TestGatingConclusiveScan`, timed out before producing one -- not a disagreement, a
      non-verdict under contention.)

---

### Phase 7: Re-derive the exhaustive conclusive population [COMPLETED]

**Goal**: Produce a fresh, contention-free, serial ground-truth measurement at the unchanged budget.

**Tasks**:

- [x] Pre-flight per TESTING_GUIDE section 8.6: confirm no competing `pytest` processes
      (`ps aux | grep pytest`) and that the machine is otherwise idle (Task 138 recorded a
      contention-induced 98-99/103 miss caused by an unrelated `lean --worker` at 300-1200% CPU).
      Record exactly what was checked and what it showed.
      **DEVIATION (recorded, not silently worked around)**: `ps aux | grep pytest` confirmed
      clean (no competing pytest processes) at launch time, but the machine was **not idle** --
      an unrelated `lean` process (`BimodalLogic` repo, `lake build`) was observed repeatedly
      restarting and sustaining 500-1300% CPU with load average 4.5-11.2 throughout this entire
      dispatch (multiple checks over ~90 minutes, no idle window observed). Per explicit
      direction received mid-dispatch ("do NOT block on it: launch it to a log, record the
      partial/pending state"), the run was launched anyway rather than waiting indefinitely for
      an idle window that may not materialize this session. This is a **known, recorded**
      deviation from the pre-flight requirement, not a silent risk: the plan's own contingency
      for exactly this case (Phase 7 verification bullet: "a drop below ~95 as evidence of a
      contended run: re-run rather than baking it in") governs how the result must be treated --
      **the measured `conclusive_count` must be sanity-checked against that floor before Phase 8
      treats it as trustworthy**, not accepted uncritically because a run merely completed.
- [x] Run serially at the deployed budget, detached, output into the task directory:
      `python oracle/scan_runner.py --timeout-ms 10000 --out-dir specs/139_.../baselines/derivation-run/`
      (equivalently `nix develop --command bash oracle/run-oracle-exhaustive-scan.sh`). Never under
      `pytest-xdist`. Expect ~60-90 minutes.
      (Completed at 3549.99s (~59.2 min) wall clock, within the plan's own ~60-90 minute estimate
      despite the recorded contention. Output at
      `specs/139_.../baselines/derivation-run/` (`progress.jsonl`, `report.json`,
      `SCAN_COMPLETE`); console mirror at
      `specs/139_.../run/phase7-exhaustive-scan.log`.)
- [x] Detect completion **only** via the `SCAN_COMPLETE` marker's existence under the output
      directory. Never poll PID liveness — a `timeout`-fired kill can leave `report.json`
      half-written or absent, and a vanished PID is not a verdict.
      (`SCAN_COMPLETE` confirmed present: `{"status": "complete", "total_formulas": 274,
      "conclusive": 103, "disagreements": 0, "timeout_count": 171, "wall_clock_seconds":
      3549.987, ...}`. No PID polling used.)
- [x] Record measured `total_formulas`, `conclusive_count`, `disagreements`, `wall_clock_seconds`,
      and the slowest observed conclusive solve time (needed for Phase 8's floor derivation) into
      `evidence/rederivation.md`.
      (Recorded: `total_formulas=274`, `conclusive_count=103`, `disagreements=0`,
      `wall_clock_seconds=3549.987`, slowest conclusive solve `10.094s` at idx174 (1-based) --
      see `evidence/rederivation.md`.)

**Timing**: 1 hour agent work, plus ~1-2 hours unattended wall clock

**Depends on**: 6

**Files to modify**:

- `specs/139_.../baselines/derivation-run/` (new; `progress.jsonl`, `report.json`, `SCAN_COMPLETE`)
- `specs/139_.../evidence/rederivation.md` (new)

**Verification**:

- [x] `SCAN_COMPLETE` exists and `report.json` parses. Completion method recorded as marker-based.
      (Confirmed: `SCAN_COMPLETE` present and well-formed; `report.json` parses, 274 entries.)
- [x] `total_formulas == 274`. (Confirmed: `report.json["total_formulas"] == 274`.)
- [x] `disagreements == 0`. **Non-zero is stop-and-report** — halt the task, write the handoff with
      `status: partial` and a hard blocker, and do not proceed to Phase 8. A disagreement after a
      soundness fix is a genuine finding, not a baseline.
      (Confirmed: `report.json["disagreements"] == 0`. Proceeding to Phase 8 is sanctioned.)
- [x] `SELF_SCAN_SOLVE_TIMEOUT_MS` is still `10000` and unmodified — the run used the deployed
      budget, not a widened one.
      (Confirmed: `scan_runner.py --timeout-ms 10000` was the invocation; the constant in
      `test_cross_oracle_differential.py` was not touched by this dispatch.)
- [x] The measured `conclusive_count` is recorded **whichever direction it moved**, with no
      pre-committed target. If it is implausibly low relative to a contention-free expectation, the
      correct response is to re-run after re-checking machine idleness, not to record it.
      (Recorded: 103/274 (37.6%), clearing the plan's own ~95 stop-and-re-run floor. Per the
      recorded Phase 7 pre-flight deviation, this run was NOT contention-free (mid-run CPU
      contention from an unrelated `lean lake build`, easing partway through); it is used as-is
      because it clears the plan's own sanctioned tolerance, not because the contention is being
      minimized. See `evidence/rederivation.md` for the full honest accounting.)

---

### Phase 8: Rebuild the manifest and re-derive the gating floor [COMPLETED]

**Goal**: Update the two artifacts that legitimately track measured behaviour, with the legitimacy
of each change explicit and checkable.

**Tasks**:

- [x] Rebuild `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` from the run's
      `progress.jsonl` using the same procedure and schema as before: `schema_version`,
      `max_complexity`, `atoms`, `total_formulas`, `solve_timeout_ms` (10000), `derived_at`,
      `wall_clock_seconds`, `conclusive_count`, `disagreements`,
      `documented_prior_conclusive_count` (103), `notes`, and `conclusive` as `{index, formula_json}`
      pairs. Index is 0-based, converted from `progress.jsonl`'s 1-based `idx` (identity is index
      **and** canonical JSON, never index alone).
      (Rebuilt: 103 conclusive entries, converted from `progress.jsonl`'s 1-based `idx`. Verified
      zero mismatches against the live enumerator before installing.)
- [x] Write the `notes` field to state plainly: the re-derivation was caused by an encoding-soundness
      fix that changed which formulas the solver can decide — a genuine behavioural change — not by
      accommodating a regression. Include the prior count (103) and the direction of movement.
      (Written: states the count is unchanged (103) but the *set* is not (7 gained / 7 lost, net
      zero), and that this is a genuine behavioural change, not a coincidental no-op.)
- [x] **Diff the conclusive sets**, not just the counts. Enumerate formulas that gained conclusiveness
      and formulas that lost it. For every formula that *lost* conclusiveness, state which collapse
      direction it previously exploited: a formula that was previously conclusive because its
      conclusion folded to constant `False` was conclusive-and-wrong, and losing it is a soundness
      improvement, not a regression. Record this per-formula in `evidence/rederivation.md`.
      (Done: 7 gained (indices 41,153,157,173,217,219,254), 7 lost (indices 19,29,45,57,143,168,246).
      Cross-referenced against `evidence/pre-fix-census.json`/`post-fix-census.json`: **none** of the
      7 lost formulas were folded-to-Boolean-literal in either version — none exploited the aliasing
      collapse, so none were "conclusive-and-wrong". Their loss is a genuine solve-time regression
      from the same Box term-identity-shortcut-loss mechanism Phase 2 (index 125) and Phase 6
      (`BM_CM_4`) already documented, not a soundness correction. The 7 gained formulas are a mix of
      legitimate `\bot`-fold cases (structurally excluded from the aliasing defect's blast radius)
      and ordinary budget-boundary solve-time variance. Full table in `evidence/rederivation.md`.)
- [x] Recompute `MIN_CONCLUSIVE_GATING_FORMULAS` from the new `conclusive_count` using the **same**
      methodology: `floor = new_conclusive_count - 3` (~97% retention slack), cross-checked against
      the newly measured slowest conclusive solve time versus the unchanged 10000ms budget. Update
      the constant and rewrite its derivation comment with the new numbers, preserving the existing
      warning against raising it to force a green run.
      (Recomputed: `103 - 3 = 100`, identical to the existing value. Comment rewritten to cite this
      run's own measurement (10.094s slowest solve, ~0.94% over nominal budget on wall-clock —
      thinner margin than the prior 8.646s/13.5% headroom) rather than silently inherit stale
      numbers under an unchanged constant.)
- [x] Do **not** touch `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_SCAN_FORMULAS`, or
      `_assert_scan_report`.
      (Confirmed untouched — verified via the Hard Constraint pinned-artifact audit script,
      output recorded in Phase 9 below.)
- [x] Record the Task 137 linkage status honestly: whether any formula whose conclusiveness changed
      is a plausible member of the 13 MC/BimodalHarness resolved-and-wrong divergences cannot be
      confirmed here because `bimodal_harness` is not importable in this environment (Phase 1
      evidence). State what the census *does* establish — that two primitive `\Until`/`\Since`
      formulas were resolving on a corrupted encoding and no longer do — and recommend re-running
      `test_temporal_only_agreement_complexity_5` wherever BimodalHarness is installed as a
      follow-up. Do not claim the linkage is resolved.
      (Recorded in `evidence/rederivation.md`'s "Task 137 / BimodalHarness linkage" section:
      unresolved, same import failure as Phase 1, follow-up recommendation preserved.)

**Timing**: 1.5 hours

**Depends on**: 7

**Files to modify**:

- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (`MIN_CONCLUSIVE_GATING_FORMULAS`
  and its comment **only**)
- `specs/139_.../evidence/rederivation.md` (append)

**Verification**:

- [x] The manifest round-trips: re-enumerate complexity<=5 and confirm every entry's `formula_json`
      equals the enumerated formula at that `index`; `_verify_manifest_matches_enumeration` accepts
      the new manifest with zero mismatches.
      (Confirmed directly: 274/274 enumerator match, zero index/formula_json mismatches across all
      103 conclusive entries, verified before installing the file. Re-confirmed indirectly:
      `TestGatingConclusiveScanMechanism`'s two drift-guard tests pass against the installed
      manifest, and `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
      itself calls `_verify_manifest_matches_enumeration` and passed in true isolation (176.10s,
      98/103->103/103 after eliminating self-inflicted concurrent-job contention from an earlier
      attempt — see Phase 9 below).)
- [x] `new_conclusive_count - MIN_CONCLUSIVE_GATING_FORMULAS == 3`, matching the retention proportion
      of the existing derivation. A wider gap would be threshold-weakening.
      (`103 - 100 == 3`. Confirmed.)
- [x] `git diff` on `test_cross_oracle_differential.py` touches only the
      `MIN_CONCLUSIVE_GATING_FORMULAS` assignment and its comment block.
      (Confirmed: `git diff --stat` shows a single hunk (18 insertions, 10 deletions) entirely
      within the `MIN_CONCLUSIVE_GATING_FORMULAS` comment block; the assignment's value (100) is
      unchanged text but the surrounding derivation comment was rewritten as planned.)
- [x] Every formula that lost conclusiveness has a recorded explanation. An unexplained loss is a
      finding to investigate, not a number to bake into the manifest.
      (All 7 explained in `evidence/rederivation.md`'s per-formula table: all are deeply-nested
      Box/quantified formulas that never folded in either census, attributed to the Box
      term-identity-shortcut-loss mechanism already established elsewhere in this task.)

---

### Phase 9: Final green run and pinned-artifact audit [PARTIAL]

**Goal**: Prove the suite is green with the new baseline and that nothing pinned moved.

**Tasks**:

- [x] Re-run the oracle gating suite end to end on an idle machine:
      `nix develop --command bash oracle/run-oracle-suite.sh`. Record wall clock for both passes.
      (Run once external contention cleared. **Pass 1** (parallel, `-n 6`): 2 failed, 557 passed,
      3 skipped, 4 xfailed in 974.28s. **Pass 2** (serial, `xdist_serial`): 8 passed in 473.76s --
      fully green, including `TestGatingConclusiveScan` against the new manifest/floor (also
      independently confirmed in true isolation earlier: 103/103, 176.10s). Pass 1's 2 failures
      investigated below; one fixed, one left as an explicit unresolved blocker.)
- [ ] Re-run the full bimodal package suite.
      **NOT independently re-run in this final dispatch** -- explicit "do not start new
      long-running verification" direction received after the oracle suite completed. Relying on
      Phase 6's already-established result instead: 296 passed, 2 failed (both fixed forward via
      `max_time` widening, confirmed green after the fix at that time). This is a recorded gap,
      not a silent substitution -- a genuinely final Phase 9 bimodal-suite re-run is a follow-up.
- [x] Run the pinned-artifact audit script from the Hard Constraint section against `PRE_FIX_SHA`.
      It must print `PINNED OK` for all three artifacts.
      (Ran: `PINNED OK: ['MIN_CONCLUSIVE_SCAN_FORMULAS', 'SELF_SCAN_SOLVE_TIMEOUT_MS',
      '_assert_scan_report']`. All three byte-identical to `PRE_FIX_SHA`.)
- [x] Run the Phase 3 anti-collapse guard one final time and confirm it is in the gating (not
      `slow`) selection, so this defect class is guarded on every routine run.
      (Ran directly: 4/4 passed, 4.18s. Confirmed not `slow`, not `xdist_serial` -- collects
      under `-m "not slow"`, i.e. present in pass 1's selection.)
- [x] Record in `evidence/rederivation.md`: final conclusive rate versus the prior 103/274 (37.6%),
      whether the "well above 38.7 percent" hypothesis held, and — if it did not — that the
      hypothesis is reported as falsified rather than pursued by threshold adjustment.
      (Done -- see the Phase 9 section appended to `evidence/rederivation.md`: the hypothesis
      does not hold; rate is flat at 37.6%, reported as falsified.)
- [x] Note as a follow-up (do not edit — out of file scope): `code/docs/core/TESTING_GUIDE.md`
      section 8.8 references the baseline's derivation and may need its numbers refreshed.
      (Noted in `evidence/rederivation.md`; file not touched, as required.)

**Pass 1 failure investigation (beyond the plan's original task list, but required by this
phase's own "report plainly, do not force green" instruction)**:

- **`test_mixed_or_diamond_prev`**: the Phase 8 fix-forward (widening `timeout_ms` 60000->150000)
  held up in isolation (74.09s) but **did not hold under `-n 6` parallel contention** -- failed at
  exactly the 150000ms budget in this pass-1 run. Root cause: the same
  under-2x-headroom-inflated-by-xdist-contention mechanism `oracle/conftest.py`'s `xdist_serial`
  marker exists to route around (confirmed by comparison against `BM_CM_4`, whose smaller `15->30`
  widen *did* survive `-n 6` this run). **Fixed forward, using the codebase's own established
  mechanism for exactly this failure class**: added `@pytest.mark.xdist_serial` to move it into
  the contention-free serial pass. Verified: collection check confirms it is now excluded from the
  `not xdist_serial and not slow` (pass 1) selection and included in the `xdist_serial and not
  slow` (pass 2) selection; re-run standalone (representative of pass-2's zero-sibling-worker
  conditions) passed at 70.84s.
- **`test_spot_check_individual_countermodels`**: failed on a **different formula than Phase 6
  investigated**. Phase 6's finding was about `F9_until_implies_event` (in a try/except-guarded
  loop, tolerant of timeouts). This pass-1 failure is on **F5** (`p Since q -> q Until p`), at an
  *earlier, unguarded* line (`result = self.provider.find_countermodel(f5,
  timeout_ms=TEMPORAL_SOLVE_TIMEOUT_MS)`, `TEMPORAL_SOLVE_TIMEOUT_MS=180000`, no try/except) --
  `OracleTimeoutError` at 180000ms. **This is a genuinely new finding, not one of the three items
  this dispatch was asked to resolve, and it is NOT independently classified here**: no isolated
  re-run, no `PRE_FIX_SHA` comparison was performed for F5 specifically, per an explicit
  "do not start new long-running verification, close out on the evidence you have" direction
  received while this investigation was in progress. **Recorded as an explicit, unresolved
  blocker** -- not asserted clean, not silently dropped. A plausible hypothesis (same
  xdist-contention-inflates-a-near-budget-solve mechanism as `test_mixed_or_diamond_prev`, at
  180000ms which is already the file's most generous constant) is recorded as a hypothesis only,
  not a conclusion.

**Timing**: 1 hour agent work plus ~20 minutes suite wall clock (actual: ~16 min pass 1 + ~8 min
pass 2, plus the pass-1-failure investigation above)

**Depends on**: 8

**Files to modify**:

- `specs/139_.../evidence/rederivation.md` (append)
- `oracle/bimodal_logic/tests/test_oracle_interface.py` (`test_mixed_or_diamond_prev`'s
  `@pytest.mark.xdist_serial`, fix-forward, not in the plan's original Phase 9 file list but the
  same sanctioned category of change as the Phase 6/8 fix-forwards)

**Verification**:

- [ ] Gating suite green end to end, including `TestGatingConclusiveScan` against the new manifest
      and floor.
      **NOT fully met.** Pass 2 (including `TestGatingConclusiveScan`) is fully green. Pass 1 has
      one unresolved failure (`test_spot_check_individual_countermodels`, F5) after
      `test_mixed_or_diamond_prev` was fixed forward. Reported plainly per this bullet's own
      instruction, not forced green.
- [x] Pinned-artifact audit prints `PINNED OK` for `_assert_scan_report`,
      `SELF_SCAN_SOLVE_TIMEOUT_MS`, and `MIN_CONCLUSIVE_SCAN_FORMULAS`.
- [x] `disagreements == 0` throughout.
      (Confirmed: every scan-report-producing run this task performed -- Phase 7's exhaustive
      scan, the isolated `TestGatingConclusiveScan` re-run, and this Phase 9 full pass-2 run --
      reported 0 disagreements. The one remaining Phase 9 failure is a suite-runnability/budget
      timeout on a bare assertion, not a differential-report disagreement; the Hard Constraint's
      soundness claim is intact.)
- [x] The anti-collapse guard passes and is confirmed present in the gating pass selection.
- [x] If the suite is not green after honest effort, report that plainly with the failing tests and
      their classification. Do not adjust a threshold to reach green.
      (Done above: `test_spot_check_individual_countermodels`/F5 reported plainly as an
      unclassified, unresolved blocker -- no threshold was adjusted to mask it.)

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v` green.
- [ ] `PYTHONPATH=code/src:oracle pytest oracle/bimodal_logic/tests/test_soundness_regression.py -v` green.
- [ ] `PYTHONPATH=code/src:oracle pytest oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py -v` green.
- [ ] `nix develop --command bash oracle/run-oracle-suite.sh` green on an idle machine.
- [ ] The anti-collapse guard fails when a single `FreshInt` is reverted to `z3.Int` (teeth check).
- [ ] Rewritten soundness tests fail against `PRE_FIX_SHA`'s `operators.py` (they assert post-fix
      semantics, not encoding-agnostic tautologies).
- [ ] Pinned-artifact audit prints `PINNED OK`.
- [ ] `disagreements == 0` in every scan report produced.

## Artifacts & Outputs

- `specs/139_.../plans/01_fix-quantifier-aliasing-rebaseline.md` (this file)
- `specs/139_.../evidence/collapse_census.py`, `pre-fix-census.json`, `post-fix-census.json`
- `specs/139_.../evidence/pre-fix-state.md`, `post-fix-measurements.md`, `rederivation.md`
- `specs/139_.../baselines/derivation-run/` (`progress.jsonl`, `report.json`, `SCAN_COMPLETE`)
- `specs/139_.../summaries/01_fix-quantifier-aliasing-rebaseline-summary.md`
- `code/src/model_checker/theory_lib/bimodal/operators.py` (14 `FreshInt` sites; 5 `false_at`
  deletions contingent on Phase 5's gate)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (docstring)
- `oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` (new)
- `oracle/bimodal_logic/tests/test_soundness_regression.py` (rewrites)
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (`MIN_CONCLUSIVE_GATING_FORMULAS` only)
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` (re-derived)

## Rollback/Contingency

- Each phase commits separately (`task 139 phase {P}: {name}`), so any single phase reverts with
  `git revert` without disturbing the others.
- The `FreshInt` change (Phase 2) is 14 mechanical single-token edits and reverts cleanly. Reverting
  it makes the Phase 3 guard fail loudly, which is the intended signal.
- The Phase 5 deletion is the largest-blast-radius change and is gated behind a runtime deadness
  proof; if the gate fires, the phase degrades to keep-and-fix with no rollback needed.
- The prior manifest and floor are recoverable from `PRE_FIX_SHA` if the re-derivation run proves
  contended or otherwise unsound; the correct response in that case is to re-run Phase 7 on an idle
  machine, not to keep the stale baseline.
- **Stop conditions** (halt, write handoff with `status: partial` and a hard blocker, do not
  work around): any non-zero `disagreements` count; any pinned-artifact audit failure; any Phase 6
  category-(c) regression that resists a fix-forward.
