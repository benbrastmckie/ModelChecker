# Implementation Plan: A2-triangle encoding-completeness test

- **Task**: 191 - A2 triangle encoding completeness test
- **Status**: [COMPLETED]
- **Effort**: 4.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/191_a2_triangle_encoding_completeness_test/reports/01_a2-triangle-encoding-completeness.md
- **Artifacts**: plans/01_a2-triangle-encoding-completeness.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Build the A2-triangle deciding test from `bimodal/docs/ADEQUACY.md` section 7.3 as a standing test
in this repository's suite. At `back = mid = fwd = 1` and a closure `|C| <= 4`, exhaustively
enumerate every candidate witness family `(bx, L_0, ..., L_k)` over subsets of `C` and compare
three verdicts per closure: (i) the pure-Python re-checker `certificate.recheck`, (ii)
`lake exe check_certificate`, and (iii) whether the real Z3 encoding reports SAT on the same
Gamma/Delta at the same lengths. Legs (i) and (ii) are already compared on the fixture corpus by
`tests/integration/test_certificate_lean_agreement.py`; leg (iii) — the encoding-completeness
direction — has never been built, and that is the substance of this task. Definition of done: a
new `tests/integration/test_certificate_a2_triangle.py` runs the exhaustive enumeration
unconditionally for three closures, compares its aggregate against `BimodalStructure`'s real
SAT/UNSAT verdict, cross-checks a bounded deterministic sample against the Lean binary under the
existing skip discipline, and the full bimodal suite stays green.

### Research Integration

Report `01_a2-triangle-encoding-completeness.md` established that no production code is needed:
leg (i) is `certificate.recheck(family, premises, conclusions, target_time)`, leg (ii) reuses
`test_certificate_lean_agreement.py`'s `_run_check_certificate`/skip-resolution plumbing, and leg
(iii) is `test_structure.py`'s `_build(premises, conclusions, back=1, mid=1, fwd=1)` followed by
reading `structure.z3_model_status`. It also flagged the enumeration's combinatorics (1,536
candidates box-free, 1,572,864 with one box) as needing a runtime decision, recommended two
closure-verified Gamma/Delta pairs, and recommended promoting the Lean plumbing to a shared
helper now that a second consumer exists.

Plan-time measurement resolved the one open runtime question the report left for `/plan`, so the
"benchmark first, then decide" contingency the report recommended is already discharged and is
**not** carried as a phase here:

| Measured at plan time (this repo state, this host) | Value |
|---|---|
| `recheck` cost, single-lasso candidate | ~6.7 us/call |
| `recheck` cost, two-lasso candidate | ~7.7 us/call |
| Box-free Until closure: rechecks / accepted candidates | 1,536 / 52, <0.1 s |
| Single-box closure: rechecks / accepted candidates | 1,572,864 / 96, ~11.5 s |
| `["A"] / ["A"]` closure: rechecks / accepted candidates | 24 / 0 |
| Z3 verdict, all three closures | SAT, SAT, UNSAT — agreeing with the enumeration in every case |
| One `lake exe check_certificate` invocation | ~2.2 s |

Consequences adopted below: the literal subsets-of-`C` enumeration ADEQUACY section 7.3 specifies
is affordable unconditionally (no atoms-only derived generator, which the report offered only as a
fallback), and the Lean leg is the sole component that must be sample-bounded (~2.2 s per
subprocess makes the 148 accepted candidates across the two SAT closures a ~5.5-minute cost,
against the ~22 s the existing 10-test Lean module takes).

### Prior Plan Reference

No prior plan for this task. The originating scope note lives in task 184's
`plans/01_witness-family-certificate-redesign.md` Phase 5, whose "resume at the Phase 9 handoff"
pointer is broken (that handoff carried only the A0 standing test); this plan supersedes that
pointer and does not reuse its phase structure.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch; no roadmap consultation performed.

## Goals & Non-Goals

**Goals**:
- A standing test module `tests/integration/test_certificate_a2_triangle.py` implementing the
  ADEQUACY section 7.3 A2-triangle comparison at `back = mid = fwd = 1`.
- Exhaustive, deterministic candidate enumeration over subsets of the closure — faithful to the
  section's literal "enumerate every candidate ... over subsets of `C`" wording.
- Leg (iii) coverage: the enumeration's aggregate ("some candidate is accepted") compared against
  `BimodalStructure.z3_model_status` for the same Gamma/Delta, in both the SAT and the UNSAT
  direction.
- Leg (ii) coverage on a bounded deterministic sample, plus on the live Z3-extracted certificate
  (which the production fail-fast guard re-checks in Python only, never against Lean).
- A shared, importable Lean-invocation helper, so the skip-resolution/subprocess plumbing exists
  once rather than twice.
- ADEQUACY section 7.3 updated to record the deciding test as standing, mirroring section 7.2's
  A0 wording.

**Non-Goals**:
- Any change to production semantics, encoder, or re-checker code. This task adds tests and docs
  only; a triangle disagreement is a finding to report, not something this task pre-emptively
  fixes.
- Closures with `|C| > 4`, or lengths other than `back = mid = fwd = 1`.
- The atoms-only derived candidate generator (the report's optional optimization) — unnecessary at
  the measured cost and harder to argue as faithful to the section's literal text.
- Exhaustive Lean cross-checking of all accepted candidates (~5.5 minutes of subprocesses).
- Repairing task 184's broken resumption pointer in its own plan file.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The enumeration and the encoder disagree about candidate shape (lasso count, `bx` keying, target-time range), producing a false triangle failure | H | M | Read all three from the live search object rather than re-deriving: lasso count from `semantics._active_lassos`, `bx` keys from the `Box` children of the closure (matching `extract_certificate` and `_box_faithful`, both of which key on `Box.child`), target times from `witness_registry.target_window()` = `range(-1, 2)` |
| Re-deriving premises/conclusions from surface syntax yields different `Formula` objects than the search used, so the closures differ | H | M | Drive `recheck` with `structure.semantics._premise_formulas`/`_conclusion_formulas` — the same objects the encoder translated (precedent: `test_structure.py`'s existing re-check assertions) |
| Lean leg makes the suite unacceptably slow | M | H (if unbounded) | Fixed, named per-class sample budget (module constant), sized against the ~2.2 s/invocation measurement; the exhaustive work stays in pure Python |
| A future example addition uses `\rightarrow`/`\wedge`/`\vee`, silently blowing past `\|C\| <= 4` via `DefinedOperator` expansion into nested `Imp`/`Bot` | M | M | Assert `len(closure) <= 4` inside the test for every example, so the bound is machine-checked rather than a comment |
| The single-box enumeration's ~12 s makes routine local runs slower | L | M | Mark that case with the already-registered `slow` marker (`code/pyproject.toml`), deselectable via `-m "not slow"`; no new marker invented |
| Extracting the shared Lean helper regresses the existing Lean-agreement module | M | L | Phase 1 is a pure move with no behavior change, verified by re-running that module before anything new is added |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: Phases 2-4 all
write the same new test module, so they are deliberately not parallelized.

### Phase 1: Extract the shared Lean-check helper [COMPLETED]

**Goal**: The `lake exe check_certificate` invocation and skip-resolution plumbing lives in one
importable place, with the existing Lean-agreement module unchanged in behavior.

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` holding
      `_resolve_bimodal_logic_path`, `_resolve_lake`, `run_check_certificate(payload, timeout)`,
      the trivial-payload `probe()`, the resolved `BIMODAL_LOGIC_PATH`/`LAKE` values, the
      `BIMODAL_LOGIC_COMMIT` constant, and the computed skip reason — exported under public names
      (no leading underscore on what other modules import).
- [x] Re-point `tests/integration/test_certificate_lean_agreement.py` at the helper via an
      absolute import (`from model_checker.theory_lib.bimodal.tests._lean_check import ...`);
      `tests/` is a package (`tests/__init__.py` exists) but `tests/integration/` is not, so do
      not use a relative import.
- [x] Keep that module's `pytestmark = pytest.mark.skipif(...)` semantics identical: skip with a
      named reason, never fail, when the checkout, `lake`, or the probe is unavailable.
- [x] Note in the helper's docstring that the module-level probe now runs once per session shared
      across consumers, rather than once per consuming module.
- [x] **Deviation (not in original task list)**: the plan's own verification step below assumed
      `test_certificate_lean_agreement.py`'s moved names had no other importer, but
      `tests/unit/test_semantics_core.py` imported `_SKIP_REASON`/`_run_check_certificate`/
      `PER_FIXTURE_TIMEOUT_SECONDS` from it directly (`TestExportedCertificateAgreesWithLeanBinary`).
      Re-pointed that import at `_lean_check.py`'s public `SKIP_REASON`/`run_check_certificate`,
      with a local `_LEAN_TIMEOUT_SECONDS = 30` replacing the borrowed
      `PER_FIXTURE_TIMEOUT_SECONDS` (that name stayed fixture-corpus-specific, not promoted to
      the shared helper). Verified via the same test run as the rest of this phase.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - new shared helper module
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  import from the helper; delete the moved definitions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py -v`
  still reports the same test count and outcomes as before the move (10 tests green on a host with
  the BimodalLogic checkout; cleanly skipped, never failed, with `BIMODAL_LOGIC_PATH` pointed at a
  nonexistent path).
- No other importer of the moved names exists: `grep -rn "_run_check_certificate\|_resolve_lake\|_resolve_bimodal_logic_path" code/` returns only the helper and that one module.

---

### Phase 2: Candidate enumerator and Tier 1 triangle for the box-free closures [COMPLETED]

**Goal**: A deterministic exhaustive candidate generator plus the leg (i) vs. leg (iii) comparison,
passing for one SAT and one UNSAT box-free closure.

**Tasks**:
- [x] Create `tests/integration/test_certificate_a2_triangle.py` with a module docstring stating
      the ADEQUACY section 7.3 obligation, which leg is novel here (iii, encoding completeness),
      and that legs (i)/(ii) on the fixture corpus remain
      `test_certificate_lean_agreement.py`'s job.
- [x] Add a `_build(premises, conclusions, **overrides)` equivalent of `test_structure.py`'s
      helper (`Syntax` -> `BimodalSemantics` -> `ModelConstraints` -> `BimodalStructure`), driven
      at `back=1, mid=1, fwd=1`.
- [x] Add `_candidates(structure)` yielding every `(WitnessFamily, target_time)` candidate:
      closure sorted deterministically (e.g. by `repr`), labels ranging over all `2**|C|` subsets,
      one `LabelledLasso(back=(b,), mid=(m,), fwd=(f,))` per lasso index in
      `structure.semantics._active_lassos`, `bx` over all Boolean assignments to the `Box` children
      of the closure, and `target_time` over `list(structure.semantics.witness_registry.target_window())`
      (`range(-1, 2)` at these lengths).
- [x] Assert `len(closure) <= 4` per example, so the ADEQUACY bound is machine-checked.
- [x] Add the Tier 1 comparison: count accepted (`status == "countermodel"`) candidates via
      `recheck(family, structure.semantics._premise_formulas, structure.semantics._conclusion_formulas, t)`
      and assert `(accepted_count > 0) == structure.z3_model_status`, with a failure message that
      names which of the two ADEQUACY diagnoses applies (accepted-but-UNSAT = encoding
      incompleteness; none-accepted-but-SAT = encoding unsoundness or a re-checker defect).
- [x] Parametrize over two box-free closures: `[] / ["(q \\Until p)"]` (expected SAT, 1,536
      candidates, accepted > 0) and `["A"] / ["A"]` (expected UNSAT, 24 candidates, accepted == 0). Surface-syntax strings
      are written as Python literals here, so operator backslashes are doubled exactly as in
      `test_structure.py` (`"\\Box A"`, not `"\Box A"`).
- [x] Also assert, for the SAT closures, that `structure.certificate` is not `None` and re-checks
      as a countermodel — the extracted certificate is itself one of the accepted candidates.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: the two box-free closures are asserted to have `|C| = 3` and `|C| = 1`,
yielding 1,536 and 24 candidate re-checks with 52 and 0 accepted, and Z3 verdicts SAT and UNSAT.
These were measured at plan time on this host; confirm them from the test's own run output (print
or assert the exact counts) rather than trusting this plan, and treat a divergence as a finding to
report, not a number to quietly re-baseline.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` -
  new module: `_build`, `_candidates`, Tier 1 test

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -v`
  green, both parametrized cases, in under ~10 s total.
- The enumerated candidate count for each closure equals the expected `(2**|C|)**(3*lassos) * 2**boxes * 3`, asserted in the test.

---

### Phase 3: Tier 1 for the single-box closure [COMPLETED]

**Goal**: The same exhaustive comparison over a closure containing a `Box`, exercising the
witness-lasso and `bx` dimensions of the candidate space.

**Tasks**:
- [x] Add the `["\\Box A"] / ["B"]` closure to the Tier 1 parametrization (`|C| = 3`, one `Box`,
      two active lassos: main plus one witness lasso).
- [x] Confirm the generator picks up the second lasso from `semantics._active_lassos` and the
      `bx` dimension from the closure's `Box` children, with `bx` keyed on `Box.child` — matching
      both `extract_certificate` and `_box_faithful`'s `family.bx_of(f.child)`.
- [x] Mark this case with the already-registered `slow` marker (`code/pyproject.toml`); do not
      introduce a new marker.
- [x] Record the measured wall-clock time of this case in the test's own comment, next to the
      candidate count, so a future slowdown is visible against a stated baseline.
- [x] **Note (structural, not a task-list item)**: rather than duplicating the Phase 2 test
      body, extracted it into a shared module-level `_assert_exhaustive_triangle_agrees` helper
      called by both `TestExhaustiveTriangleBoxFree` (unmarked, parametrized) and the new
      `TestExhaustiveTriangleWithBox` (single `slow`-marked test) -- the box case has no
      sibling to parametrize alongside, so its own class keeps the marker off the box-free
      cases.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: this closure is asserted to enumerate 1,572,864 candidate re-checks
(`512**2 * 2 * 3`) with 96 accepted and a Z3 verdict of SAT, taking ~11.5 s. Confirm all four from
the run itself; if the runtime exceeds roughly a minute on the implementing host, note it and
consider the report's atoms-only generator as a follow-up rather than silently reducing scope.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` -
  third parametrized closure, `slow` marker

**Verification**:
- The single-box case passes and reports `accepted > 0` with `z3_model_status is True`.
- `pytest ... -m "not slow"` deselects exactly this case and leaves the Phase 2 cases running.

---

### Phase 4: Tier 2 bounded Lean cross-check [COMPLETED]

**Goal**: Leg (ii) agreement on a bounded, deterministic sample of candidates plus on the live
Z3-extracted certificate, under the same skip discipline as the existing Lean module.

**Tasks**:
- [x] Import the Phase 1 helper and apply the same skip so the Lean tests skip cleanly (never
      fail) without a BimodalLogic checkout or `lake`. **Deviation**: applied as a
      `@pytest.mark.skipif(SKIP_REASON is not None, ...)` decorator on `TestBoundedLeanCrossCheck`
      itself, not as a module-level `pytestmark` -- a module-level skip would also skip Tier 1's
      exhaustive completeness comparison, directly contradicting this same plan's own Testing &
      Validation checklist ("the Tier 1 completeness comparison still runs and still passes" with
      `BIMODAL_LOGIC_PATH=/nonexistent`), which this class-scoped form satisfies and a
      module-level one would not.
- [x] Add a named module constant for the per-class sample size (`LEAN_SAMPLE_PER_CLASS = 5`)
      with a comment citing the ~2.2 s per-invocation cost and the existing Lean module's total
      as the budget being matched.
- [x] For each closure: take the first `LEAN_SAMPLE_PER_CLASS` accepted candidates and a
      deterministically strided sample of the same size from the rejected candidates; serialize
      each via `WitnessFamily.to_json(premises, conclusions, target_time)` and assert
      `run_check_certificate(payload, timeout)["status"]` equals the Python re-checker's status.
      Selection must be reproducible across runs (fixed enumeration order, fixed stride — no
      unseeded randomness). Verified reproducible across two consecutive runs.
- [x] For each SAT closure: one additional invocation on `structure.certificate`'s serialization
      at `structure.target_time`, asserting Lean also answers `countermodel` — closing the gap the
      production fail-fast guard leaves (it calls the Python `recheck` only).
- [x] On a `rejected` disagreement, compare the `failed[].condition` sets and assert a non-empty
      intersection, matching `TestPythonRecheckerAgreesWithLean`'s existing convention.
- [x] Assert in the failure messages that the Lean predicates are the contract (ADEQUACY section
      5.3), so a disagreement is attributed Python-side by default.
- [x] **Note (Scope Hypothesis follow-up)**: measured total for this class alone, all three
      cases, ~58s (6s/15s/36s) — within the ~50-60s estimate below, so `LEAN_SAMPLE_PER_CLASS`
      was not lowered. Most of the single-box case's ~36s is two Python-side enumeration passes
      over its 1,572,864 candidates (needed to fix a deterministic stride before sampling), not
      the ~11 Lean subprocess invocations themselves; an early-exit once both quotas are filled
      was added to `_sampled_candidates` to trim this, with modest effect (the strided rejected
      sample's last index falls ~80% into the enumeration regardless).

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: the Lean leg is budgeted at roughly 11 invocations per SAT closure sample
set (5 accepted + 5 rejected + 1 extracted certificate) and fewer for the UNSAT closure, about
22-25 invocations and ~50-60 s total at the measured ~2.2 s each. Time the actual run; if it
exceeds the existing Lean module's runtime by more than about 3x, lower
`LEAN_SAMPLE_PER_CLASS` rather than accepting the regression.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` -
  Tier 2 tests, sample-budget constant

**Verification**:
- The whole new module is green with the checkout present, and its Lean tests report as skipped
  (not failed) with `BIMODAL_LOGIC_PATH=/nonexistent`.
- Two consecutive runs select the same sampled candidates (reproducible ids in `-v` output).

---

### Phase 5: Documentation and full-suite verification [COMPLETED]

**Goal**: The A2 deciding test is recorded as standing where the adequacy argument is stated, the
stale claim about which legs are covered is corrected, and the whole bimodal suite is green.

**Tasks**:
- [x] Update `bimodal/docs/ADEQUACY.md` section 7.3 to record the deciding test as standing in
      this repository's suite, naming `tests/integration/test_certificate_a2_triangle.py`, the
      three closures, and the two-tier structure (exhaustive Python; bounded Lean) — mirroring
      section 7.2's existing "standing in this repository's suite" wording for A0.
- [x] Correct `test_certificate_lean_agreement.py`'s docstring claim that it discharges "Section
      7.3's A2-triangle test's re-checker leg": state that it covers legs (i)/(ii) on the fixture
      corpus and point at the new module for the full triangle including leg (iii).
- [x] Add the new module to `bimodal/tests/README.md` (the file does enumerate test modules, in
      the `integration/` table).
- [x] Run the full bimodal suite and the repo test suite gate. **Finding, not caused by this
      task**: `bimodal/tests/integration/test_iterate.py::TestLiveIteration::
      test_iterate_three_yields_three_pairwise_distinct_certificates` fails
      (`assert 0 == 2`) on this working tree. Confirmed via `git log` this is task 189's own
      deliberately-red reproduction test (`task 189 phase 1: baseline, reproduction, and failing
      live test`, committed mid-way through this task's own phases on the shared working tree,
      per the dispatch's Territory concurrency note) for an unrelated iterator defect
      (`fix_shared_iterator_is_world_assumption`) still being fixed by that task, not this one.
      With that single foreign test deselected, the full bimodal suite (374 tests, including
      every test this task added) and the full `code/tests/` repo gate (645 passed, 5 skipped)
      are both green.

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - section 7.3 standing-test record
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  docstring scope correction
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - module listing (only if the file
  already enumerates modules)

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green.
- `PYTHONPATH=code/src pytest code/tests/ -v` green.
- No task-number references introduced outside `specs/**`
  (`bash .claude/scripts/check-task-references.sh` clean for the touched files).

---

## Testing & Validation

- [ ] `test_certificate_a2_triangle.py` green in full, and green with `-m "not slow"` (fewer cases,
      no failures).
- [ ] Lean-dependent tests skip cleanly with `BIMODAL_LOGIC_PATH=/nonexistent`, and the Tier 1
      completeness comparison still runs and still passes in that configuration.
- [ ] `test_certificate_lean_agreement.py` unchanged in outcome after the Phase 1 helper
      extraction.
- [ ] Full bimodal suite green: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.
- [ ] Repo suite green: `PYTHONPATH=code/src pytest code/tests/ -v`.
- [ ] Each example's asserted candidate count matches the closed-form
      `(2**|C|)**(3*lassos) * 2**boxes * len(target_window)`.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
  (new): the A2-triangle standing test.
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (new): shared
  `lake exe check_certificate` invocation and skip-resolution helper.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
  (modified): imports the helper; docstring scope corrected.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (modified): section 7.3 records the
  deciding test as standing.
- `specs/191_a2_triangle_encoding_completeness_test/summaries/01_*-summary.md`: implementation
  summary, including the observed triangle verdicts per closure.

## Rollback/Contingency

All changes are additive test and documentation edits with no production-code surface, so rollback
is per-phase `git revert` of that phase's own commit — no working-tree discard is required, and no
snapshot-then-rollback recipe applies. If a defensive checkpoint is wanted before Phase 1's
cross-file helper move, use `bash .claude/scripts/git-snapshot.sh 191 --no-revert` (durable,
non-reverting); do not invoke `git-snapshot.sh` in its default reverting mode here.

Contingency if the triangle actually fails (Z3 and the enumeration disagree on any closure): stop,
do not weaken the assertion or drop the closure. Record the disagreement, the closure, the
accepted-candidate count, and the Z3 verdict in the implementation summary and report it as a
finding — per ADEQUACY section 7.3 the direction of the mismatch localizes the defect (accepted
candidates with UNSAT = encoding incompleteness; no accepted candidates with SAT = encoding
unsoundness or a re-checker defect), and diagnosing or fixing the encoder is outside this task's
scope.
