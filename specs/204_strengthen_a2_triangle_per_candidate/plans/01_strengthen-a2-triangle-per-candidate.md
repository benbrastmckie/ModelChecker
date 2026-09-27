# Implementation Plan: Per-Candidate A2-Triangle Leg (i)/(iii) Comparison

- **Task**: 204 - strengthen_a2_triangle_per_candidate
- **Status**: [IMPLEMENTING]
- **Effort**: 6.5 hours
- **Dependencies**: 195 (research complete; its implementation phase is concurrent — see Risks)
- **Research Inputs**: `specs/204_strengthen_a2_triangle_per_candidate/reports/01_strengthen-a2-triangle-per-candidate.md`
- **Artifacts**: plans/01_strengthen-a2-triangle-per-candidate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Replace the one-bit aggregate leg (i)/(iii) comparison in
`bimodal/tests/integration/test_certificate_a2_triangle.py` with a per-candidate comparison, by
building a solver-free evaluator for the encoder's already-emitted clause list
(`structure.model_constraints.all_constraints`) and pinning it to each enumerated candidate's own
data. The evaluator is built as a **compile-once, interpret-many** pass: the Z3 `BoolRef` trees are
walked exactly once per built `structure` into Python closures over an interned integer atom
index, so the per-candidate hot loop performs only list indexing and native boolean operations —
matching `recheck`'s own ~6.15us/candidate cost profile instead of paying a Z3 Python/C-API call
per AST node per candidate. The new machinery lands in its own test-support module with its own
unit tests (TDD), is wired into the shared Tier 1 helper with first-divergence reporting, and the
final tier placement of each of the six parametrized Tier 1 cases is decided by a measurement
taken under CI's exact invocation shape (`-n 4 -q --timeout=300 --timeout-method=thread`) rather
than an estimate.

### Research Integration

The report's four load-bearing findings drive the phase structure directly:

- **Finding 4/5 (closed operator set)**: the emitted clause list uses only `And`, `Or`, `Not`,
  `Implies`, `BoolRef == BoolRef`, and `AtMost`, over three atom families (`lab_{lasso}_{slot}_{repr}`,
  `bx_{repr}`, `sel_{t}`). Phase 1 implements exactly these and raises loudly on anything else;
  Phase 2 adds a machine-checked inventory assertion so the closed set is pinned, not assumed.
- **Finding 6 (candidate determines every atom)**: the assignment builder is the exact inverse of
  `extract_certificate` (`core.py:352-412`) — `bit` from `LabelledLasso.label`, `guess` from
  `family.bx`, `sel` one-hot from `target_time`. Phase 2 implements it and adds the
  extracted-certificate round-trip as its strongest self-check.
- **Finding 7 (compile, do not interpret)**: the single design decision the report adds beyond
  task 195's estimate. Phase 1 builds the compiler; the interning of atom names to integer indices
  (the report's own fallback mitigation) is adopted up front rather than held in reserve, since it
  costs almost nothing at compile time and removes string hashing from the hot loop.
- **Finding 8/9 (CI admits `slow` unconditionally)**: `slow` is not deselected by
  `.github/workflows/tests.yml:208`, so every existing tier boundary in this module is a
  local-iteration boundary only and the real constraint is the 300s-per-test ceiling under `-n 4`.
  Phase 4 measures against that exact shape.
- **Finding 10**: Tier 2 (`TestBoundedLeanCrossCheck`) is untouched; Phase 5 verifies its
  clean-skip discipline still holds rather than assuming it.

### Prior Plan Reference

No prior plan for this task. Task 195's plan
(`specs/195_research_encoder_spec_proof_routes/plans/01_encoder-spec-proof-routes.md`) is a
documentation-plus-one-test plan and is **not** a template for this one; its only relevance here is
the concurrent-territory risk recorded below.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md was loaded.

## Goals & Non-Goals

**Goals**:
- A per-candidate assertion that, for every enumerated candidate, "every emitted constraint
  evaluates true under the candidate's pinned assignment" iff `recheck`'s verdict is
  `"countermodel"`, failing on the **first** divergence with the family, target time, the
  disagreeing side, and the specific constraint that diverged.
- A solver-free evaluator whose per-candidate cost is in the same order as `recheck`'s, achieved by
  construction (compile-once) rather than hoped for and measured after.
- Loud failure (never silent defaulting) on any atom the assignment builder does not populate, any
  operator outside the closed set, and any atom-name collision.
- Final tier placement for all six Tier 1 parametrized cases justified by a recorded measurement
  taken under CI's exact invocation shape, with the measured figures written into the module
  docstring the way the existing ones are.
- Tier 2's clean-skip discipline verified intact.

**Non-Goals**:
- Diagnosing any divergence the strengthened test finds. Per the dispatch, a genuine divergence is
  reported as a finding (incompleteness vs. unsoundness, per `ADEQUACY.md` section 7.3) and the
  encoder is not touched.
- Weakening or removing the existing aggregate assertion. It is **retained**: pinned evaluation
  checks the emitted *constraint set*, whereas `structure.z3_model_status` is the only place the
  real Z3 *search* verdict is checked. These are different facts and both stay asserted.
- Editing `ADEQUACY.md` or `A2_GAP.md`. Task 195's concurrent implementation is rewriting exactly
  the aggregate-vs-per-candidate sections of both documents (its Phases 2-4); a second concurrent
  editor of those sections is the collision most worth avoiding. Recorded as a follow-up instead.
- Reducing the enumeration's scope or sampling within a case, unless Phase 4's measurement forces
  it — and then as a narrowing of one case's scope, never as a weakening of the assertion.
- Any change to Tier 2 (`TestBoundedLeanCrossCheck`) or to the Lean cross-check path.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Concurrent task 195 declares `test_certificate_a2_triangle.py` in its `file_scope` while `[IMPLEMENTING]` on the same working tree | H | M | Per `context/contracts/territory.md`: re-read the file immediately before every edit; stage only this task's own hunks (explicit file lists, never a directory/glob `git add`); never run `git-snapshot.sh` in reverting mode; treat an unexpected failure outside this task's own file set as possibly a sibling's in-flight edit and STOP and report a foreign commit or modification rather than dismissing it. Most of this task's new code lands in **new** files, which minimizes the shared surface to the Tier 1 helper only. |
| Per-candidate cost still pushes the 10.5M-candidate boxed case (`~64.5s` today) past CI's 300s ceiling under `-n 4` | H | M | Phase 4 measures before committing to a tier; the compile-once + integer-interned design (Phase 1) is the primary cost mitigation; if measurement still threatens the ceiling, narrow that one case's scope (a named, deterministic stride over the enumeration) rather than weakening the assertion. |
| An atom referenced by a constraint is not populated by the assignment builder, and is silently treated as unconstrained | H | L | Coverage is checked **once per structure** (not per candidate): the compiler's interned atom-name set must be exactly covered by the builder's produced key set, else raise. Any unwritten index in the hot path remains a sentinel and raises. |
| `AtMost`'s bound argument position is mis-read (`z3.AtMost(*sels, 1)`) | M | M | Phase 1 unit-tests `AtMost` directly against small solver-backed cases, mirroring `test_witness_constraints.py`'s existing `TestSelectorConservativity` (`:111-138`). |
| Two distinct closure formulas share a `repr`, colliding in the `lab_`/`bx_` atom names | M | L | The builder raises on any attempt to write an already-populated key with a *different* value; a collision therefore fails loudly at build time instead of producing a wrong evaluation. |
| A genuine divergence is found and scope balloons into encoder diagnosis | M | L | Out of scope per the dispatch and Non-Goals: report the first divergence as a finding with the localizing detail and stop. |
| Measuring the full CI-shaped `code/` run is itself expensive | L | H | Measure the module alone under `-n 4` first for iteration; take the authoritative figure for the two boxed cases from `--durations=0` output of one CI-shaped run, not from repeated full runs. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is a strict chain: the evaluator
must exist before the assignment builder can be validated against real constraints, both must
exist before the comparison can be wired in, and the wiring must exist before it can be measured.

---

### Phase 1: Compile-once pinned evaluator core [COMPLETED]

**Goal**: A self-contained, test-support module that compiles a list of Z3 `BoolRef` constraints
into a reusable Python evaluator over an interned integer atom index, handling exactly the six
operators the encoder emits and raising loudly on anything else.

**Tasks**:
- [x] Write `tests/unit/test_pinned_eval.py` FIRST (RED), over small hand-built Z3 formulas — no
      `BimodalStructure` needed:
  - [x] each of `And`, `Or`, `Not`, `Implies`, `a == b` (two `BoolRef`s), `AtMost(*xs, k)` evaluates
        correctly for both polarities, including nesting and the 0-arg/1-arg `And`/`Or` degenerate
        forms and Z3's `true`/`false` constants
  - [x] `AtMost` bound semantics pinned against a small solver-backed cross-check, mirroring
        `test_witness_constraints.py`'s `TestSelectorConservativity` (`:111-138`), so the bound's
        argument position cannot be silently wrong
  - [x] an unsupported node (e.g. `z3.Ite`, an arithmetic term, a quantifier) raises a named error
        identifying the offending declaration, never returns a default
  - [x] an atom index left unpopulated raises rather than being read as `False`
- [x] Create `tests/_pinned_eval.py` (sibling of the existing `tests/_lean_check.py` helper):
  - [x] `compile_constraints(constraints) -> CompiledConstraints` walking each `BoolRef` tree
        exactly once, interning every leaf atom's Z3 declaration name into
        `atom_index: Dict[str, int]` and emitting one Python callable per top-level constraint that
        takes the assignment sequence and returns `bool`
  - [x] `CompiledConstraints.evaluate_all(assignment) -> bool` (short-circuiting) and
        `CompiledConstraints.first_false(assignment) -> Optional[int]` returning the index of the
        first constraint that evaluated false, for divergence reporting
  - [x] `CompiledConstraints.describe(index) -> str` giving the offending constraint's text, called
        only on the failure path so it costs nothing in the hot loop
- [x] Run the new unit tests to GREEN; commit.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` - NEW: the compiler and
  evaluator
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` - NEW: unit tests for
  all six operators, the loud-failure paths, and the `AtMost` bound

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py -v`
  passes, with the unsupported-operator and unpopulated-atom cases asserted via `pytest.raises`.
- No Z3 API call appears inside `evaluate_all`/`first_false` (confirmed by diff read-through: only
  the compile path touches `decl`/`arg`/`num_args`/`kind`).

---

### Phase 2: Candidate-to-assignment builder, with coverage and inventory guards [COMPLETED]

**Goal**: Build the pinned assignment for a candidate directly from its own data — the exact
inverse of `extract_certificate` — and prove against the real constraint list that the assignment
is total over every referenced atom and that the operator inventory is closed.

**Tasks**:
- [x] Extend `tests/unit/test_pinned_eval.py` (RED first) with structure-backed cases built through
      the same `Syntax -> ModelConstraints -> BimodalStructure` pipeline the integration module's
      `_build` uses:
  - [x] **Operator inventory**: for each Tier 1 case's settings, every node in
        `structure.model_constraints.all_constraints` has a declaration in the closed six-operator
        set and every leaf matches one of the three atom-name families — pinning Finding 4/5
        mechanically instead of trusting it
  - [x] **Coverage**: the builder's produced key set is exactly `compile_constraints(...).atom_index`'s
        key set (neither an unpopulated referenced atom nor a stray key), asserted once per structure
  - [x] **Round-trip (the strongest self-check)**: for an expected-SAT case, the assignment built
        from `structure.certificate` / `structure.target_time` (which came from a genuinely
        satisfying Z3 model) makes `evaluate_all` return `True`. A `False` here means the evaluator
        or builder is wrong, not that the encoder is.
  - [x] **Collision guard**: writing an already-present key with a different value raises
- [x] Implement in `tests/_pinned_eval.py`:
  - [x] `atom_names_for(structure, family, target_time)` / `assignment_for(...)`:
        `lab_{lasso}_{slot}_{formula!r}` from `family.lassos[j].label(t)` for each
        `lasso = structure.semantics._active_lassos[j]` and each slot of
        `back + mid + fwd` order; `bx_{child!r}` from `family.bx_of(child)` for every `Box` member
        of the closure; `sel_{t}` as `(t == target_time)` for every `t` in
        `registry.target_window()`

**Deviation (confirmed by the coverage assertion this phase itself requires)**: the literal
"every slot × every closure formula" construction above produces *stray* keys the compiled
constraints never reference -- e.g. a plain `Atom` is never directly bound at a position, only
as an `Untl`/`Snce` neighbour or a premise/conclusion target, so `bit(lasso, t, Atom(...))` is
not emitted for every slot. The coverage assertion (below) caught this immediately as a
missing=[] / stray=[...] mismatch when the literal construction was tried. Fixed by inverting
the direction: `PinnedAssignmentBuilder` parses each of `atom_index`'s own key strings into a
typed resolver once per structure (mirroring `compile_constraints`'s own compile-once split on
the assignment side), so the produced key set is exactly `atom_index`'s key set by construction,
never a superset. This is the pre-edit-gate contract in action -- the hypothesis failed its own
probe and was corrected rather than the assertion being loosened. The collision guard moved with
it: it now fires at construction time, when two closure formulas' `repr()` strings collide,
rather than at a per-candidate write.
  - [x] a `PinnedAssignmentBuilder` bound once per structure that holds the compiled
        `atom_index` and writes each candidate's values into a preallocated list, so the
        per-candidate path allocates no dict and hashes no strings
- [x] Run to GREEN; commit.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts that the operator set is exactly the six named in the
report's Finding 4 and the atom families exactly the three in Finding 3, and that slot-level
memoization (`registry.wrap`) makes an assignment built from `target_window()` alone total over
the wider `_coherence_window` references. All three are hypotheses from the research report, not
facts: confirm each at implementation time by the machine-checked inventory and coverage
assertions above. If the inventory assertion finds a seventh operator or a fourth atom family,
extend Phase 1's evaluator rather than loosening the assertion.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` - add the assignment builder
  and the per-structure coverage check
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` - add the inventory,
  coverage, round-trip, and collision-guard tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py -v`
  passes, including the round-trip case returning `True`.
- The coverage assertion passes for every Tier 1 settings combination (`back=mid=fwd=1` and
  `back=2, mid=1, fwd=2`, box-free and boxed closures).

---

### Phase 3: Wire the per-candidate comparison into the Tier 1 helper [NOT STARTED]

**Goal**: The Tier 1 body compares legs (i) and (iii) candidate by candidate, failing on the first
divergence with enough detail to diagnose it, while retaining the existing aggregate assertions.

**Tasks**:
- [ ] Re-read `tests/integration/test_certificate_a2_triangle.py` immediately before editing
      (concurrent task 195 declares it in its `file_scope`).
- [ ] In `_run_exhaustive_triangle` (`:157-171`), compile once before the loop
      (`compile_constraints(structure.model_constraints.all_constraints)`), bind the assignment
      builder once, and inside the existing loop:
  - [ ] compute `pinned = compiled.evaluate_all(builder.assign(family, target_time))`
  - [ ] compare against `verdict["status"] == "countermodel"`; on inequality, raise immediately
        with the first-divergence report: the candidate (`family`, `target_time`), which side
        accepted, the offending constraint's text via `describe(first_false(...))` when the
        encoding rejected, `recheck`'s `failed` entries when `recheck` rejected, and the
        incompleteness-vs-unsoundness reading from `ADEQUACY.md` section 7.3
  - [ ] return the pinned-accepted count alongside `(total, accepted)` so the aggregate assertion
        can also cross-check the two counts are equal
- [ ] In `_assert_exhaustive_triangle_agrees` (`:195-244`), assert `pinned_accepted == accepted`
      and keep the existing count, accepted-count, `(accepted > 0) == z3_model_status ==
      expected_sat`, and extracted-certificate assertions unchanged.
- [ ] Keep the failure message's "Report this as a finding -- do not weaken this assertion or drop
      the closure" directive, extended to the per-candidate case.
- [ ] Run the four unconditional box-free cases (`-m "not slow"`) to GREEN; commit (staging only
      this task's own files, explicitly listed).

**Timing**: 1.25 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: This phase assumes the per-candidate biconditional holds for all six Tier 1
cases at their currently recorded accepted counts (52, 0, 926, 0, 96, 5115) — i.e. that
`pinned_accepted == accepted` for each. That is precisely the A2 claim under test and is a
hypothesis, not a fact: confirm by running the cases. A mismatch is the differential firing and is
reported as a finding (Phase 5), not silenced by adjusting an expected count.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` -
  `_run_exhaustive_triangle` and `_assert_exhaustive_triangle_agrees` only; Tier 2 untouched

**Verification**:
- `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -m "not slow" -v`
  passes all four box-free cases.
- A deliberate temporary perturbation (e.g. inverting one candidate's pinned verdict locally,
  reverted immediately) produces the intended first-divergence message — confirming the reporting
  path is reachable and informative, not dead code.

---

### Phase 4: Measure under CI's exact invocation shape and finalize tiering [NOT STARTED]

**Goal**: Decide each Tier 1 case's final tier from a recorded measurement taken under CI's real
invocation, and record the measured figures in the module docstring the way the existing ones are.

**Tasks**:
- [ ] Measure the module alone under the CI flag set, from `code/`:
      `PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -n 4 -q --timeout=300 --timeout-method=thread`
      (`--durations=0` is already in `pyproject.toml`'s `addopts`), recording each case's duration
      before and after the change.
- [ ] Take the authoritative figure for the two `slow` boxed cases from one CI-shaped run over the
      real target set, matching `.github/workflows/tests.yml:208`'s marker expression:
      `PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`,
      reading the boxed cases' lines out of the durations report. Follow
      `context/patterns/bounded-build-waiter.md` if this run is backgrounded.
- [ ] Compute headroom to the 300s ceiling for the `nb=2,fwd=2` boxed case (10,485,760 candidates,
      `~64.5s` before this change) and record the measured multiplier the per-candidate comparison
      actually costs.
- [ ] Decide tiers from the measurement, not from the estimate:
  - [ ] box-free cases stay unconditional if headroom holds
  - [ ] boxed cases stay `slow` (recall `slow` grants **no** timeout exemption — it controls local
        `-m "not slow"` deselection only)
  - [ ] only if the `nb=2,fwd=2` case materially threatens 300s, narrow **that one case's** scope
        with a named, deterministic stride over the enumeration (no unseeded randomness), and say so
        explicitly in its docstring — never weaken the assertion
- [ ] Update the module docstring's Tier 1 paragraph and `TestExhaustiveTriangleWithBox`'s
      docstring with the newly measured wall clock and the measured multiplier, in the same style
      as the existing recorded figures.
- [ ] Run the `slow` cases to GREEN; commit.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: The report predicts the per-candidate cost lands in the same order as
`recheck`'s ~6.15us/candidate, i.e. roughly a 2x multiplier on the boxed `nb=2,fwd=2` case's
`~64.5s`, leaving ample headroom under 300s. That is an estimate carried from research, never a
measured fact: the recorded measurement in this phase is what decides tier placement, and a
materially larger multiplier triggers the narrowing branch above rather than an unconditional
commitment.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` -
  module docstring Tier 1 paragraph, `TestExhaustiveTriangleWithBox` docstring, and marker
  placement only if the measurement forces a change

**Verification**:
- Every Tier 1 case passes under the CI-shaped invocation, each comfortably inside 300s, with the
  measured duration for every case recorded in the docstring.
- No new pytest marker is introduced and no existing marker is removed without a recorded measured
  justification.

---

### Phase 5: Full gate, Tier 2 clean-skip check, and findings report [NOT STARTED]

**Goal**: Close the task against the repository's full gate, confirm Tier 2's clean-skip discipline
is intact, and report any genuine divergence as a finding without diagnosing it.

**Tasks**:
- [ ] Run the full bimodal suite:
      `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal -q --timeout=300 --timeout-method=thread`.
- [ ] Run the repository gate set as CI does (the same two passes as
      `.github/workflows/tests.yml:208` and `:212`) and confirm green.
- [ ] Verify Tier 2 (`TestBoundedLeanCrossCheck`, `:359-522`) still **skips cleanly** (never fails)
      with no BimodalLogic checkout — run it with the checkout unavailable and confirm the
      `skipif(SKIP_REASON is not None, ...)` path reports skips, and that no new import from
      `_pinned_eval` is reachable from Tier 2's collection path.
- [ ] Confirm the diff touches no non-test source file (`semantic/`, `models/` unchanged) — this
      task strengthens a differential, it does not change the encoder.
- [ ] If any genuine per-candidate divergence was observed at any point, record it as a finding in
      the task summary: the candidate, which leg accepted, the offending constraint, and the
      incompleteness-vs-unsoundness reading (`ADEQUACY.md` section 7.3). Do **not** diagnose or
      modify the encoder.
- [ ] Note as follow-up (not done here): the `ADEQUACY.md` section 7.3 / `A2_GAP.md` update
      recording that leg (iii) is now per-candidate, deferred because task 195's concurrent
      implementation owns those sections; and the report's Context Extension Recommendation (a
      short note on the compile-vs-interpret cost distinction for solver-free Z3 clause
      evaluation).
- [ ] Commit.

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- None expected beyond fixes surfaced by the gate; the summary artifact is written by the
  implementation postflight

**Verification**:
- Full bimodal suite green; CI-shaped gate passes green.
- Tier 2 reports skips (not failures) without a BimodalLogic checkout.
- `git diff --stat` against the task's base shows changes confined to the two new test-support/test
  files and the one integration test module.

---

## Testing & Validation

- [ ] `test_pinned_eval.py` covers all six operators in both polarities, `AtMost`'s bound against a
      solver-backed cross-check, Z3 `true`/`false` constants, and the degenerate 0/1-argument
      `And`/`Or` forms.
- [ ] Unsupported operator, unpopulated atom, and atom-name collision each raise a named error
      (asserted via `pytest.raises`), never default silently.
- [ ] Operator-inventory and atom-coverage assertions pass for every Tier 1 settings combination.
- [ ] The extracted-certificate round-trip evaluates the full conjunction to `True` for an
      expected-SAT case.
- [ ] `pinned_accepted == accepted` for all six Tier 1 cases; the existing aggregate assertions
      still hold unchanged.
- [ ] The first-divergence reporting path is exercised at least once (temporary local perturbation,
      reverted) to confirm it is reachable and informative.
- [ ] Every Tier 1 case measured under `-n 4 -q --timeout=300 --timeout-method=thread`, inside 300s,
      with figures recorded in the docstring.
- [ ] Tier 2 skips cleanly without a BimodalLogic checkout.
- [ ] Full bimodal suite and the CI-shaped repository gate both green.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` (new): compile-once constraint
  evaluator plus candidate-to-assignment builder.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` (new): unit tests for
  the evaluator, the builder, and the inventory/coverage/collision guards.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
  (modified): per-candidate leg (i)/(iii) comparison with first-divergence reporting; measured
  figures and tier placement in the docstrings.
- Recorded measurements for all six Tier 1 cases under CI's exact invocation shape (in the module
  docstring, and in the task summary).
- Any observed divergence, reported as a finding in the task summary (undiagnosed, per scope).

## Rollback/Contingency

Every phase commits independently and the change is confined to the test tree, so no production
behavior can regress. To revert, drop the two new files and revert the single integration module —
`git revert` of this task's commits restores the aggregate-only comparison exactly.

Contingencies:
- **Phase 2 inventory assertion finds an operator or atom family outside the closed set**: extend
  Phase 1's evaluator to cover it (and its unit test), rather than loosening the assertion; if the
  new construct is not evaluable without a solver, stop and report — the design premise would be
  falsified and the task needs re-planning rather than a workaround.
- **Phase 4 measurement shows the 10.5M-candidate case cannot fit 300s even with the compiled
  evaluator**: narrow that one case with a named deterministic stride and record the reduced
  coverage explicitly; the assertion itself is never weakened. If even a narrowed form is
  unaffordable, mark that one case `[BLOCKED]` with the measurement as evidence and complete the
  other five.
- **Concurrent task 195 has modified the integration module**: re-read, rebase this task's hunks
  onto the sibling's version, and re-run Phase 3's verification. If a foreign commit or foreign
  uncommitted modification is observed, STOP and report per the dispatch's concurrency note rather
  than resolving it unilaterally.
