# Implementation Plan: Refactor Verification Test Harness

- **Task**: 206 - Refactor Verification Test Harness
- **Status**: [NOT STARTED]
- **Effort**: 9.5 hours (plus up to 1.5 hours if Phase 7's contingency branch is taken)
- **Dependencies**: task 207 (completed — the `all_constraints` fix this harness's
  `full_constraints` helper now aliases); task 205 (concurrent — owns the trust-boundary /
  checker-promotion decision this plan must not pre-empt)
- **Research Inputs**: `specs/206_refactor_verification_test_harness/reports/01_refactor-verification-test-harness.md`
- **Artifacts**: plans/01_refactor-verification-test-harness.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/standards/status-markers.md`
  - `.claude/context/standards/artifact-management.md`
  - `.claude/context/standards/tasks.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
  - `.claude/rules/git-workflow.md`
- **Type**: python
- **Lean Intent**: false

## Overview

The bimodal verification harness (`code/src/model_checker/theory_lib/bimodal/tests/`) carries one
real piece of duplication (four byte-equivalent `_settings`/`_build` helpers) and one real
performance defect: `_candidates()` iterates `target_window` innermost, so the ~96.5% of
`recheck()`'s per-candidate cost that does not depend on `target_time` — structural, (C1) local
coherence, (C2) fulfilment, (C3) box faithfulness — plus the equivalent `lab_`/`bx_` share of the
pinned evaluator's row build, is recomputed `target_window_len` times per witness family for no
reason. Research measured the fix end-to-end against the real code paths: **110.89s → 32.31s
(70.9% reduction, 3.43x)** on the widest boxed Tier 1 case, with
`total`/`accepted`/`pinned_accepted` **bit-for-bit identical** (10,485,760 / 5,115 / 5,115).
Definition of done: the duplication is gone, the amortization is structural (not an incidental
memoization riding on generator order), before/after numbers are measured under CI's exact
invocation shape on the same host and recorded in place, and every preserved invariant below is
still green across the bimodal suite, the four-theory gate, and the repository-wide target set.

### Research Integration

The research report (F1–F10) is integrated as follows, including its three *negative* findings,
which this plan adopts as decisions rather than re-opening:

- **F1 → Phase 2.** Four byte-equivalent `_settings`/`_build` helpers (in
  `tests/integration/test_certificate_a2_triangle.py`, `tests/integration/test_search_period_coverage.py`,
  `tests/unit/test_structure.py`, `tests/unit/test_pinned_eval.py`) are genuine, removable
  duplication.
- **F2 → Phase 2 (declined route, recorded).** The three grids (`_GRID`, `_A0_SWEPT_GRID`, the
  A2-triangle parametrize table) each pin an independent property and are **not** merged. The
  dispatch also names `tests/unit/test_witness_registry.py` as a site restating grid
  configurations; direct read shows it constructs `WitnessRegistry(back=…, mid=…, fwd=…)`
  ad hoc per unit test with no `_settings`/`_build` helper and no shared grid table — see
  Phase 2's Scope Hypothesis, which requires this be confirmed mechanically before the phase
  closes.
- **F3 → Phase 2 (declined route, recorded).** Tier membership expressed as docstring prose +
  `slow` marker + `BIMODAL_LOGIC_PATH` `skipif` is three *mechanisms* pytest requires at three
  decision points, not one fact restated. No declarative tier registry is built.
- **F4 → Phase 2 (declined route, recorded, with coordination note).** `_pinned_eval.py` stays
  inside `tests/`, matching its own sibling `_lean_check.py`. The promotion implication (natural
  destination alongside `certificate.py` in `semantic/`, with a narrowed public surface;
  today's explicit `__all__` already eases that move) is *stated for coordination*, not decided
  here.
- **F5 → Phase 1.** The authoritative numbers reproduce (111.85–113.36s standalone on this host
  vs. the CI-shaped 123.29s on record); Phase 1 re-establishes the baseline under the CI shape
  before any edit.
- **F6 → Non-Goals.** Fixture-sharing of solved structures (~0.024s build) and cross-configuration
  compiled-evaluator caching (~0.0056s compile) are **rejected** for the 300s-ceiling problem:
  measured at 0.02% of the widest case's cost, and the single place fixture-sharing would apply
  never executes in CI (no workflow sets `BIMODAL_LOGIC_PATH`).
- **F7/F8/F9 → Phases 3, 4, 5.** The measured algorithmic fix, split across the production-code
  extraction (Phase 3), the pinned-evaluator split (Phase 4), and the structural loop restructure
  (Phase 5).
- **F10 → Phases 6 and 7.** The scheduling route is a *decision gate* measured after the fix,
  not a parallel option; and if taken, it must ship with a freshness check, never a bare
  `performance` marker (which is currently a complete CI no-op).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch; ROADMAP.md was not consulted.

## Goals & Non-Goals

**Goals**:

- Remove the four byte-equivalent `_settings`/`_build` helpers in favor of one shared
  `tests/_build_support.py`, updating all call sites.
- Record, in place, the three organization routes deliberately declined (grids stay separate,
  tier gating unchanged, `_pinned_eval.py` stays in `tests/`) with the reason each was declined,
  plus the coordination note on what a future checker promotion would imply for
  `_pinned_eval.py`'s location and public surface.
- Land the measured algorithmic amortization: a `_recheck_family` extraction in
  `semantic/certificate.py`, a family-only/target-time split plus per-family base row in
  `tests/_pinned_eval.py`, and an explicit family-outer / `target_window`-inner enumeration in the
  harness.
- Measure before and after under CI's exact invocation shape, on the same host, and report both
  numbers; record them in the module docstrings that already carry measured numbers.
- Decide the scheduled-run question (F10) on the *post-fix* measurement, and implement it with a
  freshness check only if the measured headroom is still judged inadequate.
- Keep the bimodal suite, the four-theory gate, and the repository-wide target set green.

**Non-Goals**:

- The trust boundary between testing and formal verification, and whether Tier 2 is promoted to
  an output gate. Owned by a separate task. This plan preserves Tier 2's clean-skip behaviour
  exactly as it stands and makes no promotion decision.
- Moving `_pinned_eval.py` out of the test tree. Explicitly deferred (F4); the coordination note
  is written, the move is not made.
- Merging the three grids into one declarative registry (F2), or replacing pytest's
  marker/`skipif` mechanics with a home-grown tier registry (F3).
- Fixture-sharing of solved structures and cross-configuration compiled-evaluator caching as
  routes to the 300s-ceiling problem (F6, measured at 0.02% of the cost). Fixture-sharing remains
  a legitimate, independent, much lower-priority local-developer-experience cleanup; it is not
  done here.
- Any narrowing of any enumeration. No candidate is skipped, no stride is introduced, no closure
  is dropped. Every count assertion keeps its current value.
- Diagnosing the encoder, weakening any assertion, or touching the `certificate` wire format.

**Preserved invariants (hard requirements, from the dispatch — each phase's Verification section
re-checks the ones it could plausibly break)**:

1. Tier 2 (`TestBoundedLeanCrossCheck`, `test_certificate_lean_agreement.py`,
   `test_semantics_core.py`'s Lean section) degrades to a **clean skip** — never a failure, never
   a silent pass — without a BimodalLogic checkout. `_lean_check.py`'s `SKIP_REASON` /
   `PROTOCOL_FAILURE` split stays intact.
2. The `timeout is False` assertions in the A0 standing tests (`tests/unit/test_structure.py`'s
   `TestA0FrameClassStandingTest` over `_A0_SWEPT_GRID`) and in
   `tests/integration/test_search_period_coverage.py`'s grid pins stay, unchanged: they exist so
   an inconclusive solver run cannot pass as a genuine UNSAT.
3. The retained **aggregate** assertion in `_assert_exhaustive_triangle_agrees`
   (`(accepted > 0) == structure.z3_model_status == expected_sat`) stays alongside the
   per-candidate comparison: it is the only check of the real Z3 search verdict as distinct from
   the pinned constraint-set evaluation.
4. `_run_exhaustive_triangle` still raises on the **first** per-candidate divergence, with its
   current incompleteness/unsoundness attribution and its current message text's substance.
5. `_sampled_candidates` still selects the **same** candidates (same fixed enumeration order,
   same stride derived from the same exact `total_rejected`) — determinism is part of what Tier 2
   establishes, not an implementation detail.
6. `_candidates`' `len(closure) <= 4` ADEQUACY-bound assertion stays, on every call.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Extracting `_recheck_family` out of `recheck()` changes behaviour for a production caller (the runtime fail-fast guard, `iterate.py`, `semantic/model.py`, `semantic/symmetry.py`, `semantic/core.py`) | H | L | Pure extract-method: `recheck()`'s signature, return shape, and first-failure ordering unchanged. Phase 3 adds a dedicated equivalence test *before* any caller is rewired, and runs the full gate in-phase (Tier `full`). |
| Amortization silently changes a verdict (a candidate accepted/rejected differently) | H | L | The existing tests already pin `expected_total`/`expected_accepted` and assert `pinned_accepted == accepted`; an unchanged-green suite **is** the bit-for-bit proof. Phase 5 additionally records the three counts explicitly before and after. |
| A per-family cache degrades to zero benefit if iteration order changes later | M | M | Phase 5 makes the amortization **structural** (explicit outer loop over families), not a single-slot memo keyed on `id(family)` riding on the generator's current shape — this removes the failure mode rather than tolerating it. |
| Consolidating `_build` into a shared module perturbs a test that depended on a subtle local difference | M | L | The four helpers are byte-equivalent apart from type annotations and docstrings (verified by direct read); Phase 2 is Tier `interface` and enumerates its dependent set, running the bimodal suite in-phase. |
| Re-measurement is not comparable to the baseline (different host, different marker set, different target set) | M | M | Phase 1 records the *exact* command, host, and marker expression into `specs/206_refactor_verification_test_harness/baselines/`; Phase 6 re-runs that recorded command verbatim on the same host and reports both numbers side by side. |
| A future scheduled-run move repeats the inert `performance`-marker pattern and silently stops running the loudest test in the suite | H | L | Phase 7 is gated behind Phase 6's measurement and, if taken, requires a companion freshness check (the `oracle/check-scan-freshness.sh` precedent) plus the `unstable-watch.yml` scheduled-workflow template — never a bare marker change. |
| A concurrent sibling task edits a shared file in this same working tree | M | M | Re-read every file immediately before editing; stage only this task's own hunks (explicit file lists, never `git add -A`, never a directory/glob pathspec); never run `git-snapshot.sh` in its reverting default mode. See `context/contracts/territory.md`, Cross-Task Territory. |
| A task number leaks into a code docstring while writing the coordination note | M | M | Task numbers are permitted in `specs/**` only. In code and docs, name the durable anchor (e.g. "the separately-tracked checker-promotion decision", `docs/ADEQUACY.md` section 7.3, `docs/SEARCH_COVERAGE.md`), never "task N". See `.claude/rules/no-task-references-in-deliverables.md`. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 2, 3, 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 6, 7 |

Phases within the same wave can execute in parallel.

### Phase 1: Record the CI-shaped baseline before any edit [NOT STARTED]

**Goal**: Reproduce (not re-estimate) the authoritative numbers under CI's exact invocation shape
on this host, on unmodified code, and record the command, the host, and the per-test wall clocks
as a durable comparison point for Phase 6.

**Tasks**:
- [ ] Confirm the working tree is clean for the harness files about to be measured
      (`git status --short -- code/src/model_checker/theory_lib/bimodal`), and confirm no sibling
      task has in-flight edits there; if one does, STOP and report rather than measuring a
      foreign diff.
- [ ] Run CI's exact per-PR gate invocation from `code/`, over the real target set, adding only
      `--durations=25` (which does not change what is executed):
      `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread --durations=25`
      (add `PYTHONPATH=src` only if imports fail; note in the record if it was needed). Source:
      `.github/workflows/tests.yml`'s parallel-pass pytest line.
- [ ] Extract the per-test wall clock for both boxed Tier 1 cases from the durations table:
      `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` (on record: 123.29s / 10,485,760
      candidates) and `test_boxed_closure_enumeration_agrees_with_z3` (on record: 17.77s /
      1,572,864 candidates), plus the widest box-free case (on record: ~1.94s).
- [ ] Record the three counts the widest case establishes (`total`, `accepted`,
      `pinned_accepted`) as read from the test's own pinned expectations — 10,485,760 / 5,115 /
      5,115 — so Phase 5 has an explicit equality target, not an implicit one.
- [ ] Write `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md`
      containing: the verbatim command, whether `PYTHONPATH` was needed, the host identifier,
      total suite wall clock, the three extracted per-test wall clocks, the three counts, and
      whether `BIMODAL_LOGIC_PATH` was set (it is unset in this environment, so Tier 2 is
      expected to skip cleanly — record the observed skip count).
- [ ] Note in the record whether the measured numbers agree with the 123.29s / 17.77s already on
      file. A material divergence is a finding to report, not a number to quietly adopt.

**Timing**: 1 hour (dominated by the suite's own wall clock; expect one full run plus one
confirmatory run of the two boxed cases if the durations table is ambiguous).

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: The baseline is expected to land at 123.29s / 17.77s for the two boxed
cases, within the run-to-run spread research observed (111.85–113.36s standalone, the gap being
`-n 4` worker contention). Confirm by reading the actual `--durations=25` table rather than
assuming; if either number differs by more than ~20%, record the observed value as the baseline
and flag the divergence in the record before proceeding.

**Files to modify**:
- `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` - new; the
  baseline record.

**Verification**:
- The baseline file exists and names the verbatim command, the host, and all three per-test wall
  clocks.
- No source file under `code/` was modified by this phase (`git status --short -- code/` shows
  nothing from this phase).
- Tier 2's skip is observed as a clean skip, not a failure, with `BIMODAL_LOGIC_PATH` unset
  (preserved invariant 1, established at baseline so Phase 5 has something to compare against).

---

### Phase 2: Consolidate the duplicated build helpers; record the declined organization routes [NOT STARTED]

**Goal**: Replace the four byte-equivalent `_settings`/`_build` helpers with one shared
test-support module, and record in place — in the docstrings that already carry this kind of
reasoning — why the grids, the tier-gating mechanism, and `_pinned_eval.py`'s location are
deliberately left as they are.

**Tasks**:
- [ ] Re-read all four call sites immediately before editing (sibling-task concurrency).
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` with `_settings`
      and `_build`, fully type-annotated (the `test_certificate_a2_triangle.py` /
      `test_pinned_eval.py` variants are annotated; `test_structure.py`'s is not — take the
      annotated form). Give it an explicit `__all__`, matching `_pinned_eval.py`'s and
      `_lean_check.py`'s convention for a leading-underscore library-like module inside `tests/`.
      Its docstring states that it is the single home for the pipeline construction order
      (`Syntax -> ModelConstraints -> BimodalStructure`) that four modules previously restated.
- [ ] Update the four call sites to import from it, deleting their local copies:
      `tests/integration/test_certificate_a2_triangle.py`,
      `tests/integration/test_search_period_coverage.py`, `tests/unit/test_structure.py`,
      `tests/unit/test_pinned_eval.py`. Remove any now-unused imports
      (`ModelConstraints`, `Syntax`, `BimodalProposition`, `bimodal_operators`,
      `BimodalSemantics`) left behind in each module — check each individually; several are still
      used for other purposes.
- [ ] Confirm mechanically that `tests/unit/test_witness_registry.py` carries no `_settings`/
      `_build` helper and no shared grid table (see this phase's Scope Hypothesis), and record
      the result. If it does carry one, add it to the call-site list and say so explicitly.
- [ ] Record the declined routes where a reader will meet them, using durable anchors and **no
      task numbers** (see the Risks table's last row):
      - In `tests/integration/test_search_period_coverage.py`'s and `tests/unit/test_structure.py`'s
        docstrings (and the A2-triangle parametrize table's own comment): one sentence each
        stating that this grid is local to the property it pins and is deliberately not merged
        with the other two, naming the property.
      - In `tests/README.md`: a short subsection recording the three declined organization
        routes (grids not merged; tier gating left to pytest's own marker/`skipif` mechanics at
        their three required decision points; `_pinned_eval.py` kept in `tests/` alongside
        `_lean_check.py`) with the reason for each.
      - In `tests/_pinned_eval.py`'s module docstring: the coordination note — if a checker is
        promoted onto the production path by the separately-tracked trust-boundary decision, the
        natural destination is alongside `semantic/certificate.py` with a narrowed public
        surface, and today's explicit `__all__` is what would make that move mechanical. State
        it as an implication for coordination; make no promotion decision and change no location.
- [ ] Commit at each green sub-step (shared module + one call site is already a green sub-step),
      staging explicit file lists only.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Four call sites carry the duplicated helpers
(`test_certificate_a2_triangle.py`, `test_search_period_coverage.py`, `test_structure.py`,
`test_pinned_eval.py`), and `test_witness_registry.py` carries none despite the dispatch naming
it as a restatement site. Confirm both halves mechanically before closing the phase, e.g.
`grep -rn "^def _settings\|^def _build" code/src/model_checker/theory_lib/bimodal/tests/`
returning exactly the new shared module (plus nothing under `unit/`/`integration/`), and a
targeted read of `test_witness_registry.py` confirming its `WitnessRegistry(back=…, mid=…, fwd=…)`
constructions are per-test and ad hoc. If the count differs, state the corrected count and
adjust rather than forcing the hypothesis.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` - new; shared `_settings`/`_build`.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - import shared helpers, delete local copies.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py` - same, plus grid-locality docstring sentence.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - same, plus grid-locality docstring sentence.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` - same.
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` - docstring coordination note only (no code change).
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - declined-routes subsection.

**Verification**:
- Enumerated dependent set builds and passes: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
  green, with the same passed/skipped counts as Phase 1's baseline observed for this subtree.
- `grep -rn "^def _settings\|^def _build" code/src/model_checker/theory_lib/bimodal/tests/`
  returns only `_build_support.py`.
- No task-number reference introduced outside `specs/**`:
  `bash .claude/scripts/check-task-references.sh` clean for the touched paths.
- Preserved invariants 2 and 6 untouched: the `timeout is False` assertions and the
  `len(closure) <= 4` assertion are byte-identical in the diff.

---

### Phase 3: Extract `_recheck_family` in `semantic/certificate.py` [NOT STARTED]

**Goal**: Make `recheck()`'s target-time-independent portion (structural + C1 + C2 + C3)
separately callable, as a pure extract-method with no behaviour change for any of its production
or test callers, so the harness can compute it once per witness family.

**Tasks**:
- [ ] Re-read `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` immediately
      before editing.
- [ ] Add `_recheck_family(family, premises, conclusions)` containing, verbatim and in the same
      order, the body of `recheck()` from `closure = closure_of(premises + conclusions)` through
      the (C3) `_box_faithful` check. It returns either the failure dict `recheck()` would have
      returned, or the data (C4) needs — at minimum the `closure` it computed, so the caller does
      not recompute `closure_of` per candidate. Keep the return shape simple and explicit (e.g.
      `(failure_or_None, closure)`); do not introduce a new public type.
- [ ] Rewrite `recheck()` as a thin composition: normalize `premises`/`conclusions` to lists, call
      `_recheck_family`, return its failure unchanged if present, then apply (C4) `_target_holds`
      and return `{"status": "countermodel", "time": target_time}`. `recheck()`'s signature,
      return shape, first-failure ordering, and every failure message stay byte-identical.
- [ ] Leave `__all__` alone: `_recheck_family` is a leading-underscore internal, consistent with
      `_coherent_at`/`_fulfil_at`/`_box_faithful`/`_target_holds` already being private in this
      module. The harness importing a private sibling is the same access pattern
      `test_certificate_a2_triangle.py` already uses for `semantics._premise_formulas` and
      `semantics._active_lassos`.
- [ ] Add an equivalence test to `tests/unit/test_certificate.py`:
      `recheck(family, premises, conclusions, t)` equals the composition of `_recheck_family` and
      `_target_holds`, over a representative sample covering each failure class (structural,
      local_coherent, fulfilling, box_faithful, target) plus an accepting candidate — so the
      composition is guarded before any caller is rewired.
- [ ] Commit the extraction + equivalence test as one green sub-step.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - extract `_recheck_family`; `recheck()` becomes its composition with (C4).
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py` - new equivalence test.

**Verification**:
- The new equivalence test passes and covers all five failure classes plus the accepting case.
- Full gate set: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
  and `PYTHONPATH=code/src pytest code/tests/ -q` both green.
- Every existing `recheck` caller is unaffected: `iterate.py`, `semantic/model.py`,
  `semantic/core.py`, `semantic/symmetry.py`, and the runtime fail-fast guard exercised by
  `tests/unit/test_structure.py`'s `TestFailFastGuardOnACorruptedCertificate` all pass unchanged.
- The diff contains no logic change — confirm by reading it: moved lines only, plus the new
  composition and the normalization of `premises`/`conclusions` to lists.

---

### Phase 4: Split the pinned evaluator's entries into family-only and target-time groups [NOT STARTED]

**Goal**: Let `PinnedAssignmentBuilder` build a candidate's row as a cached per-family base row
plus a cheap per-`target_time` overlay, instead of re-resolving every `lab_`/`bx_` atom for every
`target_window` position.

**Tasks**:
- [ ] Re-read `tests/_pinned_eval.py` and `tests/unit/test_pinned_eval.py` immediately before
      editing.
- [ ] At construction time, partition `self._entries` into two lists: family-only entries
      (`lab_`, `bx_` — their resolvers ignore `target_time`) and target-time entries (`sel_` —
      `lambda family, target_time: target_time == t`). Do the partition where the resolver kind
      is already known, in `_parse_atom`'s three-family dispatch, rather than by re-inspecting
      the atom-name prefix a second time; the three families are already closed and already raise
      loudly on anything outside them.
- [ ] Add a method that builds the family-only portion of the row once for a given family
      (e.g. `base_row(family) -> Row`), and a method that overlays the `sel_` entries for one
      `target_time` onto a caller-owned row (e.g. `apply_target(row, family, target_time)`).
      Keep the existing `assign(family, target_time)` working with an unchanged signature and
      unchanged result — implemented as `base_row` + overlay — so `build_names`, `check_coverage`,
      and the existing unit tests are untouched in behaviour.
- [ ] Preserve the lasso-count guard (`len(family.lassos) != len(self.active_lassos)` →
      `ValueError`) on the new entry points, not just on `assign`: it must not become reachable-
      only-through-the-slow-path.
- [ ] Update `__all__` if a new name needs exporting, and keep the module docstring's three-closed-
      atom-families contract statement accurate with respect to the new partition.
- [ ] Add unit tests in `tests/unit/test_pinned_eval.py`: (a) `base_row` + `apply_target` produces
      a row **equal** to `assign(family, target_time)` for every `target_time` in a structure's
      window; (b) the partition is exhaustive — every entry lands in exactly one of the two
      groups, and their union is `atom_index`'s full key set (this is the row-level counterpart of
      the existing `check_coverage`/`TestAssignmentCoverage` guard); (c) mutating the base row for
      one `target_time` does not leak into the next (the reuse must not alias `sel_` slots
      across overlays).
- [ ] Commit as green sub-steps: partition + equality test first, then the reuse API.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly two `lab_`/`bx_` resolver kinds are family-only and exactly one
(`sel_`) is target-time-dependent, per `_parse_atom`'s three closed families. Confirm at
implementation time by asserting the partition is exhaustive against `atom_index` (test (b)
above) rather than trusting the prefix inventory — the existing
`TestOperatorInventoryIsClosed`/`TestAssignmentCoverage` tests establish the precedent for
machine-checking this kind of closure claim.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` - partition `_entries`; add base-row / overlay entry points; keep `assign` behaviourally identical.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py` - equality, exhaustive-partition, and no-aliasing tests.

**Verification**:
- Changed module plus its enumerated direct dependents pass:
  `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -q`
  (the latter still on the unmodified hot loop — it must stay green before Phase 5 rewires it).
- `assign()`'s results are unchanged for every `target_time` in the window (test (a)).
- The existing `TestNoZ3ApiCallInHotPath` guard still passes: the new entry points introduce no
  Z3 API call in the hot path.

---

### Phase 5: Restructure the harness enumeration into an explicit family-outer, target-inner loop [NOT STARTED]

**Goal**: Make the amortization structural rather than incidental — an explicit outer loop over
witness families and an inner loop over `target_window`, computing each family's `_recheck_family`
verdict and pinned base row exactly once per family — with the three counts bit-for-bit identical
to the baseline.

**Tasks**:
- [ ] Re-read `tests/integration/test_certificate_a2_triangle.py` immediately before editing.
- [ ] Change `_candidates` (or add a sibling generator) to yield `(family, target_window)` per
      family instead of flattening to `(family, target_time)`, so the loop shape the amortization
      depends on is visible in the generator's own type rather than implied by nesting order.
      Keep `len(closure) <= 4` asserted on every call (invariant 6) and keep reading the
      candidate space's shape from the live search object rather than re-deriving it.
- [ ] Rewrite `_run_exhaustive_triangle` as: for each family, call `_recheck_family` once and
      `builder.base_row(family)` once; then for each `target_time` in the window, apply only
      (C4) `_target_holds` and the `sel_` overlay, compare the two verdicts per candidate, and
      increment `total`/`accepted`/`pinned_accepted`. Every candidate is still individually
      counted and individually compared — nothing is skipped, no stride is introduced.
- [ ] Preserve the first-divergence raise exactly (invariant 4), including both attribution
      branches, `compiled.first_false`/`describe` in the incompleteness branch, the candidate
      index `#{total}`, and the "do not weaken this assertion" instruction. When the family-only
      leg already failed, the per-candidate `recheck`-equivalent verdict must still carry the
      same `failed` entries the current message interpolates.
- [ ] Apply the same restructure to `_sampled_candidates`' two passes, preserving the selection
      **exactly**: same fixed enumeration order, same `total_rejected` count, same stride, same
      chosen candidates, same early break once both quotas are filled (invariant 5). If the
      restructure would perturb the selection in any way, keep `_sampled_candidates` on the flat
      shape and say so explicitly rather than changing which candidates Tier 2 checks.
- [ ] Verify the three counts are unchanged by running the two boxed cases directly and reading
      the pinned expectations they assert (10,485,760 / 5,115 / 5,115 for the widest;
      1,572,864 / 96 for the other). An unchanged-green suite is the bit-for-bit proof; record
      the observed numbers in the commit message anyway.
- [ ] Commit as green sub-steps: box-free cases green first (fast), then the `slow` boxed cases.

**Timing**: 1.5 hours (plus the boxed cases' own wall clock)

**Depends on**: 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: ~96.5% of `recheck`'s per-candidate cost and the `lab_`/`bx_` share of the
row build are eligible for amortization, predicting roughly a 3.4x reduction on the widest case
(research measured 110.89s → 32.31s script-level on this host). This is a hypothesis about *this*
implementation, not a fact: confirm by Phase 6's CI-shaped measurement, and report the actual
ratio whatever it is. A smaller-than-predicted gain is a result to report, not a reason to narrow
the enumeration.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - `_candidates` yields per-family windows; `_run_exhaustive_triangle` and `_sampled_candidates` amortize the family-only work.

**Verification**:
- Full gate set: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
  (including `slow`) and `PYTHONPATH=code/src pytest code/tests/ -q` both green.
- The three counts for both boxed cases are identical to Phase 1's recorded baseline — asserted
  by the tests' own pinned `expected_total`/`expected_accepted` and
  `pinned_accepted == accepted`, which were not edited.
- Invariant 3 confirmed present and unedited in the diff: the aggregate
  `(accepted > 0) == structure.z3_model_status == expected_sat` assertion, with its full message.
- Invariant 4 confirmed: deliberately perturb one candidate's verdict in a scratch copy (not
  committed) to confirm the first-divergence raise still fires with both attribution branches
  intact, then discard the scratch change.
- Invariant 5 confirmed: `_sampled_candidates` returns the same candidates as before — compare
  the selected `(family, target_time)` sequences from a pre-change and post-change run at
  `back=mid=fwd=1`.
- Invariant 1 confirmed: with `BIMODAL_LOGIC_PATH` unset, Tier 2 still skips cleanly (same skip
  count as baseline), never fails.

---

### Phase 6: Re-measure under CI's invocation shape; decide the scheduling question [NOT STARTED]

**Goal**: Report before and after under the same invocation shape on the same host, record both
numbers where this codebase already records measured numbers, and decide on the *measured*
headroom whether a scheduled-run move is still needed. This is a decision gate.

**Tasks**:
- [ ] Re-run Phase 1's verbatim recorded command on the same host, with `--durations=25`.
- [ ] Extract the post-change per-test wall clocks for both boxed cases and the widest box-free
      case; compute the reduction ratio and the headroom against the 300s per-test ceiling, and
      the implied CI-hardware slowdown margin (`300 / measured`).
- [ ] Append the after-numbers to
      `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` as a
      before/after table, stating both numbers explicitly (the dispatch requires both, not just
      the improvement).
- [ ] Update the recorded measurements in place, following this module's own existing convention
      of carrying measured numbers in the docstring: `TestExhaustiveTriangleWithBox`'s docstring
      (both boxed cases, the aggregate-only comparison multiplier, the headroom, and the revised
      CI-hardware slowdown margin that replaces today's ~2.4x), the module docstring's Tier 1
      bullet, and `TestExhaustiveTriangleBoxFree`'s docstring if its numbers moved. Keep the
      existing "if CI wall-clock ever approaches the ceiling, narrow with a named deterministic
      stride — never weaken the assertion" guidance; do not delete the guidance just because the
      margin improved.
- [ ] **Gate criterion** — decide and record explicitly: is the post-fix margin adequate? Adequate
      means the widest case's measured CI-shaped wall clock leaves headroom against the 300s
      ceiling that tolerates CI hardware materially slower than this host, stated as a concrete
      ratio, not as a feeling. Research projects ~36s (~88% headroom, ~8x slowdown tolerance);
      today's 123.29s gives ~59% (~2.4x).
      - **Adequate** → Phase 7 is not taken; close it `[COMPLETED WITH EXCLUSIONS]` with a
        `#### Reasoned Exclusions` record citing this phase's measurement as Evidence.
      - **Inadequate** → take Phase 7.
- [ ] Record the decision, the criterion, and the number it was decided on, in the baseline file
      and in the phase's completion note. A scheduling change is a legitimate outcome; so is
      declining it on the measurement.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The widest case is expected to land near ~36s and the second boxed case near
~5–8s (a linear extrapolation of research's measured 70.9% script-level reduction onto the
CI-shaped numbers, not an independent measurement under `-n 4`). Confirm by the actual durations
table; report the measured values, and if they diverge materially from the projection, say so and
re-decide the gate on the measured number rather than the projection.

**Files to modify**:
- `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` - before/after table and the gate decision.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - recorded measurements in the module and class docstrings.

**Verification**:
- Both before and after numbers are recorded, side by side, for both boxed cases.
- The docstrings' recorded numbers match the durations table this phase produced (no stale
  123.29s / 17.77s left claiming to be current, and no new number recorded that the run did not
  produce).
- The gate decision names its criterion and the measured number it was decided on.
- Full gate set still green after the docstring edits (they are prose, but the phase's tier is
  `full` because the phase's own product is a measurement of the full gate).

---

### Phase 7: Contingency — move the widest case to a scheduled run with a freshness check [NOT STARTED]

**Goal**: Taken **only if** Phase 6's gate found the post-fix margin inadequate. Move the widest
boxed Tier 1 case off the per-PR path to a scheduled run while keeping the second boxed case in
the PR gate — without letting it silently stop running.

**Tasks**:
- [ ] Confirm Phase 6's gate verdict was "inadequate" and quote the measurement that decided it.
      If it was "adequate", do **not** execute this phase: close it
      `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record whose Evidence
      column cites Phase 6's measured wall clock and headroom.
- [ ] Add a dedicated marker (or reuse an existing one only after confirming it is actually
      executed somewhere) and register it in `code/pyproject.toml`'s
      `[tool.pytest.ini_options] markers`. Do **not** reuse `performance`: it is excluded by
      `.github/workflows/tests.yml`'s gating pass and run by no workflow at all, so applying it
      would make the loudest test in the suite silently stop running — worse than the status quo.
- [ ] Add a scheduled, explicitly non-gating workflow following
      `.github/workflows/unstable-watch.yml`'s template (`schedule:` + `workflow_dispatch`,
      non-gating classification) that runs the moved case under the same
      `--timeout=300 --timeout-method=thread` shape.
- [ ] Add a companion freshness check, following `oracle/check-scan-freshness.sh`'s precedent, that
      fails the PR gate when the scheduled run's last recorded result is stale — the condition of
      making this move, not an optional follow-up.
- [ ] Keep the second boxed case (the 1,572,864-candidate one) in the PR gate, as the dispatch
      specifies. Narrow nothing: the moved case still enumerates every candidate on its scheduled
      run.
- [ ] Update `code/docs/core/TESTING_GUIDE.md`'s exhaustive-scan cadence discussion (section 8.8's
      neighbourhood) and the module docstring's tiering discussion to state the new cadence and
      the freshness pairing.

**Timing**: 0 hours if not taken; 1.5 hours if taken.

**Depends on**: 6

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify** (only if taken):
- `code/pyproject.toml` - register the new marker.
- `.github/workflows/` - new scheduled, non-gating workflow.
- `.github/workflows/tests.yml` - exclude the new marker from the gating pass.
- a freshness-check script plus its PR-gate wiring.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - marker application and tiering docstring.
- `code/docs/core/TESTING_GUIDE.md` - cadence decision record.

**Verification**:
- If taken: the moved case is selected by the scheduled workflow's marker expression and
  deselected by the PR gate's — verified with `pytest --collect-only -m <expr>` for both
  expressions, not by inspection.
- If taken: the freshness check fails loudly on a synthetic stale record and passes on a fresh
  one.
- If taken: `code/tests/ci/test_workflow_parity.py` still passes (it constrains how many
  parallel-pass `pytest` lines a workflow file may contain).
- If not taken: the phase heading carries `[COMPLETED WITH EXCLUSIONS]` and a
  `#### Reasoned Exclusions` record citing Phase 6's measurement.

---

### Phase 8: Final verification across the bimodal suite, the four-theory gate, and the repository-wide target set [NOT STARTED]

**Goal**: Confirm nothing regressed anywhere, per the dispatch's explicit verification
instruction, and leave the evidence on record.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` — the
      bimodal suite, including `slow`.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` — the four-theory gate.
- [ ] The repository-wide target set under CI's shape:
      `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
      from `code/`, plus the second, serial pass
      `pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread`.
- [ ] Confirm each preserved invariant (1–6) explicitly, one line each, citing the test or the
      diff that establishes it.
- [ ] Confirm no task-number reference leaked outside `specs/**`:
      `bash .claude/scripts/check-task-references.sh`.
- [ ] Append the final pass/skip/fail counts to the baseline record and note any test whose
      status changed from Phase 1's baseline (there should be none other than the intended
      wall-clock changes).

**Timing**: 1 hour

**Depends on**: 6, 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` - final gate evidence.

**Verification**:
- All three invocations green, with counts recorded.
- The six preserved invariants each confirmed with a named citation.
- `check-task-references.sh` clean.

## Testing & Validation

- [ ] Bimodal suite green including `slow`:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.
- [ ] Four-theory gate green: `PYTHONPATH=code/src pytest code/tests/ -q`.
- [ ] Repository-wide target set green under CI's exact invocation shape, both the `-n 4` pass and
      the `xdist_serial` pass.
- [ ] `total` / `accepted` / `pinned_accepted` unchanged for both boxed Tier 1 cases
      (10,485,760 / 5,115 / 5,115 and 1,572,864 / 96) — the tests' own pinned expectations,
      unedited, are the check.
- [ ] `recheck()`'s behaviour unchanged for every caller, guarded by the new equivalence test plus
      the existing `test_certificate.py`, `test_iterate.py`, `test_structure.py`, and
      `test_semantics_core.py` suites.
- [ ] `PinnedAssignmentBuilder.assign()`'s results unchanged for every `target_time` in the
      window; the entry partition exhaustive against `atom_index`.
- [ ] Tier 2 still skips cleanly with `BIMODAL_LOGIC_PATH` unset, with the same skip count as the
      Phase 1 baseline; if a BimodalLogic checkout is available, Tier 2 also passes and selects
      the same sampled candidates as before.
- [ ] `timeout is False` assertions intact in `TestA0FrameClassStandingTest` and in
      `test_search_period_coverage.py`'s grid pins.
- [ ] The aggregate `(accepted > 0) == structure.z3_model_status == expected_sat` assertion intact,
      with its full message.
- [ ] No task-number reference outside `specs/**`: `bash .claude/scripts/check-task-references.sh`.
- [ ] Before and after wall clocks both reported, measured on the same host under the same
      invocation shape.

## Artifacts & Outputs

- `specs/206_refactor_verification_test_harness/plans/01_refactor-verification-test-harness.md` — this plan.
- `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` — the
  before/after measurement record, the gate decision, and the final gate evidence.
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` — new shared `_settings`/`_build`.
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` — `_recheck_family`
  extraction; `recheck()` as its composition with (C4).
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` — family-only / target-time
  entry partition, base-row reuse, and the coordination note on a future promotion.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` —
  amortized family-outer enumeration; updated recorded measurements.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`,
  `tests/unit/test_pinned_eval.py` — new equivalence, partition, and aliasing tests.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`,
  `tests/unit/test_structure.py`, `tests/README.md` — shared-helper imports and the declined-routes
  record.
- Conditional on Phase 6's gate: a scheduled non-gating workflow, a freshness check, a new marker
  registration, and a `TESTING_GUIDE.md` cadence note.

## Rollback/Contingency

Each phase commits at its own green sub-steps, so the cheapest rollback is `git revert` of the
offending commit range — no working-tree discard needed, and it is the default choice here.

Phase-level fallbacks, in increasing order of retreat:

- **Phase 3 (production code)** is the highest-risk change. If the equivalence test cannot be made
  to pass, or any existing `recheck` caller regresses, revert Phase 3 alone. Phase 4's pinned-
  evaluator amortization stands on its own and delivers roughly the smaller half of the measured
  gain (research measured the `recheck`-only variant at 62.18s and the combined variant at 32.31s
  from a 110.89s baseline), so the task still produces a real, measured improvement without it.
- **Phase 5** is the only phase that can change what the widest tests execute. If the three counts
  move by even one, revert Phase 5 immediately and report the divergence as a finding — do not
  adjust an expected count to match.
- **Phase 2** is behaviour-neutral and independently revertible.
- **Phase 7**, if taken, is revertible by restoring the gating marker expression; the moved case
  returns to the PR gate at whatever wall clock Phase 6 measured.

If an intentional rollback of *uncommitted* work is ever required, take a snapshot first per
`context/contracts/recovery.md`'s rollback rung (including its out-of-scope override flag for the
deliberate whole-tree case) before running the destructive command. For an ordinary defensive
checkpoint before risky work — not a rollback — use `git-snapshot.sh --no-revert`, which is
durable without reverting the working tree.

Because a sibling task may be editing this same working tree: stage explicit file lists only,
never `git add -A` and never a directory or glob pathspec; re-read each file immediately before
editing; and if a foreign commit or foreign uncommitted modification appears, stop and report it
after checking `git log` to confirm the work is not this task's own.
