# Implementation Plan: Task #203

- **Task**: 203 - research_divisor_period_search_coverage
- **Status**: [IMPLEMENTING]
- **Effort**: 4.75 hours
- **Dependencies**: 195 (in flight this same cycle; owns `ADEQUACY.md`, `SETTINGS.md`,
  `A2_GAP.md`, `semantic/core.py`, `tests/unit/test_structure.py`,
  `tests/integration/test_certificate_a2_triangle.py` — Phase 4 below is gated on its edits)
- **Research Inputs**: `specs/203_research_divisor_period_search_coverage/reports/01_divisor-period-search-coverage.md`
- **Artifacts**: plans/01_divisor-period-search-coverage.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The task's own deliverable — a report comparing three routes to fixing the divisor-period
non-monotonicity, with a recommendation and a staged path, explicitly *not* an implementation — is
complete and landed. This plan lands the report's durable conclusions where a future reader and a
future refactorer will find them: a machine-checked regression pin of the non-monotonicity fact
(the report's Stage 0, and its finding that no such pin exists anywhere in the suite), and a new
bimodal doc recording the decision, the three-route comparison, the two corrections to the
question as originally posed, and the staged path. It deliberately does **not** build the
recommended sweep driver (the report's Stage 1), which is a separate task's work.

### Research Integration

Five conclusions from the report drive the five phases below:

1. **F7** — no test anywhere in `tests/unit/test_witness_registry.py`,
   `tests/unit/test_witness_constraints.py`, or
   `tests/integration/test_certificate_a2_triangle.py` pins the non-monotonicity fact; it lives
   only in prose. A refactor of `WitnessRegistry.wrap()` could silently change the represented
   period space with the suite still green. Phases 1 and 2 close that at two levels.
2. **D1 / F1 / F2** — the decision is the bounded sweep over `back' ∈ [1,back] × fwd' ∈ [1,fwd]`
   with `mid` fixed, not the literal "union over divisors of each bound" (already today's
   behavior at a single bound) and not the single-call period-selector re-encoding. `mid` needs no
   sweep at all, making the fix quadratic rather than cubic in the bound.
3. **F4** — the premise that route (c) costs the certificate wire format and the Lean-side
   re-checker does not hold: `LabelledLasso.nb`/`nm`/`nf` are derived from the exported label
   arrays' lengths, and `recheck`'s windows from those same derived lengths, never from the
   search's configured settings. Recording this prevents a future task re-opening that cost line.
4. **F5 / F6 / D2** — route (c) is declined now on proportionality: it buys nothing the sweep does
   not, at the cost of new clause shapes in three modules whose encoding-completeness argument
   would have to be re-established, while A0 permanently caps the achievable claim and A1 is still
   `[NOT STARTED]`.
5. **Risk, asymmetric** — a theorem-style (`expectation: False`) example has no early exit on the
   sweep's negative side and pays the full `back_max × fwd_max` multiplier. This is the single
   fact that must be measured before any default-behavior change, and it must be recorded next to
   the recommendation rather than buried in a report.

Deliberately **not** in this plan: the sweep driver itself, any `search_mode` setting, any change
to `WitnessRegistry`, `WitnessConstraintGenerator`, `certificate.py`, or the search's default
behavior, and the benchmark of the sweep against the 53-example suite. Those are the report's
Stages 1–2 and belong to a follow-on task; Phase 3's doc records them as named open obligations
instead of implementing them.

### Prior Plan Reference

No prior plan for this task. Effort calibration and shape are taken from the sibling
research-task plan in the same document family
(`specs/195_research_encoder_spec_proof_routes/plans/01_encoder-spec-proof-routes.md`): a
documentation-plus-one-test plan of five to six short phases closing with a grep-based consistency
gate, landing in a few hours. That calibration proved accurate there and the work here is smaller.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch; no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:

- Pin the exact-period slot-folding mechanism at the unit level: positions that share a slot under
  `WitnessRegistry.wrap()` must be shown to share it, so a refactor of `wrap()` cannot silently
  widen or narrow the represented period space.
- Pin the end-to-end consequence at the integration level: a formula measured SAT at `(3,1,3)` and
  `(6,1,6)` and genuinely UNSAT (not inconclusive) at `(2,1,2)`, `(4,1,4)` and `(5,1,5)`, with the
  `timeout` flag asserted false at every point so an UNKNOWN can never masquerade as UNSAT.
- Record the decision, the three-route comparison, the staged path, and the declined route in a
  new bimodal doc, discoverable from the docs hub.
- Record the two corrections to the question as posed: that a single bound already covers exactly
  the divisors of that bound (so the literal "union over divisors" is not a change), and that
  neither candidate route touches the certificate wire format or the Lean re-checker.
- Record the asymmetric theorem-side cost as the gating measurement for any future default change.
- Point `ADEQUACY.md` section 7.1's condition (iii) at the new doc, if and only if that file is
  free of the in-flight sibling task's uncommitted edits when the phase runs.

**Non-Goals**:

- Building the sweep driver, a `search_mode` setting, or any other change to the search's
  behavior or defaults. The task description forbids it ("a report ... not an implementation") and
  the report stages it separately.
- Any edit to `WitnessRegistry`, `WitnessConstraintGenerator`, `certificate.py`, or
  `semantic/core.py`.
- Re-deciding or re-wording the exact-period semantics in `SETTINGS.md` or `semantic/core.py`'s D4
  — the in-flight sibling task owns those files and that wording this cycle.
- Benchmarking the sweep against the 53-example suite (needs the driver first).
- Creating or editing follow-on task entries in `specs/state.json`; Phase 3 records obligations in
  the doc, it does not touch task state.
- Adding any `.claude/context/` note. `.claude/**` is a disposable deploy artifact
  (`rules/source-store-deploy-boundary.md`); such a note would have to be authored in the source
  store under a `/meta` task.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The in-flight sibling task is editing `ADEQUACY.md` on this same working tree, so Phase 4's pointer collides with a foreign uncommitted modification | M | H | Phase 4 runs last, checks `git status --short` for that one path first, and takes the documented no-edit branch (record the deferral, report it) rather than editing over foreign work. Never a directory or glob `git add`; only this task's own hunks, by explicit file list |
| The measured verdict grid does not reproduce, because the formula strings are transcribed from report prose rather than built from the operator conventions | H | M | Treat the grid as a hypothesis, not a fact (Phase 2's Scope Hypothesis). Build the premise list from `\prev`/`\neg` chaining conventions as `examples.py` and `test_structure.py` use them, run the sweep first, record observed verdicts, and only then assert them. If a point disagrees with the report, assert what reproduces and record the divergence in the phase notes rather than forcing the reported value |
| An asserted UNSAT is really solver UNKNOWN (`models/structure.py` maps UNKNOWN to `status=False` with the timeout flag set), so the pin would encode an inconclusive run as a genuine negative | H | M | Assert the timeout flag is false at every grid point, both SAT and UNSAT, exactly as the report's measurement protocol did |
| The `(6,1,6)` grid point inflates suite runtime | L | L | The report measured 0.002–0.006s per solve at these points. Measure the new module's wall clock in Phase 5 and record it; if any point exceeds ~2s, mark that point `slow` and record why |
| The new doc cites task-management metadata (a task number, a `specs/` report path), violating the no-task-references rule for deliverables outside `specs/**` | M | M | The doc states its conclusions self-containedly and cites only durable anchors — doc names, section headings, symbol names, file paths under `code/` — never a `specs/` path or a task number. Phase 5 runs the repo lint to confirm |
| The new doc's cited line numbers drift | L | M | Cite section headings and symbol names in prose; use line numbers only where the surrounding text already does, and re-verify each with a grep in Phase 5 |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 3 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1, 2 and 3 touch three disjoint files
and share no state.

---

### Phase 1: Pin the slot-folding mechanism at the unit level [COMPLETED]

**Goal**: A unit test making it impossible to change `WitnessRegistry.wrap()`'s exact-period
folding without a named test failing.

**Tasks**:
- [x] Read `semantic/witness_registry.py`'s `wrap()` and `slots_per_lasso`, and
      `tests/unit/test_witness_registry.py`'s existing
      `TestWrapAgreesWithLabelledLassoDecoding`, to match the module's established style.
- [x] Add a test class to `tests/unit/test_witness_registry.py` (natural name:
      `TestWrapFoldsByExactPeriod`) asserting the divisor arithmetic directly: at `nb=3`,
      positions `-1` and `-4` share a slot (`-1 % 3 == -4 % 3 == 2`) while `-1` and `-2` do not;
      at `nb=4`, `-1` and `-4` do **not** share a slot. State in the class docstring that this is
      what makes a back-period `p` representable at `nb` exactly when `p` divides `nb`.
- [x] Add the forward-side mirror for `nf` through the `nb + nm + ((t - nm) % nf)` branch, with at
      least one same-slot and one distinct-slot assertion.
- [x] Add one assertion that `bit()` returns the *same* Z3 Boolean for two positions sharing a
      slot and distinct Booleans for two that do not — this is the step that makes the folding
      observable to the encoding rather than merely to arithmetic.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v`.
      53 passed (6 new). Confirmed the pin bites: a scratch `% self.nb` -> `% (self.nb + 1)`
      edit to `wrap()` failed 2 of the new assertions; the edit was discarded (not committed).

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` — one new test
  class pinning `wrap()`'s exact-period folding and its consequence for `bit()` identity

**Verification**:
- The new class passes on the unmodified `wrap()`. These tests pin existing behavior, so green on
  the first run is the expected outcome, not a TDD violation; a RED here would itself be a finding
  and must be reported rather than worked around.
- Temporarily changing `wrap()`'s `% self.nb` to `% (self.nb + 1)` in a scratch copy makes at
  least one new assertion fail (confirm the pin actually bites, then discard the scratch change
  without committing it).

---

### Phase 2: Pin the end-to-end non-monotonicity grid [COMPLETED]

**Goal**: An integration test recording, as a machine-checked fact, that the searched space is not
monotone in `back`/`fwd` — the measurement that currently exists only in prose.

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`
      with a `_build` helper copied from `tests/integration/test_certificate_a2_triangle.py`'s
      (the real `Syntax -> ModelConstraints -> BimodalStructure` pipeline over
      `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` with `back`/`mid`/`fwd` overridden).
- [x] Build the period-3 premise chain: `\prev`-chains pinning `A, ¬A, ¬A, A, ¬A, ¬A` at
      positions `-1..-6`, unary operators chained directly onto their argument with no extra
      parentheses (`examples.py`'s convention, as `test_structure.py`'s `TestA0FrameClassStandingTest`
      does), empty conclusions.
- [x] Run the grid `(2,1,2) (3,1,3) (4,1,4) (5,1,5) (6,1,6)` once and record the observed
      `z3_model_status`, timeout flag and per-point runtime in the module docstring before writing
      any assertion. Both chains reproduced the Scope Hypothesis exactly (no divergence): period-3
      SAT at (3,1,3)/(6,1,6), UNSAT (timeout=False) at (2,1,2)/(4,1,4)/(5,1,5); period-2 SAT at
      (2,1,2)/(4,1,4)/(5,1,5)/(6,1,6), UNSAT at (3,1,3). Total wall clock for all 10 builds
      ~0.92s.
- [x] Assert the observed pattern, parametrized over the grid: SAT at the divisor-compatible
      points, `z3_model_status is False` at the others, and the timeout flag false at **every**
      point so no UNKNOWN is recorded as a genuine UNSAT.
- [x] State in the module docstring what the test does and does not establish: it pins the search
      as configured (this is not an encoding-completeness defect — the encoder faithfully encodes
      families at the lengths given), and it is the fact the recommended sweep would change, with
      a pointer to the new doc from Phase 3 by name.
- [x] Add the counterpart direction from the same measurement — a period-2 chain SAT at `(2,1,2)`
      and UNSAT at `(3,1,3)` — so the pin shows non-monotonicity in both directions rather than
      one lucky formula.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py -v`.
      10 passed in 1.28s.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The grid verdicts (period-3 chain: SAT at `(3,1,3)`/`(6,1,6)`, genuine UNSAT
at `(2,1,2)`/`(4,1,4)`/`(5,1,5)`; period-2 chain: SAT at `(2,1,2)`, genuine UNSAT at `(3,1,3)`)
are a **hypothesis carried over from a prior measurement in another task's report**, not a fact,
and the exact premise strings are a reconstruction from that report's prose. Confirm by running
the grid before asserting anything, and assert only the observed verdicts. The prior measurement
itself records that a first attempt at a related formula produced spurious SAT results from a
mis-rendered operator, so a divergence here is plausible: if a point disagrees, assert what
reproduces, record the divergence and the corrected strings in the module docstring, and report it
in the phase notes — do not adjust the formula until it yields the reported answer.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py` —
  new file; the `_build` helper, the two period chains, the parametrized grid assertions and the
  scope-limiting module docstring

**Verification**:
- The new module passes, with the timeout flag asserted false at every grid point.
- Total wall clock for the module is recorded in the phase notes; any point above ~2s is
  `slow`-marked with the reason.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/ -q`
  shows no new failure elsewhere in the integration directory.

---

### Phase 3: Record the decision in a new bimodal doc [COMPLETED]

**Goal**: The recommendation, the three-route comparison, the two corrections and the staged path
live in the theory's own documentation, not only in a task report.

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md` with sections
      covering, in order: the fact (exact-period folding in `WitnessRegistry.wrap()`, the
      divisibility rule, the measured non-monotonicity and where it is now pinned); the three
      routes compared; the decision and why; the staged path; and the open obligations.
- [x] In the routes section, state for each route what it costs and what it buys: documentation
      alone leaves the adequacy document's condition (iii) undischarged; the bounded sweep over
      `back' ∈ [1,back] × fwd' ∈ [1,fwd]` with `mid` fixed needs zero changes to
      `WitnessRegistry`, `WitnessConstraintGenerator` or `certificate.py` and leaves the one-hot
      `sel` selector and (C1)–(C4) untouched line-for-line; the single-call period-selector
      re-encoding costs new clause shapes in three modules plus a re-established
      encoding-completeness argument, for the same asymptotic work concentrated in one harder
      instance.
- [x] Record the two corrections explicitly, each under its own heading so a future reader cannot
      miss them: (1) at a single bound the search already represents exactly the periods dividing
      that bound, so a "union over the divisors of the bound" is today's behavior rather than a
      change — the load-bearing version is the `1..n` sweep, since every `p ≤ n` divides itself;
      (2) neither route touches the certificate wire format or the Lean-side re-checker, because
      `LabelledLasso`'s segment lengths and `recheck`'s windows are derived from the exported label
      arrays, not from the search's configured settings.
- [x] Record the proportionality argument: the frame-class gap permanently caps the achievable
      claim at ℤ-time validity and the compression obligation is unstarted, so the sweep
      discharges condition (iii) exactly as well as the re-encoding would, at materially lower
      engineering and proof cost.
- [x] Record the asymmetric cost as the gating measurement, in its own subsection: a theorem-style
      (`expectation: False`) example must exhaust the entire `back_max × fwd_max` grid with every
      call UNSAT before the sweep can report UNSAT — no early exit on the negative side — so
      theorem-style examples pay the full multiplicative cost every run, and no default change
      should ship before this is measured against the example suite.
- [x] Record the open obligations as a named list: build the sweep driver; expose it as an opt-in
      setting rather than flipping the default; benchmark it with attention to the theorem side;
      re-derive condition (iii) as discharged once the compression bound lands; and respect the
      two-phase certificate-emission idempotency guard when constructing more than one registry
      per solve.
- [x] Add the doc to `docs/README.md` in both places the hub lists docs: the Quick Navigation
      bullet list and the per-file overview section below it.
- [x] Cite only durable anchors — doc names, section headings, symbol names, paths under `code/` —
      and no task number or `specs/` path anywhere in either file. Verified by direct grep (the
      repo-wide `check-task-references.sh` scans only `agent-system/extensions`, `.opencode`,
      `lua`, `.memory` — it does not cover `code/`, so this task grepped both files directly for
      `task N`/`specs/NNN_` patterns and found none.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md` — new file; the decision
  record
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` — two additive entries (Quick
  Navigation bullet, overview subsection)

**Verification**:
- Every symbol and section heading the new doc cites resolves: grep each of `wrap`,
  `slots_per_lasso`, `sel`, `LabelledLasso`, `recheck`, and each cited section heading, and
  confirm a hit at the cited file.
- `bash .claude/scripts/check-task-references.sh` reports no new finding for either file.
- The new doc names the test modules from Phases 1 and 2 by path, and those paths exist.

---

### Phase 4: Point condition (iii) at the new doc, if the file is free [NOT STARTED]

**Goal**: A reader arriving at the adequacy document's condition (iii) — the condition this
non-monotonicity falsifies as worded — finds the decision record, without this task editing over a
sibling's in-flight work.

**Tasks**:
- [ ] Run `git status --short -- code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` and
      `git log --oneline -3 -- code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`.
- [ ] **If the path shows a foreign uncommitted modification** (the concurrent sibling task owns
      this file this cycle): take the no-edit branch. Make no change to `ADEQUACY.md`. Instead add
      one line to `SEARCH_COVERAGE.md`'s open-obligations list recording that the cross-reference
      from condition (iii) is still owed, mark this phase `[BLOCKED]` with that reason, and report
      the observation — including what `git log` showed — rather than proceeding.
- [ ] **If the path is clean**: re-read section 7.1 immediately beforehand, then add a single
      additive sentence under condition (iii) pointing at `SEARCH_COVERAGE.md` by name for the
      route comparison and the decision. Change no existing wording, and do not restate the
      routes.
- [ ] Stage only this one path by explicit filename; never a directory or glob pathspec.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that the pointer belongs under `ADEQUACY.md` section
7.1's condition (iii) and that condition (iii) is still worded as the report found it. Confirm by
grepping for the section 7.1 heading and the condition (iii) text immediately before editing; the
concurrent sibling task is actively rewriting that section's prerequisite structure, so the
anchor may have moved or been rephrased. If it has, place the pointer at whatever the current
condition (iii) text is, and record the difference in the phase notes.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — at most one additive sentence
  under section 7.1 condition (iii); **conditional**, see the decision rule above

**Verification**:
- Either the one-sentence pointer is present and `git diff` for that path shows exactly one added
  line with nothing else changed, or the phase is `[BLOCKED]` with the foreign-modification
  evidence recorded and `ADEQUACY.md` untouched.

---

### Phase 5: Consistency gate [NOT STARTED]

**Goal**: Everything this plan added is green, internally consistent, and free of drifted
citations.

**Tasks**:
- [ ] Run the full bimodal suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`.
- [ ] Run `PYTHONPATH=code/src pytest code/tests/ -q` to confirm nothing outside the theory
      regressed.
- [ ] Re-verify every citation added by Phase 3 and Phase 4 with a grep (symbol names, section
      headings, file paths), and fix any that has drifted.
- [ ] Run `bash .claude/scripts/check-task-references.sh` and confirm no finding for any file this
      plan touched.
- [ ] Confirm the docs hub's two new entries render in the same style as their neighbours.
- [ ] Record in the phase notes: the measured wall clock of the new integration module, the
      observed grid verdicts as asserted, and whether Phase 4 took the edit or the no-edit branch.
- [ ] Confirm no file outside this plan's declared set was modified by this task
      (`git status --short`), and that any foreign modification present is left untouched and
      reported.

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification only; citation repairs, if any, land in the Phase 3/4 files)

**Verification**:
- Both pytest invocations pass, with the pre-existing pass/fail baseline reported for comparison.
- The citation greps all resolve.
- The task-reference lint is clean for every touched file.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v` — new exact-period folding class passes.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py -v` — grid pin passes with the timeout flag false at every point.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` — full theory suite green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` — no regression outside the theory.
- [ ] `bash .claude/scripts/check-task-references.sh` — no task-number reference in any touched deliverable.
- [ ] Every symbol, section heading and path cited by the new doc resolves by grep.
- [ ] The new integration module's wall clock is measured and recorded, not assumed.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` — new test class pinning `wrap()`'s exact-period folding and its effect on `bit()` identity.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py` — new module pinning the measured non-monotonicity grid in both directions.
- `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md` — new doc: the fact, the three-route comparison, the decision, the two corrections, the staged path, the open obligations.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` — two additive hub entries.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — at most one additive pointer sentence; conditional on the file being free of the sibling task's in-flight edits.
- `specs/203_research_divisor_period_search_coverage/summaries/01_divisor-period-search-coverage-summary.md` — implementation summary.

## Rollback/Contingency

Every phase is additive and independently revertible: Phases 1 and 2 add tests only, Phase 3 adds
one new file plus two hub lines, Phase 4 adds at most one sentence. Revert a single phase with
`git revert` of that phase's own commit — the per-substep commit mode keeps each phase's diff
self-contained, and no production code is modified anywhere in this plan, so no runtime behavior
can regress.

Do **not** take a working-tree snapshot as a routine start-of-phase precaution: a concurrent
sibling task is editing this same tree, and a reverting snapshot would discard its work. If a
genuine rollback of uncommitted changes ever becomes necessary, follow
`context/contracts/recovery.md`'s rollback rung for the correct invocation shape, including its
out-of-scope override flag, and only after confirming from `git status` which hunks belong to this
task.

If Phase 2's grid does not reproduce at all (no formula in the family yields a non-monotone
verdict pattern), do not weaken the assertion to something trivially true: keep Phase 1's unit
pin, record the failure to reproduce in `SEARCH_COVERAGE.md` as an open question against the prior
measurement, and report it — a prior measurement that does not reproduce is a finding about the
report, not a reason to ship a vacuous test.
