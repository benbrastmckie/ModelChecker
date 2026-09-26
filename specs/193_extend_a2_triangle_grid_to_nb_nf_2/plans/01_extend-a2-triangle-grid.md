# Implementation Plan: Extend the A2-triangle exhaustive grid to nb=nf=2

- **Task**: 193 - Extend the A2-triangle encoding-completeness test's exhaustive grid beyond back=mid=fwd=1 to cover nb=nf=2
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/193_extend_a2_triangle_grid_to_nb_nf_2/reports/01_extend-a2-triangle-grid.md
- **Artifacts**: plans/01_extend-a2-triangle-grid.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: python
- **Lean Intent**: false

## Overview

`tests/integration/test_certificate_a2_triangle.py`'s Tier 1 exhaustive enumeration is pinned to
`back = mid = fwd = 1`, which is structurally blind to the one A2 violation known to have actually
occurred (narrow-window local coherence, which requires `nb = 2` to manifest — see
`semantic/witness_constraints.py`'s module docstring). This plan generalizes the test's candidate
generator and closed-form count to arbitrary `nb`/`nm`/`nf`, then adds `back = 2, mid = 1, fwd = 2`
grid points — production's actual `DEFAULT_EXAMPLE_SETTINGS` — for the two box-free closures
unconditionally and for one box-carrying closure under the existing `slow` marker. The existing
three closures' `back = mid = fwd = 1` cases and Tier 2's clean-skip discipline are left byte-for-byte
intact. Done means: the new grid points pass with counts confirmed against the test's own run
output, the full module (including `slow`) runs inside CI's 300s-per-test ceiling, and
`ADEQUACY.md` section 7.3 records both the new coverage and the documented infeasibility of the
size-3 boxed closure at this grid size.

### Research Integration

The research report supplies measured (not estimated) numbers this plan is built on:

- `_candidates()` builds single-element segment tuples (`back=(back_label,)`), which produce valid
  `LabelledLasso` instances only at `nb = nm = nf = 1`; segments must become
  `itertools.product(labels, repeat=nb)` etc. (Finding 1).
- `_expected_candidate_count()`'s exponent `3 * lassos` is `(nb+nm+nf) * lassos` specialized to the
  current fixture; the general form is `slots_per_lasso * lassos`, and the identity
  `target_window_len == slots_per_lasso == nb+nm+nf` (already relied on silently) should be named
  (Finding 2).
- Measured at `back=2, mid=1, fwd=2`: box-free `[] |- (q \Until p)` = 163,840 candidates / 926
  accepted / SAT / 1.06s; box-free `A |- A` = 160 / 0 / UNSAT / ~0s; boxed `\Box A |- A`
  (closure size 2) = 10,485,760 / 0 / UNSAT / 65.47s full run (Finding 3).
- The existing boxed closure `\Box A |- B` (closure size 3) is infeasible at this grid:
  10,737,418,240 candidates, ~19h extrapolated; even one-sided `back=2, mid=1, fwd=1` is ~14.4
  minutes (Finding 3).
- CI passes `--timeout=300 --timeout-method=thread` per test and the `slow` marker grants no
  exemption — it only controls local `-m "not slow"` deselection (Finding 4). Verified
  independently against `.github/workflows/tests.yml`, which additionally runs with `-n 4`, so
  measured idle-host timings must be read with parallel-load headroom (see Risks).
- No three-way disagreement was observed at `nb=nf=2`; the narrow-window defect is already fixed,
  so this task adds forward regression coverage rather than chasing a live bug (Finding 5).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch's delegation context, so no roadmap consultation
was performed and no roadmap phases are included.

### Concurrency Note

Tasks 192, 194, and 196 are dispatched this same `/orchestrate` cycle on this shared working tree
with undeclared file scope. Before editing either file this plan touches, re-read it immediately
beforehand; stage only this task's own paths by explicit filename (never a directory or glob
pathspec); never run `git-snapshot.sh` in its reverting default mode; and if a foreign commit or
foreign uncommitted modification to
`code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` or
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` appears, STOP and report it after
checking `git log`.

## Goals & Non-Goals

**Goals**:
- Generalize `_candidates()` and `_expected_candidate_count()` in
  `test_certificate_a2_triangle.py` to arbitrary `nb`/`nm`/`nf`, with the
  `slots_per_lasso == target_window_len` identity named rather than silently assumed.
- Grid-parameterize `_assert_exhaustive_triangle_agrees()` so a case declares its own
  `back`/`mid`/`fwd`.
- Add both box-free closures at `back=2, mid=1, fwd=2` as unconditional (non-`slow`) Tier 1 cases.
- Add exactly one box-carrying closure of closure size 2 at `back=2, mid=1, fwd=2` as an additional
  `slow`-marked Tier 1 case, selected by an implementation-time measurement gate against a
  conservative wall-clock ceiling.
- Keep all three existing closures' `back = mid = fwd = 1` cases, their expected counts, and Tier 2's
  `skipif(SKIP_REASON)` class-level clean-skip discipline unchanged.
- Record the new coverage — and the size-3 boxed closure's documented infeasibility at this grid —
  in the module docstring and `ADEQUACY.md` section 7.3.

**Non-Goals**:
- Extending the existing `\Box A |- B` (closure size 3) boxed closure to `nb=nf=2`, at any tier or
  marker. Research Finding 3-4 establishes this as infeasible under the current CI harness
  (~19h full, ~14.4min one-sided vs. a 300s ceiling), not a tuning problem.
- Diagnosing the encoder. A genuine three-way disagreement is reported as a finding in the
  implementation summary and the task's return metadata; fixing it is out of scope and the
  assertion must not be weakened or the closure dropped.
- Any change to production code (`witness_constraints.py`, `witness_registry.py`, `certificate.py`,
  `core.py`) or to Tier 2's sampling stride, per-class count, or skip mechanism.
- Adding new `slow`/`timeout` markers to `code/pyproject.toml` (`slow` is already registered) or
  changing CI workflow files.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The 65s boxed case measured on an idle host runs slower under CI's `-n 4` parallel load and approaches the 300s per-test ceiling | H | M | Phase 3's decision gate requires measured idle-host wall clock <= 100s (>=3x headroom), not merely <300s; if the chosen formula exceeds 100s, take the documented contingency branch (one-sided `back=2, mid=1, fwd=1`, ~524,288 candidates) |
| Generalizing `_candidates()` silently changes the existing three closures' enumeration, invalidating their expected counts | H | M | Phase 1 is a pure refactor verified by running the existing module (including `slow`) with all three existing expected counts unchanged, before any new grid point is added |
| Tier 2's `_sampled_candidates()` couples to the new generator shape and breaks or changes its selection | M | M | Phase 1 verification runs `TestBoundedLeanCrossCheck` explicitly; `SKIP_REASON is None` on this host, so Tier 2 genuinely executes rather than skipping and a coupling regression cannot hide behind a skip |
| Research's exact `accepted` counts are host- and formula-dependent and may not reproduce | M | L | Every new expected count is a Scope Hypothesis confirmed from the test's own run output at implementation time (deliberately RED-first: write the case, read the actual, then pin), never copied blind from the report |
| A future closure-size or `max_witnesses` change silently invalidates a new case | L | L | Reuse the existing `expected_closure_size` assertion pattern for every new parametrize entry — it already fails loudly rather than drifting |
| A genuine three-way disagreement surfaces at `nb=nf=2` | M | L | Report as a finding (summary + `.return-meta.json`); do not weaken the assertion, drop the closure, or attempt an encoder diagnosis |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 2 and 3 are parallel-safe only because
Phase 3 writes no repository file — it runs a scratchpad measurement script. Phase 2 owns
`test_certificate_a2_triangle.py` for that wave.

### Phase 1: Generalize the candidate generator and the closed-form count [NOT STARTED]

**Goal**: `_candidates()` and `_expected_candidate_count()` produce correct candidates and totals at
any `nb`/`nm`/`nf`, with the existing three closures' behavior at `back = mid = fwd = 1` provably
unchanged.

**Tasks**:
- [ ] Re-read `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` immediately before editing (sibling-task concurrency).
- [ ] In `_candidates()`, read `nb`/`nm`/`nf` from `semantics.witness_registry` and build each lasso's segments as `itertools.product(labels, repeat=nb)` / `repeat=nm` / `repeat=nf`, combined across the three segments via `itertools.product`, replacing the hard-coded `back=(back_label,), mid=(mid_label,), fwd=(fwd_label,)` construction. Materialize the per-lasso choice list once, preserving the existing comment's explanation of why that matters.
- [ ] Keep the `len(closure) <= 4` assertion and its message verbatim.
- [ ] In `_expected_candidate_count()`, compute `slots_per_lasso = registry.slots_per_lasso` once and use it for both the exponent (`slots_per_lasso * lassos`, replacing the literal `3`) and the trailing multiplicand; add a one-line comment naming the `target_window_len == slots_per_lasso == nb+nm+nf` identity that the previous code relied on without stating.
- [ ] Update `_candidates()`'s docstring to say it reads segment lengths from the registry rather than assuming length-1 segments.
- [ ] Run the full module including `slow` and confirm all existing cases pass with their existing expected counts untouched.
- [ ] Commit (green sub-step).

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the existing expected counts are unchanged — `1536`/`52`
(box-free until), `24`/`0` (box-free contradiction), `1,572,864`/`96` (boxed). Confirm by running
`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -v`
with no expected-count literal edited in this phase; any count assertion failure means the
refactor changed enumeration semantics and must be fixed, never re-pinned.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - generalize `_candidates()` segment construction and `_expected_candidate_count()`'s exponent

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -v` — all Tier 1 cases pass with unedited expected counts.
- `TestBoundedLeanCrossCheck`'s three cases run (not skip — `SKIP_REASON is None` on this host) and pass, confirming `_sampled_candidates()` still drives the generalized generator correctly.

---

### Phase 2: Add the two box-free closures at back=2, mid=1, fwd=2 [NOT STARTED]

**Goal**: Both box-free closures are exhaustively enumerated at production's default grid,
unconditionally (no `slow` marker), with counts confirmed from run output.

**Tasks**:
- [ ] Re-read the test file immediately before editing.
- [ ] Add `back`, `mid`, `fwd` parameters to `_assert_exhaustive_triangle_agrees()` and pass them to `_build()`, replacing the hard-coded `back=1, mid=1, fwd=1`. Keep the existing call sites' behavior identical by passing `1, 1, 1` explicitly for every pre-existing case.
- [ ] Add the grid to `TestExhaustiveTriangleBoxFree`'s parametrize signature and extend each existing `pytest.param` with its `1, 1, 1` grid, keeping the existing `id=` values unchanged.
- [ ] Add two new `pytest.param` entries at `back=2, mid=1, fwd=2`: `[] / ["(q \\Until p)"]` (closure size 3, expected SAT) and `["A"] / ["A"]` (closure size 1, expected UNSAT), with ids suffixed `_nb2_nf2`.
- [ ] Run the two new cases, read the actual `total`/`accepted` from the assertion output, and pin them (research predicts `163,840`/`926`/SAT and `160`/`0`/UNSAT — treat these as hypotheses to confirm, and if the actual `total` disagrees with the closed-form `_expected_candidate_count()`, that is a generator bug from Phase 1, not a number to re-pin).
- [ ] Update the class docstring to name both grid sizes covered and the measured added wall cost.
- [ ] Commit (green sub-step).

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts the two new cases total `163,840` / `160` candidates with `926` / `0`
accepted and SAT / UNSAT verdicts, at ~1.06s combined. Confirm from the test's own run output and
from `_expected_candidate_count()`'s independent closed-form agreement (the existing triple
assertion `total == expected_formula_total == expected_total` already enforces this); record the
actual measured wall clock for the class in the docstring rather than copying the report's figure.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - grid-parameterize the shared helper; add two box-free `nb=nf=2` parametrize cases

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py::TestExhaustiveTriangleBoxFree -v` — four cases pass.
- Total added wall clock for the class is under 5s (well inside a non-`slow` budget); if it is not, record the actual and reassess the `slow` marking for the new cases only.

---

### Phase 3: Measurement gate — select a box-carrying closure of size 2 for nb=nf=2 [NOT STARTED]

**Goal**: One concrete boxed closure is selected for the `nb=nf=2` `slow` case, with its closure
size, candidate total, accepted count, Z3 verdict, and idle-host wall clock all measured directly
rather than assumed.

**Tasks**:
- [ ] Write a scratchpad measurement script (under the session scratchpad directory, not the repository) that imports the test module's own generalized `_candidates`, `_run_exhaustive_triangle`, `_expected_candidate_count`, and `_build`, and for each candidate formula reports: closure size, candidate total, accepted count, `z3_model_status`, and wall clock.
- [ ] Measure candidate A: `[] |- ["\\Box A"]` at `back=2, mid=1, fwd=2` — preferred if it is closure size 2 and SAT, because a SAT boxed case additionally exercises the extracted-certificate `recheck` leg that `_assert_exhaustive_triangle_agrees` runs only when `expected_sat` is true.
- [ ] Measure candidate B: `["\\Box A"] |- ["A"]` at `back=2, mid=1, fwd=2` — research-measured fallback (closure size 2, 10,485,760 candidates, 0 accepted, UNSAT, 65.47s).
- [ ] Apply the gate, in order: (a) closure size must be 2 (size 3 is out of scope per Non-Goals; a larger size blows the enumeration); (b) idle-host wall clock must be <= 100s, giving >=3x headroom under CI's 300s ceiling with `-n 4` parallel load; (c) prefer SAT over UNSAT among candidates passing (a) and (b).
- [ ] Contingency branch, taken only if no candidate passes (a)+(b): select candidate B at the one-sided grid `back=2, mid=1, fwd=1` (closure size 2, 2 lassos, 1 box, 4 slots => 524,288 candidates, expected well under 10s), which still covers the `nb=2` slot-recurrence dimension the historical defect required. Measure it before selecting it.
- [ ] Record the selected formula, grid, all four measured values, and the gate outcome in the phase body of this plan (or the progress file) so Phase 4 pins numbers from a measurement, not from this plan's prose.
- [ ] No repository file is modified in this phase; nothing to commit.

**Timing**: 45 minutes (dominated by ~1-3 minutes of compute per full-grid measurement)

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts candidate B measures 10,485,760 candidates / 0 accepted / UNSAT /
~65s, and hypothesizes candidate A is closure size 2 with the same candidate total but SAT.
Confirm both by direct measurement with the scratchpad script; the measured values, not these,
are what Phase 4 pins. If candidate A's closure size is not 2, discard it and proceed with B
without further search.

**Files to modify**:
- None (scratchpad measurement script only, outside the repository)

**Verification**:
- Both candidates' measured candidate totals agree exactly with `_expected_candidate_count()`'s
  closed form (independent cross-check of Phase 1's generalization at a second grid point).
- The gate outcome is unambiguous: exactly one formula + grid is selected, with all four values
  recorded.

---

### Phase 4: Add the selected boxed closure as a slow-marked nb=nf=2 Tier 1 case [NOT STARTED]

**Goal**: The box-guess and two-lasso dimensions are covered at `nb=nf=2` by one `slow`-marked
exhaustive case, with the existing `\Box A |- B` size-3 case untouched.

**Tasks**:
- [ ] Re-read the test file immediately before editing.
- [ ] Add a second test method to `TestExhaustiveTriangleWithBox` (leaving `test_boxed_closure_enumeration_agrees_with_z3` and its numbers byte-for-byte unchanged) carrying `@pytest.mark.slow`, invoking `_assert_exhaustive_triangle_agrees` with Phase 3's selected premises/conclusions, grid, `expected_closure_size`, and Phase 3's measured `expected_total` / `expected_accepted` / `expected_sat`.
- [ ] Extend the class docstring with the new case's measured candidate count, accepted count, verdict, and wall clock, and state explicitly that the size-3 closure stays at `back = mid = fwd = 1` because `nb=nf=2` there is ~10.7 billion candidates (~19h) — well past CI's 300s per-test ceiling, which `slow` does not lift.
- [ ] Run the new case alone and confirm it passes with the pinned numbers and inside the wall-clock gate.
- [ ] Commit (green sub-step).

**Timing**: 45 minutes

**Depends on**: 2, 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts the new case's `expected_total`, `expected_accepted`,
`expected_closure_size`, and `expected_sat` equal Phase 3's measured values. Confirm by the test
passing on first run with those literals; a mismatch means Phase 3's measurement and the test's
own construction diverge (likely a differing setting override) and must be reconciled, not
re-pinned.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - add one `slow`-marked boxed `nb=nf=2` case and extend the class docstring

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py::TestExhaustiveTriangleWithBox -v --durations=0` — both cases pass; the new case's reported duration is within Phase 3's gate.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -m "not slow" -v` — the non-`slow` selection still deselects both boxed cases and passes.

---

### Phase 5: Sync the module docstring and ADEQUACY.md section 7.3 [NOT STARTED]

**Goal**: The documentation describes what the test now covers — both grid sizes — and names the
one standing coverage gap, so a reader is not left believing the grid is still `back = mid = fwd = 1`
only.

**Tasks**:
- [ ] Re-read both files immediately before editing.
- [ ] Update the test module's top-level docstring: the Tier 1 bullet and the opening paragraph's "fix `back = mid = fwd = 1`" framing should state that the grid now covers both `back = mid = fwd = 1` and `back = 2, mid = 1, fwd = 2` (production's `DEFAULT_EXAMPLE_SETTINGS`), and should name why `nb = 2` matters: `witness_constraints.py`'s recorded narrow-window local-coherence defect required `nb = 2` to manifest, since slot `back[1]` recurs at every odd-magnitude position.
- [ ] Add one or two sentences to `ADEQUACY.md` section 7.3's "Deciding test for A2" paragraph (currently describing only the `back = mid = fwd = 1` grid) recording the added `nb=nf=2` coverage, which closures carry it, and the standing gap: the size-3 boxed closure remains `back = mid = fwd = 1`-only because exhaustive enumeration at `nb=nf=2` is ~10.7 billion candidates. Do not restate the section's own Test block, which fixes `back = mid = fwd = 1` as the minimum, not the maximum.
- [ ] Reference durable anchors only (file names, section numbers, closure descriptions) — no task numbers in either file.
- [ ] Commit (green sub-step).

**Timing**: 30 minutes

**Depends on**: 4

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - module docstring
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - section 7.3 "Deciding test for A2" paragraph

**Verification**:
- Diff read-through confirming every changed hunk in the test file lies inside the module docstring (a `prose` tier edit that crosses out of the docstring is exactly this tier's blind spot — check the hunk boundaries explicitly).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py --collect-only -q` still collects every case (catches a docstring edit that broke the module).
- `bash .claude/scripts/check-task-references.sh` (or the write-time hook) reports no task-number reference in either deliverable file.

---

### Phase 6: Full gate and findings [NOT STARTED]

**Goal**: The whole bimodal suite is green with the strengthened test, the added cost is quantified,
and any three-way disagreement is reported rather than diagnosed.

**Tasks**:
- [ ] Run the full bimodal test suite including `slow`: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal -q --durations=15`.
- [ ] Run the module under CI's own timeout shape to confirm no per-test breach: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -q --timeout=300 --timeout-method=thread`.
- [ ] Record in the implementation summary: each new case's measured candidate total, accepted count, Z3 verdict, and wall clock; the total wall-clock delta for the module; and the slowest-test durations from `--durations=15`.
- [ ] If any `_assert_exhaustive_triangle_agrees` triple-comparison assertion failed for a genuine reason (accepted > 0 with Z3 UNSAT, or accepted == 0 with Z3 SAT), report it verbatim as a finding in the summary and in `.return-meta.json`, naming the closure and grid — do not weaken the assertion, drop the closure, or attempt to diagnose the encoder.
- [ ] Confirm Tier 2 (`TestBoundedLeanCrossCheck`) is untouched: `git diff` over the phase range shows no change below the Tier 2 section banner, and the class still carries its `skipif(SKIP_REASON)` decorator.
- [ ] Commit any remaining work and write the implementation summary.

**Timing**: 45 minutes

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts the module's total added wall clock is roughly (new box-free cases
~1s) + (new boxed case, Phase 3's measured figure) and that no other test in the bimodal suite
changes duration. Confirm from `--durations=15` output against the pre-change baseline recorded in
the existing docstrings (~11s boxed Tier 1, ~58s Tier 2).

**Files to modify**:
- None (verification and summary only)

**Verification**:
- Full bimodal suite green, including every `slow`-marked case.
- No test in the module exceeds 300s under `--timeout=300 --timeout-method=thread`.
- `git diff` confirms Tier 2's section is unmodified.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -v` passes with all Tier 1 cases at both grid sizes.
- [ ] The three pre-existing closures' `back = mid = fwd = 1` expected counts (`1536`/`52`, `24`/`0`, `1,572,864`/`96`) are unchanged in the file and still pass.
- [ ] Every new case's `total` agrees with `_expected_candidate_count()`'s independently computed closed form (the existing `total == expected_formula_total == expected_total` triple assertion).
- [ ] `-m "not slow"` still deselects exactly the boxed cases and passes.
- [ ] `TestBoundedLeanCrossCheck` runs (this host has a BimodalLogic checkout: `SKIP_REASON is None`) and passes unchanged; its skip decorator and sampling logic are untouched.
- [ ] No test exceeds CI's 300s per-test ceiling under `--timeout=300 --timeout-method=thread`.
- [ ] Full bimodal suite green including `slow`.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` — generalized generator and count formula, grid-parameterized shared helper, three new `nb=nf=2` Tier 1 cases (two unconditional, one `slow`), updated module and class docstrings.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — section 7.3 prose recording the added `nb=nf=2` coverage and the size-3 boxed closure's standing gap.
- `specs/193_extend_a2_triangle_grid_to_nb_nf_2/summaries/01_*-summary.md` — measured counts, verdicts, wall clocks, and any disagreement finding.

## Rollback/Contingency

Both deliverable files are self-contained and every phase commits at a green sub-step, so rollback
is `git revert` of this task's phase commits in reverse order — no working-tree discard is needed
and none should be attempted while sibling tasks share this tree. If an intentional rollback of
*uncommitted* work becomes necessary, follow `context/contracts/recovery.md`'s rollback rung for
the exact snapshot-then-rollback invocation, including its out-of-scope override flag; never emit a
bare default-mode `git-snapshot.sh` as a routine precaution.

Per-phase contingencies:
- Phase 1 refactor changes existing counts: the refactor is wrong. Fix the generator; do not re-pin
  the expected counts.
- Phase 3 finds no closure-size-2 formula within the 100s gate: take the documented one-sided
  `back=2, mid=1, fwd=1` branch (~524,288 candidates). If even that fails the gate, close Phase 4
  as `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record citing Phase 3's
  measurement as evidence — the two box-free `nb=nf=2` cases from Phase 2 still deliver the task's
  core `nb=2` regression coverage, and Phases 5-6 proceed on that reduced scope with the exclusion
  documented in `ADEQUACY.md`.
- A genuine three-way disagreement surfaces: leave the assertion in place, report the finding, and
  let the task return `partial`/`blocked` rather than adjusting the test to pass.
