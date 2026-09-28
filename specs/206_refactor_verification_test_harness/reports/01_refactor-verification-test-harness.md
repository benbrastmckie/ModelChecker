# Research Report: Refactor Verification Test Harness

- **Task**: 206 - Refactor Verification Test Harness
- **Started**: 2026-09-27T18:04:00Z
- **Completed**: 2026-09-27T18:45:00Z
- **Effort**: ~40 minutes (research only)
- **Dependencies**: task 207 (completed; the `all_constraints` fix this harness's evaluator's
  `full_constraints` helper documents as now-redundant), task 205 (concurrent; owns the trust
  boundary / tier-promotion decision this report explicitly does not pre-empt)
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` (441 lines, full read)
  - `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (full read)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
    (600 lines, full read)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`
    (full read)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`,
    `test_witness_registry.py`, `test_pinned_eval.py` (heads/full read)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` (Lean
    cross-check section)
  - `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (`recheck` and its
    helpers, `_coherent_at`/`_fulfil_at`/`_box_faithful`/`_target_holds`)
  - `code/pyproject.toml` (marker registry), `.github/workflows/tests.yml`,
    `.github/workflows/unstable-watch.yml`, `.github/workflows/differential-tests.yml`
  - `code/docs/core/TESTING_GUIDE.md` sections 8.8 (Oracle gating/exhaustive split), 8.9, 8.14
  - `specs/state.json` entries for tasks 205, 206, 207
  - Direct measurement: reproduced the widest boxed Tier 1 case standalone (single pytest
    invocation, this host) and two before/after micro-benchmarks against the real
    `recheck`/`_pinned_eval` code paths (see Findings, Performance)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The four `_settings`/`_build` helper functions duplicated verbatim across
  `test_certificate_a2_triangle.py`, `test_search_period_coverage.py`, `test_structure.py`, and
  `test_pinned_eval.py` are genuine, removable redundancy; the various numeric **grids**
  (`_GRID`, `_A0_SWEPT_GRID`, the A2-triangle parametrize table) are *not* the same data
  restated — they encode three independent test properties and should stay separate.
- Tier membership (Tier 1 vs. Tier 2) is expressed through three mechanisms — docstring prose, a
  `slow` marker, and a `BIMODAL_LOGIC_PATH`-keyed `skipif` — but these are not duplicates of one
  fact; they are three different *kinds* of gating (documentation, performance deselection,
  environment availability) that pytest requires to live at three different sites. Collapsing
  them into "one registry" would add indirection without removing a mechanism.
- `_pinned_eval.py` living inside `tests/` (not `theory_lib`) already matches this task's own
  in-repo precedent (`_lean_check.py`); no other theory has anything analogous outside its test
  tree. Recommend leaving it in place unless/until task 205 decides to promote a checker to
  production, at which point location and public surface become that task's decision, not this
  one's.
- Reproduced the authoritative baseline directly: the widest boxed case
  (`test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`) ran **111.85s–113.36s** standalone on
  this host across three separate runs, consistent with the CI-shaped **123.29s** already on
  record.
- Measured (not estimated) that build+solve (~0.02s) and one-time compile (~0.006s) are 0.02% of
  the widest case's cost — routes "share solved structures via fixtures" and "cache the compiled
  evaluator across configurations" recover essentially nothing for this bottleneck, and the one
  place they would apply (`TestBoundedLeanCrossCheck`'s `boxed_closure_sat` case duplicating
  `TestExhaustiveTriangleWithBox`'s build) never co-executes in CI, since CI never sets
  `BIMODAL_LOGIC_PATH`.
- Built and measured a real, non-narrowing algorithmic fix: since `_candidates()` already yields
  the same `WitnessFamily` object for every `target_window` position before moving to the next
  family, ~96.5% of `recheck()`'s per-candidate cost (structural + C1 + C2 + C3, which do not
  depend on `target_time`) and the equivalent target-time-independent share of the pinned
  evaluator's row-build are pure recomputation. Caching them across the shared-family run cut the
  widest case from **110.89s to 32.31s on this host — a measured 70.9% reduction, 3.43x
  speedup — with `total`/`accepted`/`pinned_accepted` identical** (10,485,760 / 5,115 / 5,115),
  i.e. no candidate is skipped and no assertion is weakened.

## Context & Scope

This task owns the bimodal verification test harness's organization and performance;
`code/src/model_checker/theory_lib/bimodal/tests/`. It explicitly excludes the trust boundary
between testing and formal verification (task 205's decision: whether `TestBoundedLeanCrossCheck`
is promoted from a sampled tier to an output gate, and how Tier 2 is repositioned), and the
certificate-wire hardening / proof-carrying acceptance mode (a separate task task 205's own
description names as already out of *its* scope too). Task 207 (completed) already fixed
`ModelConstraints.all_constraints` being stale for bimodal; `_pinned_eval.py`'s `full_constraints`
helper is now a documented no-op alias rather than a workaround, which this report treats as
settled, not re-derived.

Two governing constraints from the dispatch, both honored throughout this report's
recommendations:

- Nothing may weaken what the existing tests establish; any narrowing of an enumeration must be
  stated explicitly, never silently absorbed as a speedup. The performance recommendation below
  narrows nothing — it eliminates literal recomputation of the same result, verified by an
  exact-match rerun of the full candidate/accepted/pinned counts.
- Preserve: Tier 2's clean-skip behavior as-is; the `timeout is False` assertions in the A0
  standing tests and the search-coverage grid; the retained aggregate assertion alongside the
  per-candidate comparison.

## Findings

### Organization

**F1 — Duplicated `_settings`/`_build` helpers (real redundancy).** Four modules define
byte-for-byte equivalent `_settings(**overrides)` / `_build(premises, conclusions,
**setting_overrides)` helpers, each explicitly cross-referencing the others in its own docstring
as "matching X's own `_build` helper": `tests/integration/test_certificate_a2_triangle.py`,
`tests/integration/test_search_period_coverage.py`, `tests/unit/test_structure.py`, and
`tests/unit/test_pinned_eval.py`. This is the literal restatement the dispatch describes, and it
is safe and low-risk to consolidate into one shared test-support module.

**F2 — Grid configurations are *not* the same data restated (do not force-merge).** Three grids
exist and each encodes a distinct property, not a copy of another:
- `test_search_period_coverage.py`'s `_GRID` (`[(2,1,2),(3,1,3),(4,1,4),(5,1,5),(6,1,6)]`) pins
  the search's non-monotonicity in `back`/`fwd` (divisibility-by-period).
- `test_structure.py`'s `_A0_SWEPT_GRID` (11 points, including `mid=0` and asymmetric
  `back`≠`fwd` points) pins the A0 frame-class standing test's independence from that same
  non-monotonicity.
- `test_certificate_a2_triangle.py`'s own two-grid parametrize table (`back=mid=fwd=1` and
  `back=2,mid=1,fwd=2`) exists to catch one specific, previously-real defect (local coherence
  generated over the narrow `target_window()` instead of the wide `_coherence_window` — see that
  module's docstring) that only the wider grid can see.

  A single "declarative registry of grids" spanning all three would either (a) force these
  independent parameter tables to share entries they have no logical reason to share, coupling
  three unrelated test purposes so a future edit to one can silently perturb another, or (b) just
  relocate three still-separate tables into one file with no reduction in what a reader has to
  understand at each call site. Recommend: **do not merge the grids.** Keep each grid local to
  the module whose property it exists to pin, with the module docstring stating *why* (already
  the case for all three).

**F3 — Tier membership expressed three ways is not one fact restated three times.** The dispatch
observes that tier membership lives in (a) `test_certificate_a2_triangle.py`'s module docstring
prose ("Two tiers: Tier 1 ... Tier 2 ..."), (b) per-class/per-case `@pytest.mark.slow` markers,
and (c) a `SKIP_REASON`-driven `skipif` keyed on `BIMODAL_LOGIC_PATH` availability (applied at
three independent sites: module-level in `test_certificate_lean_agreement.py`, class-level on
`TestBoundedLeanCrossCheck` in `test_certificate_a2_triangle.py`, and class-level in
`test_semantics_core.py`). These are not redundant copies of the same fact — they are three
different *mechanisms* pytest requires at three different decision points: prose documents intent
for a human reader, `slow` controls local `-m "not slow"` deselection, and `skipif` controls
environment-availability gating. Consolidating the *skip* plumbing was already done once
(`_lean_check.py`'s `SKIP_REASON`/`PROTOCOL_FAILURE` split, explicitly built so a probe regression
cannot silently disappear as a clean skip again — see that module's own docstring for the
regression this fixed). There is no further consolidation available here that would not either
duplicate pytest's own marker/skipif mechanics into a home-grown wrapper (added indirection, no
duplication removed) or touch Tier 2's clean-skip behavior, which the dispatch requires this task
preserve as-is. **Recommend no change to the tier-gating mechanism.**

**F4 — `_pinned_eval.py`'s location already matches this repository's own precedent.**
`_pinned_eval.py` (the compile-once evaluator and `PinnedAssignmentBuilder`) and `_lean_check.py`
(the Lean subprocess/skip-resolution helper) are both non-test, library-like modules living
inside `tests/` under a leading-underscore name — a convention this task's own sibling files
already established, not one this task would be introducing. No other theory
(`logos`/`exclusion`/`imposition`) has an analogous test-support module outside its test tree; the
closest counterpart per theory (`semantic/helpers.py` for imposition) is production code serving
production callers, not test-only support code. Moving `_pinned_eval.py` into `theory_lib` proper
would be a real elevation in surface area (a stable public API, docs, likely its own `tests/`
directory) that only makes sense if it becomes a *shipped* artifact — exactly the promotion
decision task 205's own description reserves for itself ("evaluating promoting a checker onto the
production path"). **Recommend leaving `_pinned_eval.py` where it is now.** If task 205 decides to
promote a checker, the natural destination is alongside `certificate.py` in `semantic/` (mirroring
that module's own home) with a narrowed public surface (today's `__all__` already lists every
name deliberately, which would ease that future move) — stated here as the implication for
coordination, not decided here.

### Performance

**F5 — The authoritative numbers reproduce.** Running
`test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` standalone (`pytest ... --timeout=300
--timeout-method=thread`, this host, no `-n`) measured **111.99s** (`1 passed in 113.36s`); a
second, script-level reproduction (bypassing pytest overhead entirely, calling the same
`_candidates`/`recheck`/`compile_and_bind` code paths directly) measured **110.89s** and
**111.85s** across two runs. All three are consistent with the CI-shaped **123.29s** already on
record (the gap is exactly the kind of `-n 4` worker-contention overhead the docstring's own
2.4x-slower-CI-hardware margin already accounts for).

**F6 — Structure build and one-time compile are not the bottleneck.** Measured directly for the
`nb2_nf2` boxed case: `_build(...)` (the real `Syntax -> ModelConstraints -> BimodalStructure`
pipeline, including the actual Z3 solve) took **0.024s**; `compile_and_bind(structure)` (walking
23 constraints, interning 26 atoms) took **0.0056s**. Combined, these are **0.02%** of the
110s-plus total. This directly answers two of the four routes the dispatch asks to compare:

- *"Sharing solved structures across cases through pytest fixtures instead of re-solving per
  test"*: there is exactly one place in the suite where the identical structure
  (`[\Box A] |- [B]`, `back=mid=fwd=1`) is built twice —
  `TestExhaustiveTriangleWithBox.test_boxed_closure_enumeration_agrees_with_z3` and
  `TestBoundedLeanCrossCheck`'s `boxed_closure_sat` parametrize case. But the latter is
  `skipif`-gated on `BIMODAL_LOGIC_PATH`, which no `.github/workflows/*.yml` ever sets (grepped
  all six workflows; zero hits) — so in every CI run today, that second build never executes.
  Fixture-sharing would save ~0.03s in a local run with a BimodalLogic checkout present, and
  nothing in CI. **Not worth doing for the stated 300s-ceiling problem**; it is a legitimate,
  independent, much lower-priority local-developer-experience cleanup if pursued at all.
- *"Caching or reusing the compiled evaluator across configurations"*: `compile_and_bind` already
  runs exactly once per structure (before the candidate loop), so within-test reuse is already
  maximal. Across *different* configurations (different grids, different closures), the compiled
  closures are bound to that configuration's own Z3 AST and atom index — there is nothing
  structurally shared to reuse. **No measurable opportunity here.**

**F7 — Root cause: `target_window` iterates innermost, and ~96.5% of `recheck`'s per-candidate
cost does not depend on `target_time`.** `_candidates()` (both the production test file's and
this report's reproduction) generates `for family in ...: for t in target_window: yield family,
t` — every `target_window_len` consecutive candidates share the identical `WitnessFamily` Python
object. `recheck()`'s structural check, (C1) local coherence, (C2) fulfilment, and (C3) box
faithfulness (`certificate.py`'s `_coherent_at`/`_fulfil_at`/`_box_faithful`, plus
`closure_of(premises + conclusions)`) take no `target_time` argument at all; only (C4)
(`_target_holds`) does. Micro-benchmark on this host (20,000 calls, same family, varying `t`):
family-only cost **21.83us**, C4-only cost **0.80us** — **96.5%** of `recheck`'s work is being
recomputed `target_window_len` times per family for no reason (`target_window_len` is 5 for the
`nb2_nf2` grid: `nb+nm+nf = 2+1+2`). The pinned evaluator has the identical structure:
`PinnedAssignmentBuilder.assign()`'s `lab_`/`bx_` resolvers ignore `target_time`; only `sel_`
resolvers use it (`_pinned_eval.py:313-349`).

**F8 — Measured fix: amortize the family-only work across its `target_window` repeats.**
Built a script-level reproduction of the exact production code paths (`_candidates`, `recheck`,
`compile_and_bind`, `PinnedAssignmentBuilder`) plus a single-slot cache keyed on `id(family)` —
correct precisely because consecutive candidates share the same family object, and always
*correct* (never silently wrong) even if a future change to iteration order defeated the cache,
since a cache miss just recomputes from scratch. Two measurements, same host, same structure
(`[] |- [\Box A]`, `back=2, mid=1, fwd=2`, the widest boxed case):

| Variant | Wall clock | `total`/`accepted`/`pinned_accepted` |
|---|---|---|
| Baseline (current code paths, no caching) | 110.89s / 111.85s (two runs) | 10,485,760 / 5,115 / 5,115 |
| + memoize `recheck`'s family-only portion only | 62.18s (**44.4%** reduction, 1.80x) | 10,485,760 / 5,115 / 5,115 |
| + also memoize the pinned evaluator's family-only row entries | **32.31s (70.9% reduction, 3.43x)** | 10,485,760 / 5,115 / 5,115 |

The counts are bit-for-bit identical to the baseline in every variant — **nothing is narrowed**;
every one of the 10,485,760 candidates is still individually enumerated and independently
checked by both legs. Extrapolating this measured 70.9% ratio onto the CI-shaped, already-recorded
numbers (a linear extrapolation, not independently re-measured under `-n 4` over the real target
set): the widest case would move from **123.29s to roughly ~36s**, and the second boxed case
(17.77s, whose grid has `target_window_len = 3` — an even larger fraction eligible for caching)
would move from **17.77s to roughly ~5-8s**. Both would land far inside the 300s ceiling with
headroom well above 85%, versus today's 59%.

**F9 — Where the fix belongs.** Two components need the split, and they sit on opposite sides of
this task's boundary:
- `_pinned_eval.py`'s `PinnedAssignmentBuilder` is test-support code already inside this task's
  territory (`code/src/model_checker/theory_lib/bimodal/tests/`). Splitting `_entries` into a
  family-only group (`lab_`/`bx_`) and a target-time-only group (`sel_`) at construction time, and
  adding a per-family base-row cache the hot loop consults before overlaying `sel_` entries, is a
  self-contained change with no effect outside this module.
- `recheck()`'s family-only portion (structural + C1 + C2 + C3) lives in
  `semantic/certificate.py` — production code shared with the runtime fail-fast guard and every
  other `recheck` caller (`test_structure.py`, `test_semantics_core.py`,
  `test_certificate_lean_agreement.py`). The clean way to expose the decomposition without
  touching any existing caller's behavior is a pure extract-method refactor: pull the
  structural+C1+C2+C3 body into a new function (e.g. `_recheck_family`) that `recheck()` itself
  calls before layering C4 on top, so `recheck()`'s signature, return shape, and behavior for
  every existing caller are unchanged byte-for-byte, and the harness (or any future caller with
  the same target-window-innermost shape) can call `_recheck_family` once per family and reuse
  its result. This is the one piece of the performance recommendation that touches a file outside
  `tests/`; flagging it explicitly rather than letting it pass as an implicit part of "harness
  refactoring," per the dispatch's own instruction not to absorb scope quietly. It changes no
  soundness-relevant logic (pure extraction) and stays entirely on this task's side of the
  trust-boundary line task 205 owns.
- The single-slot, object-identity cache is coupled to `_candidates()`'s current
  family-outer/target_time-inner loop order. Recommend making that coupling explicit and
  structural rather than incidental: refactor the harness's own enumeration into an outer loop
  over families and an inner loop over `target_window`, computing each family's cached
  family-only verdict/base-row exactly once per outer iteration, rather than relying on a generic
  memoization trick riding on a generator's current shape. This also makes the ~70.9% saving
  robust against a future, unrelated change to `_candidates()`'s iteration order (today's
  single-slot cache would silently fall back to zero benefit, never to a wrong answer, but a
  structural loop split removes that failure mode instead of merely tolerating it).

**F10 — Route "move the widest case to a scheduled run" has strong in-repo precedent, but is a
secondary decision after F8's fix, not a replacement for it.** `code/pyproject.toml` already
registers a `performance` marker that `.github/workflows/tests.yml:208` already excludes from the
gating pass (`-m "not packaging and not performance and not unstable and not xdist_serial"`); the
second, `xdist_serial` pass (`tests.yml:214`) would not pick it up either (it is gated on
`xdist_serial` membership, not "everything else"). **However, `performance`-marked tests are
currently a complete CI no-op**: grepping every workflow in `.github/workflows/` for
`performance` finds only that one exclusion clause — no workflow ever runs `-m performance`
anywhere. The two existing consumers of that marker
(`code/tests/integration/test_performance.py`, `builder/tests/test_refactoring_target_behavior.py`)
are therefore never executed in CI today, which is exactly the "silent bit-rot" failure mode
`TESTING_GUIDE.md` section 8.8 warns about for the oracle exhaustive scan, minus that section's
antidote (`oracle/check-scan-freshness.sh`, a mandatory paired staleness check). If the widest
case is moved off the per-PR path, do **not** simply apply the `performance` marker and consider
it handled — that would make the loudest test in the suite silently stop running altogether,
worse than the status quo. The repository already has a complete, working template for doing this
correctly: `.github/workflows/unstable-watch.yml` (nightly `schedule:` + `workflow_dispatch`,
explicitly non-gating, `continue-on-error` classification) and
`TESTING_GUIDE.md` section 8.8's "scheduled off-hours, never gating" decision for the oracle
exhaustive scan, paired with its own freshness check. Given F8's measured ~36s projection already
clears the 300s ceiling with ~88% headroom, **recommend implementing F8 first and re-measuring
under the true CI-shape before deciding whether F10 is still needed** — it may no longer be, and
if it is, use the `unstable-watch.yml` template plus a freshness check, never a bare marker
change.

## Decisions

- **Organization**: consolidate the four duplicated `_settings`/`_build` helpers into one shared
  test-support module (F1); do not merge the three grids (F2); do not restructure the
  tier-gating mechanism (F3); leave `_pinned_eval.py`'s location as-is pending task 205's
  promotion decision (F4).
- **Performance**: the primary recommendation is the measured algorithmic fix (F7-F9), not a
  scheduling change. Fixture-sharing and cross-configuration evaluator caching are rejected as
  routes for the 300s-ceiling problem specifically (F6) — both measured, not assumed, to save a
  ~0.03s combined per test against a 110s-plus total, and the one scenario where fixture-sharing
  would even apply never executes in CI. A scheduled-run move is deferred pending
  re-measurement after the algorithmic fix lands (F10), and if still pursued, must ship with a
  freshness check, following `oracle/check-scan-freshness.sh`'s precedent, not the currently-inert
  `performance` marker alone.

## Recommendations

1. **(Organization, low risk)** Extract `_settings`/`_build` into one shared, leading-underscore
   test-support module under `tests/` (naming to match this tree's own convention, e.g.
   `_build_support.py`), and update the four call sites
   (`test_certificate_a2_triangle.py`, `test_search_period_coverage.py`, `test_structure.py`,
   `test_pinned_eval.py`) to import it. No behavior change; removes ~40 lines of exact
   duplication across four files.
2. **(Performance, primary)** In `_pinned_eval.py`, split `PinnedAssignmentBuilder`'s per-atom
   entries into family-only (`lab_`/`bx_`) and target-time-only (`sel_`) groups at construction
   time; cache the family-only base row keyed to the current family. Fully within this task's own
   territory.
3. **(Performance, primary, touches production code — flagged per F9)** In `semantic/certificate.py`,
   extract `recheck()`'s structural + (C1) + (C2) + (C3) body into a new function (e.g.
   `_recheck_family`), with `recheck()` becoming a thin composition of that function and (C4).
   Pure extraction; every existing caller's behavior is unchanged. Add a direct equivalence test
   (`recheck(...) == compose(_recheck_family(...), _target_holds(...))` for a representative
   sample) before wiring the harness to call the split function.
4. **(Performance)** Restructure `_run_exhaustive_triangle` (and the analogous Tier 2 sampling
   loop, if it reuses the same generator) into an explicit outer-loop-over-families,
   inner-loop-over-`target_window` shape, so the amortization in (2)/(3) is structural rather than
   an incidental consequence of `_candidates()`'s current generator order.
5. **(Performance, secondary, do after 2-4 and re-measurement)** Re-run the CI-shaped invocation
   (`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and
   not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`) over the real target set and
   record the new numbers for both boxed cases in the module docstring (matching this module's
   own existing convention of recording measured numbers in place). Only pursue a scheduled-run
   move (F10) if headroom is still judged inadequate after this remeasurement; if pursued, follow
   the `unstable-watch.yml` template and pair it with a freshness check.
6. **(Verification, every phase)** Run the bimodal suite
   (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`), the
   four-theory gate (`PYTHONPATH=code/src pytest code/tests/ -q`), and confirm the
   repository-wide target set stays green, per the dispatch's own verification instruction.

## Risks & Mitigations

- **Risk**: the single-slot family cache silently degrades to no benefit if a future edit
  reorders `_candidates()`'s loops. **Mitigation**: Recommendation 4 makes the amortization
  structural rather than incidental, removing the dependency on generator iteration order
  entirely; until that lands, the cache is always *correct* on a miss (never wrong), only
  potentially slower.
- **Risk**: extracting `_recheck_family` out of `recheck()` (Recommendation 3) touches production
  code shared by the runtime fail-fast guard. **Mitigation**: pure extract-method, no logic
  change, with a dedicated equivalence test guarding the composition before any caller is
  switched over; this is explicitly flagged to the team rather than folded silently into "harness
  refactoring."
- **Risk**: a future scheduled-run move (F10) repeats the currently-inert `performance` marker
  pattern and silently stops running the moved test. **Mitigation**: Recommendation 5 requires a
  companion freshness check (per `oracle/check-scan-freshness.sh`'s precedent) as a condition of
  making that move, not an optional follow-up.

## Appendix

- CI's exact per-PR gate command: `.github/workflows/tests.yml:208` (`-m "not packaging and not
  performance and not unstable and not xdist_serial" -n 4 -q --timeout=300
  --timeout-method=thread`, over `tests/ src/model_checker`).
- Marker registry: `code/pyproject.toml`'s `[tool.pytest.ini_options] markers` list.
- Scheduled-workflow precedent: `.github/workflows/unstable-watch.yml`;
  `code/docs/core/TESTING_GUIDE.md` section 8.8 ("Exhaustive-scan cadence decision: scheduled
  off-hours, never gating") and its `oracle/check-scan-freshness.sh` staleness-check pairing.
  Section 8.14 records the `development` marker's full retirement, confirming bimodal carries no
  other currently-active blanket-gating mechanism this task needs to account for.
  `git log` confirms task 207 ("fix stale `all_constraints` snapshot") is `completed`, and
  `_pinned_eval.py`'s `full_constraints` docstring already documents having been proven equivalent
  and converted to a named alias rather than a workaround, ahead of this task.
