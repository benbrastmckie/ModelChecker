# Research Report: Fix Shared Model Iterator's `is_world` Assumption

- **Task**: 189 - Fix shared model iterator's `is_world` assumption so bimodal can iterate
- **Started**: 2026-09-25T16:10:00Z
- **Completed**: 2026-09-25T17:05:00Z
- **Effort**: ~1 hour (codebase exploration, live reproduction, prior-art cross-check)
- **Dependencies**: None (bimodal certificate-encoding redesign, prior task's Phase 15, is already
  merged; this closes the gap that phase deliberately deferred)
- **Sources/Inputs**:
  - `code/src/model_checker/iterate/models.py` (`ModelBuilder.build_new_model_structure`,
    `_initialize_z3_dependent_attributes`)
  - `code/src/model_checker/iterate/constraints.py` (`ConstraintGenerator`)
  - `code/src/model_checker/iterate/core.py` (`BaseModelIterator`, the live orchestrator)
  - `code/src/model_checker/iterate/iterator.py` (`IteratorCore` — dead code, see Findings)
  - `code/src/model_checker/iterate/base.py` (abstract `BaseModelIterator` — dead code, see
    Findings)
  - `code/src/model_checker/iterate/graph.py` (`IsomorphismChecker`)
  - `code/src/model_checker/theory_lib/{logos,imposition,exclusion,bimodal}/iterate.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, `semantic/certificate.py`
  - `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md`, `ARCHITECTURE.md`
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
    (Phase 15, the prior task that discovered and deliberately deferred this exact gap)
  - Live reproduction via `dev_cli.py` and `pytest` (commands and output in Findings)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- Two independent, already-diagnosed defects, both confirmed live in this session: (1) an
  unguarded `semantics.is_world(state)` call in `models.py:91-97` raises `AttributeError` for
  bimodal on the *second* model of any `iterate: N > 1` run; (2) even once that crash is patched,
  `constraints.py`'s `ConstraintGenerator` (lines 204, 251) generates **no** exclusion constraint
  at all for bimodal, so nothing forces successive models to differ.
- The shared framework already declares a proper theory-specific extension point for exactly this
  purpose: `core.py`'s `BaseModelIterator._create_difference_constraint` /
  `_create_non_isomorphic_constraint` / `_create_stronger_constraint` (lines 709-758) are
  documented abstract hooks ("should be overridden by theory-specific implementations"), and
  **all four theories already provide concrete overrides** (`logos/iterate.py:215,329`,
  `imposition/iterate.py:369,430`, `bimodal/iterate.py:97,110`, exclusion inherits Logos's). The
  defect is not a missing extension point — it is that the live loop never calls it. `core.py`'s
  `iterate_generator()` (lines 249, ~340) calls `self.constraint_generator.create_extended_constraints`
  / `.create_stronger_constraint` instead, which live on a separately-instantiated, theory-agnostic
  `ConstraintGenerator` that reimplements its own generic, `is_world`-gated version of the same
  logic and never delegates to the per-theory override.
- Consequence beyond bimodal: this means the per-theory `_create_difference_constraint` overrides
  in **all four** theories' iterators (not just bimodal's) are currently dead code from the live
  loop's perspective — Logos's own override, e.g., builds richer world-count/letter-value/structural
  constraints than `ConstraintGenerator`'s generic version, and it too is never invoked. This is
  why any fix that "consults" the per-theory hooks live is a behavior change worth a real
  cross-theory regression pass, not a paperwork formality.
- Explicitly confirmed: `BimodalSemantics` fixes `N = 0` by design (certificate encoding has no
  bitvector state space) and defines no `is_world`; a shim would misrepresent the model theory
  (D3/D4) and must not be added — matches the dispatch's explicit instruction.
- Regression surface is small and already green: 4 per-theory live `iterate:N>1` test files, 19
  tests total, all passing today (baseline captured below). Bimodal has **no** live end-to-end
  `iterate: N>1` test yet — its existing tests deliberately call `_create_difference_constraint`
  etc. directly, bypassing the live loop, precisely because the loop couldn't be exercised
  end-to-end until now.
- This is not fresh discovery: the exact root cause, exact line numbers, and exact recommended
  minimal fix are already documented in three places that agree with each other and with this
  report — `bimodal/iterate.py`'s module docstring, `bimodal/docs/ITERATE.md`'s "A Live
  Limitation" section, and task 184's own plan (Phase 15, `[COMPLETED WITH EXCLUSIONS]`), which
  deliberately deferred exactly this fix as out-of-scope, cross-theory, follow-on work.

## Context & Scope

Task 189 asks for the shared `model_checker/iterate` framework to stop assuming every theory
implements `semantics.is_world()`, so that bimodal's certificate-encoding iterator (rewritten in
task 184's Phase 15) can run `iterate: N > 1` without crashing and without silently returning
duplicate/unexcluded models. The fix must not touch `BimodalSemantics` to add a fake `is_world`,
and must not regress logos/imposition/exclusion, which all currently satisfy the `is_world` gate.

Concurrency note: task 191 is scheduled for research in this same `/orchestrate` cycle with no
declared `file_scope` (may touch anything). No overlap with this task's content was found or
assumed; flagging only per the standard territory contract — re-check `git status`/`git log`
before any implementation-phase edit to the files below.

## Findings

### 1. The crash: unguarded `is_world` call, `models.py:91-97`

`ModelBuilder.build_new_model_structure` rebuilds a fresh `ModelStructure` from a Z3 model found
during iteration, by pinning every state's concrete predicate values into a temporary solver
before re-solving:

```python
for state in range(2**semantics.N):
    is_world_val = z3_model.eval(semantics.is_world(state), model_completion=True)   # line 93
    ...
    if hasattr(semantics, 'possible'):        # line 101 — guarded
    ...
if hasattr(semantics, 'verify'):               # line 110 — guarded
    ...
    if hasattr(semantics, 'falsify'):          # line 123 — guarded
```

Only the `is_world` block (lines 91-97) lacks the `hasattr` guard its three neighbors in the same
function already use. A second, already-guarded `is_world` check exists later in the same file
(`models.py:237`, inside `_initialize_z3_dependent_attributes`) — but that method is itself dead
code (see Finding 4), so it offers no protection.

For bimodal, `BimodalSemantics.__init__` sets `self.N = 0` unconditionally (a vestigial attribute
the shared framework reads; the certificate encoding's real carrier is `{0,...,k} x Z`, not
bitvector states — `semantic/core.py:138`), so `range(2**0) == range(1)`: the loop body runs
exactly once and immediately raises, because `BimodalSemantics` defines no `is_world` at all.

**Live reproduction** (this session, via `dev_cli.py` against a real bimodal countermodel example
with `iterate: 3`):

```
Failed to build model structure: 'BimodalSemantics' object has no attribute 'is_world'
...
  File ".../iterate/models.py", line 93, in build_new_model_structure
    is_world_val = z3_model.eval(semantics.is_world(state), model_completion=True)
AttributeError: 'BimodalSemantics' object has no attribute 'is_world'
...
  File ".../iterate/core.py", line 296, in iterate_generator
    new_structure = self.model_builder.build_new_model_structure(new_model)
model_checker.iterate.errors.ModelExtractionError: Failed to extract model 1: ...
```

The first certificate is found and printed correctly; the crash happens building the *second*.
This matches `bimodal/docs/ITERATE.md`'s own "A Live Limitation" section exactly, including the
stated reason it slipped past the 366/366-green suite: no example in `examples.py` sets `iterate`
above its default of `1`, so `max_iterations == 1` short-circuits before this code path is ever
reached (`core.py:161-163`).

### 2. The silent gap: `ConstraintGenerator`'s exclusion logic is entirely `is_world`-gated

Independent of the crash, `constraints.py`'s `ConstraintGenerator` — the class that actually
supplies the live loop's "exclude previously-seen models" constraints — gates both of its
constraint-building methods on `hasattr(semantics, 'is_world')`:

- `_create_state_difference_constraints` (`constraints.py:204`)
- `_create_non_isomorphic_constraint` (`constraints.py:251`)

For bimodal, both `hasattr` checks are `False`, so both methods fall through and return an empty
list / `None`. `_create_difference_constraint` (`constraints.py:149-185`) then sees an empty
`difference_constraints` and also returns `None`. Net effect once the crash above is patched:
`create_extended_constraints` (`constraints.py:86-103`, called from `core.py:249`) contributes
**nothing** to the solver for bimodal — Z3 is free to return the same certificate, or an
arbitrarily related one, on every subsequent "model N" search. This is a silent correctness gap,
not a crash, and would not be caught by any test that only checks "iteration doesn't raise."

### 3. The extension point already exists — the live loop just never calls it

`core.py`'s `BaseModelIterator` declares three theory-specific hooks as documented,
must-override-style methods (each defaults to `raise NotImplementedError`, lines 709-758):

- `_create_difference_constraint(self, previous_models) -> BoolRef`
- `_create_non_isomorphic_constraint(self, isomorphic_model) -> BoolRef`
- `_create_stronger_constraint(self, isomorphic_model) -> Optional[BoolRef]` (declared in
  `base.py`'s dead copy with a default `None`; `core.py`'s copy also `raise`s by default)

Every theory's `*ModelIterator` (all subclass `core.BaseModelIterator`) already provides a
concrete override:

| Theory | `_create_difference_constraint` | `_create_non_isomorphic_constraint` |
|---|---|---|
| Logos | `logos/iterate.py:215` (world-count + verify/falsify letter-value + structural constraints, in escalating complexity order) | `logos/iterate.py:329` |
| Imposition | `imposition/iterate.py:369` | `imposition/iterate.py:430` |
| Exclusion | inherited from `LogosModelIterator` (own override only for `_calculate_differences`, `exclusion/iterate.py:26`) | inherited |
| Bimodal | `bimodal/iterate.py:97` (blocking clause over every label-bit/box-guess certificate variable, via `_certificate_variables()`/`_blocking_clause()`) | `bimodal/iterate.py:110` |

**None of these four overrides is ever called from the live search loop.** Confirmed by
exhaustive grep: the only call sites for `self._create_difference_constraint` /
`self._create_non_isomorphic_constraint` anywhere in `code/src/model_checker/iterate/*.py` or
`theory_lib/*/iterate.py` are inside `ConstraintGenerator` itself
(`constraints.py:99,147`), calling `ConstraintGenerator`'s *own*, separately-implemented,
generic, `is_world`-gated methods of the same name — not the polymorphic iterator methods. The
live loop (`core.py:249`, `core.py:296`, and the analogous "stronger constraint" call near
`core.py:339`) only ever talks to `self.constraint_generator` (an instance of `ConstraintGenerator`,
constructed unconditionally in `BaseModelIterator.__init__`), never to `self._create_difference_constraint`
directly. `bimodal/iterate.py`'s own module docstring and `ITERATE.md`'s "How Model Diversity Is
Actually Enforced" section both name this exact call chain already (independently, for bimodal
only); this session's grep confirms it is equally true of Logos, Imposition, and Exclusion — their
richer per-theory constraint logic is just as unreachable, it simply happens that `ConstraintGenerator`'s
generic `is_world` fallback "works" for them by coincidence (they all have a real bitvector
world-state predicate the generic fallback can key off), so nobody noticed the duplication.

**Implication for the fix**: this is fundamentally a wiring defect, not a missing-capability
defect. The "proper theory-specific extension point" the task asks for is already fully specified
at `core.py:709-758` and already implemented by every theory; the fix is to make the live loop
call it (directly, or via a thin adapter that keeps `ConstraintGenerator` responsible only for
solver plumbing — `check_satisfiability`, `get_model`, the persistent solver with its timeout —
and stops it from also owning constraint *content*).

### 4. Scope and risk of two candidate fix shapes

**A — Minimal (matches `ITERATE.md`'s own suggested fix)**: guard `models.py:91-97` with
`if hasattr(semantics, 'is_world'):`, mirroring its three neighbors exactly. Fixes the crash only.
Does **not** address Finding 2/3 (bimodal still gets no exclusion constraint) and is exactly the
"special-casing" the dispatch says not to settle for.

**B — Wire the existing extension point (recommended)**: two independent changes—
1. *Constraint exclusion* (Findings 2-3): change `core.py`'s live loop to call
   `self._create_difference_constraint(self.found_models)` /
   `self._create_non_isomorphic_constraint(isomorphic_model)` directly (these are inherited,
   polymorphic, theory-correct today for all four theories) instead of routing through
   `ConstraintGenerator`'s own duplicate implementation. `ConstraintGenerator` keeps
   `check_satisfiability`/`get_model`/the persistent solver, but stops owning
   `_create_difference_constraint`/`_create_state_difference_constraints`/
   `_create_non_isomorphic_constraint` (or those methods are removed/deprecated once nothing
   calls them). `create_extended_constraints`/`create_stronger_constraint`'s call sites
   (`core.py:249`, `~339`) need only wrap the single returned `BoolRef` into the one-element list
   `check_satisfiability` already expects.
2. *Model rebuild* (Finding 1): the crash site (`models.py:91-97`) pins *concrete predicate
   values* from a solved Z3 model into a fresh solver before re-solving — conceptually the exact
   same kind of theory-specific "read this model's certified variables and pin them" operation
   `_create_difference_constraint` already performs for exclusion. There is no existing hook for
   this on `ModelBuilder` today. Two sub-options, in order of architectural cleanliness:
   - **B1**: Add a new, symmetric per-iterator hook, e.g.
     `_pin_model_values(self, temp_solver, z3_model)` on `core.BaseModelIterator` (default
     implementation = today's is_world/possible loop, so Logos/Imposition/Exclusion inherit
     unchanged behavior with zero risk), with `BimodalModelIterator` overriding it to pin
     `_certificate_variables()` (already exists, `bimodal/iterate.py:77-82`) instead. `ModelBuilder`
     would need a reference to the owning iterator (constructor injection: `ModelBuilder(build_example,
     pin_hook=self._pin_model_values)` from `core.py`'s `__init__`, or store `self` on
     `build_example._iterator` — the latter attribute already exists per `bimodal/iterate.py:270`'s
     `example._iterator = iterator`).
   - **B2** (lower-risk, still not "special-casing" at the call site): keep the loop over
     `range(2**semantics.N)` but guard it with `hasattr(semantics, 'is_world')` as in Option A,
     *and* add a symmetric, unconditional call afterward — `self._pin_extra_model_values(temp_solver,
     z3_model)` — that every iterator subclass overrides (default: no-op) to pin whatever theory-
     specific variables it needs (bimodal: `_certificate_variables()`). This changes zero existing
     behavior for the three passing theories (the `is_world` loop still runs exactly as today) while
     giving bimodal a real, non-shimmed extension point rather than a `hasattr` bypass.

**Recommendation for the plan**: B for the constraint-exclusion side (dispatch's phrasing — "bimodal
is the beneficiary" — implies logos/imposition/exclusion's *observable* results, not necessarily
their exact internal Z3 expressions, must not regress; switching to each theory's own
already-correct override is expected to maintain or improve exclusion quality, and the existing
live test suites are the empirical gate). B2 for the model-rebuild side, since it fully isolates
bimodal's new code path from the three passing theories' already-verified loop — satisfies "proper
extension point, not special-casing" (the hook is unconditional polymorphic dispatch, not an
`is_world` check at the call site) while minimizing blast radius on the three theories the dispatch
says must not regress.

### 5. Confirmed: no `is_world` shim should be added

`BimodalSemantics.N = 0` and no state-existence predicate exist by design (D3/D4,
`semantic/core.py`'s own module docstring; `ARCHITECTURE.md`'s "Never Reporting Validity (D8)"
section and "Why ℤ-Time Only" section both describe the certificate encoding's carrier as
`{0,...,k} x Z`, not enumerated bitvector states). A fake `is_world` would misrepresent this and
was already explicitly rejected in task 184's Phase 15 discussion. This report's recommended
designs (B1/B2 above) do not require one.

### 6. Regression baseline (captured live, this session)

```
PYTHONPATH=code/src pytest \
  logos/tests/integration/test_iterate.py \
  logos/tests/integration/test_iterate_generator.py \
  imposition/tests/integration/test_iterate.py \
  exclusion/tests/integration/test_iterate.py \
  bimodal/tests/integration/test_iterate.py -q
=> 19 passed
```

These are the live regression gate for logos/imposition/exclusion (`test_iterate.py`/
`test_iterate_generator.py` run real `iterate: 2` end-to-end loops, not mocks — confirmed by
reading `logos/tests/integration/test_iterate.py:66,133,188`). Bimodal's file currently has **no**
live end-to-end `iterate: N>1` test — every test either mocks `build_example` or patches
`.iterate()` entirely (`bimodal/tests/integration/test_iterate.py:36-63,173`), by its own
module docstring's design ("Deliberately not a full live `iterate: N` end-to-end run"). A new
live test (real `BuildExample` + `BimodalModelIterator.iterate_generator()`, `iterate: 3` on an
existing countermodel example such as `BM_CM_1`) is the only way to actually prove this fix,
and is a mandatory addition, not optional coverage.

### 7. Minor secondary observations (out of this task's scope; flagged only)

- `code/src/model_checker/iterate/base.py` defines a second, unrelated `BaseModelIterator`
  abstract class, confusingly same-named as `core.py`'s concrete one; grep confirms it is imported
  nowhere (`theory_lib/*/iterate.py` all import from `iterate.core`). Fully dead code; candidate
  for future cleanup, not part of this fix.
- `code/src/model_checker/iterate/iterator.py`'s `IteratorCore.iterate()` (and the loop containing
  its own local `ConstraintGenerator`/`ModelBuilder` instantiation, lines ~150-260) is also dead
  code — `core.py`'s `BaseModelIterator.__init__` constructs an `IteratorCore` only to copy a
  handful of attributes off it; `IteratorCore.iterate()`/`iterate_generator()` is never called.
  The live loop is entirely `core.py`'s own `iterate_generator()` (confirmed by this session's
  stack-trace reproduction, which shows `core.py:296`, not `iterator.py`).
- `models.py`'s `_initialize_base_attributes`/`_initialize_z3_dependent_attributes` (lines
  181-249ish) are defined but never called from `build_new_model_structure` or anywhere else in
  the module — a second guarded `is_world` check at line 237 lives in dead code, offering no
  actual protection against Finding 1.
- `graph.py`'s `IsomorphismChecker._create_graph` builds its node set from
  `model_structure.z3_world_states` (`graph.py:75`), which `BimodalStructure` never populates
  (grepped; no assignment anywhere in `theory_lib/bimodal/semantic/*.py`). Isomorphism-graph
  dedup is therefore structurally a no-op for bimodal even after this fix — consistent with, and
  presumably why, task 190's plan for bimodal isomorphism rejection works at the exact-difference
  level (certificate variables) rather than via the shared graph-isomorphism path. Not a blocker
  for this task; worth a one-line note in whichever plan implements this fix so it isn't mistaken
  for new/introduced behavior.
- `graph.py:_create_graph` also writes unconditional debug output to `/tmp/graph_debug.log` on
  every call (`graph.py:68-72` and others) — an unrelated pre-existing wart noticed in passing.

## Decisions

- Confirmed in scope: `models.py:91-97` (crash) and `constraints.py:204,251`
  (`ConstraintGenerator`'s silent exclusion gap) are the two defects to fix; both are independently
  necessary (fixing only one leaves the other).
- Confirmed out of scope, by dispatch's own framing and this report's Finding 4: rewriting
  `ConstraintGenerator`'s solver-management responsibilities, retiring `iterate/base.py` or
  `iterator.py`'s dead code, or fixing `graph.py`'s isomorphism-graph gap for bimodal. These are
  named in Finding 7 for awareness, not as required deliverables.
- Confirmed: no `is_world` (real or shimmed) is to be added to `BimodalSemantics`.

## Recommendations

1. Fix the crash and the exclusion gap together, not separately — a plan that ships only the
   `hasattr` guard (Option A) leaves Finding 2/3's silent correctness gap in place and does not
   satisfy "introduce a proper extension point rather than special-casing."
2. Adopt Finding 4's Option B for constraint exclusion (wire `core.py`'s live loop to
   `self._create_difference_constraint`/`self._create_non_isomorphic_constraint`, already
   implemented per-theory) and Option B2 for the model-rebuild pinning step (new, symmetric,
   unconditionally-dispatched hook with a no-op default, overridden by bimodal to pin
   `_certificate_variables()`), per the risk analysis in Finding 4.
3. Add a **live**, non-mocked `iterate: N > 1` test to
   `bimodal/tests/integration/test_iterate.py` (there is currently none) — e.g. real
   `BuildExample` + `BimodalModelIterator` against `BM_CM_1` with `iterate: 3`, asserting no
   exception and that returned certificates pairwise differ in at least one label bit or box
   guess. This is the only test that actually exercises the fix; every existing bimodal iterate
   test calls the per-theory methods directly or mocks the loop.
4. Re-run this session's exact regression baseline (Finding 6's four-file, 19-test command) after
   the change and treat any newly-failing case in logos/imposition/exclusion as a real regression,
   not an acceptable side effect — this is the concrete form of "must not regress."
5. Update `bimodal/docs/ITERATE.md`'s "How Model Diversity Is Actually Enforced" and "A Live
   Limitation" sections (and `ARCHITECTURE.md`'s "Model Iteration" section) once fixed — both
   currently document the crash and the gap as live, reproduced limitations with "use `iterate: 1`
   until this is fixed" guidance; leaving that guidance in place after the fix would be stale and
   misleading documentation.
6. Treat Finding 7's dead-code observations as informational only; do not fold their cleanup into
   this task's plan unless the planner judges the risk/benefit favorable on its own terms.

## Risks & Mitigations

- **Risk**: switching the live loop to call Logos/Imposition/Exclusion's own (richer, previously
  unreached) `_create_difference_constraint` overrides changes what Z3 constraints those three
  theories actually solve against, even though their own unit-level tests (which call these
  methods directly) already pass. **Mitigation**: Finding 6's baseline is the regression gate;
  additionally spot-check that a representative `iterate: 3` run for each of the three theories
  still returns the same *count* of models with the same expected pairwise-distinctness property
  before/after, not merely that the test suite stays green (tests may share fixtures that don't
  exercise every code path Logos's constraint escalation logic can take).
- **Risk**: `ModelBuilder` needs a reference to the owning iterator instance (for the B1/B2 hook)
  that it does not have today (`models.py`'s `ModelBuilder.__init__` only takes `build_example`).
  **Mitigation**: `bimodal/iterate.py:270`'s existing `example._iterator = iterator` assignment
  shows the codebase already has a precedent for stashing the iterator on `build_example`; either
  reuse that attribute or pass the hook explicitly through `core.py`'s existing
  `ModelBuilder(build_example)` construction call — both are small, mechanical changes.
- **Risk**: `check_satisfiability`'s current signature takes a `List[BoolRef]`
  (`constraints.py:105-125`), while the polymorphic `_create_difference_constraint` returns a
  single `BoolRef`. **Mitigation**: trivial adapter (`[constraint] if constraint is not None else
  None`) at the two call sites; no signature change needed to `ConstraintGenerator` itself.

## Appendix

- Reproduction commands (this session):
  - `PYTHONPATH=code/src pytest <4 iterate test files> -q` -> 19 passed (baseline).
  - `PYTHONPATH=code/src python3 dev_cli.py <scratch example with iterate:3>` ->
    `AttributeError: 'BimodalSemantics' object has no attribute 'is_world'` at `models.py:93`,
    wrapped as `ModelExtractionError`, raised from `core.py:296` via `bimodal/iterate.py:213,272`.
- Prior art (all independently corroborate this report's Findings 1-3):
  - `code/src/model_checker/theory_lib/bimodal/iterate.py` module docstring, section
    "`_create_difference_constraint`/`_create_non_isomorphic_constraint` are interface-parity
    methods, not the live loop's exclusion mechanism".
  - `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md`, sections "How Model Diversity Is
    Actually Enforced" and "A Live Limitation: `iterate: N > 1` Currently Crashes".
  - `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`, section "Model Iteration".
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`,
    Phase 15 (`[COMPLETED WITH EXCLUSIONS]`) and its Reasoned Exclusions table.
