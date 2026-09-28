# Research Report: Fix stale `ModelConstraints.all_constraints` snapshot

- **Task**: 207 - Fix stale `all_constraints` snapshot; audit every production reader
- **Started**: 2026-09-28T00:07:00Z
- **Completed**: 2026-09-28T00:45:00Z
- **Effort**: ~40 minutes
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/models/constraints.py`
  - `code/src/model_checker/models/structure.py`
  - `code/src/model_checker/iterate/models.py`, `iterate/constraints.py`, `iterate/core.py`, `iterate/build_example.py`
  - `code/src/model_checker/theory_lib/bimodal/{iterate.py,semantic/core.py,semantic/model.py}`
  - `code/src/model_checker/theory_lib/{logos,exclusion}/semantic/core.py`
  - `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
  - `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py` (`full_constraints()`)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` (`_real_build_example` pattern, reused for two empirical probe scripts written to the scratchpad, not committed)
  - `.github/workflows/tests.yml` (CI gate invocation shape)
  - `specs/archive/189_fix_shared_iterator_is_world_assumption/baselines/05_defect2-3-reproduction.md` (related, distinct prior defect, checked to rule out overlap)
- **Artifacts**: This report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- Root cause is confirmed exactly as localized in the dispatch: `models/constraints.py:97`'s
  `all_constraints = frame_constraints + model_constraints + premise_constraints +
  conclusion_constraints` is a one-time list concatenation taken before bimodal's
  `finalize_certificate()` ever runs, so it permanently omits the (C1)-(C4) certificate
  constraints for every bimodal solve, not only iterated ones. Empirically confirmed: the
  *first* bimodal model in a live run has `all_constraints` length 2 against a true solved set
  of 132 constraints.
- **`all_constraints` is never read by the actual solve, for any theory.** `models/structure.py`'s
  `_setup_solver` (base class, used unmodified by logos/exclusion/imposition, and reached via
  `super()` after bimodal's own `finalize_certificate()` call) always builds the tracked solver
  from the four component lists directly. This makes every reader of `all_constraints`
  diagnostic/derivative, never solve-determining, which substantially de-risks the fix.
- Reader 1 (`iterate/models.py:93`/`:152`, the iterator's model-rebuild base-constraints ingestion
  and pin write-back): for **bimodal**, empirically confirmed **unreachable** — the independent
  `recheck()` re-checker (`semantic/certificate.py`) passes (C1)-(C4) on every rebuilt model in a
  live `iterate: 3` run, because `theory_lib/bimodal/iterate.py`'s `_pin_theory_specific_values`
  already bypasses the dead `all_constraints` path entirely (a previously-discovered and already-
  fixed bug, documented in that file's own docstrings as the "second" and "third discovered
  bug"). This bypass is *why* it is unreachable today, not because `all_constraints` itself is
  correct.
- **New finding, beyond the three named readers**: the *same* dead-`all_constraints` mechanism
  that reader 1 describes for bimodal also breaks the **generic** `is_world`/`verify`/`falsify`
  pinning `iterate/models.py` performs for the three single-phase theories (logos, exclusion,
  imposition), which have no theory-specific override. Their pins are written only into
  `temp_solver` and then `model_constraints.all_constraints` (line 152) — an attribute nothing
  downstream reads — so the rebuilt `ModelStructure`'s real solve is effectively **unpinned**.
  Empirically confirmed for logos: a rebuilt second model's `is_world` assignment is a fresh,
  independent Z3 solution to the base constraints alone, not a value set validated against the
  iterator's own difference/exclusion search. This is a real, currently-live gap, distinct from
  (but caused by the same root fact as) the bimodal two-phase-emission gap this task was opened
  for. It is flagged here for visibility and a follow-up decision, not fixed by this task.
- Reader 2 (`iterate/constraints.py:51-52`) is fully dead: `original_constraints` is computed and
  then used only in a `logger.debug(...)` call; nothing else references it.
- Reader 3 (`models/structure.py`'s `_get_relevant_constraints`, lines 429/435) is confirmed
  display-only (`print_grouped_constraints`/verbose and `--save` output), exactly as scoped —
  and, per A2_GAP.md, `_setup_solver` never consults it, so the solve path is not implicated.
  **A fourth reader in the same class, not named in the dispatch, was found**:
  `theory_lib/bimodal/semantic/model.py:344-349`'s `save_to` override also prints
  `all_constraints` directly (the `--save --constraints`-equivalent path), with identical
  severity to reader 3.
- Recommended fix direction: convert `all_constraints` to a read-only computed property (the
  view/property option), with the write site at `iterate/models.py:152` folded into the same
  pin-into-the-four-live-lists pattern bimodal's iterate.py already uses — which both restores
  `all_constraints`'s correctness everywhere and, as a beneficial side effect, forces the
  newly-found single-phase pinning gap into the open (a silent no-op write becomes a loud
  `AttributeError` until fixed) rather than leaving it to fail silently indefinitely.

## Context & Scope

Scope is exactly the three readers named in the dispatch plus a full audit of every production
(non-test) site that reads or writes `ModelConstraints.all_constraints`, to ground a fix-direction
recommendation. Test-tree usage (`_pinned_eval.py`'s `full_constraints()`, and existing unit tests
asserting on `all_constraints`) is treated as context for the fix, not as something to change here
(per the dispatch's "preserve the test tree's existing `full_constraints()` behaviour" constraint).
This is a research task; no production code was modified. Two throwaway Python scripts were run
against the real (non-mocked) bimodal and logos iteration paths, using the exact `BuildExample`
construction pattern each theory's own `test_iterate.py` already uses, to answer the "construct a
test, don't reason it out" instruction empirically; the scripts were not committed (scratchpad
only) since this phase produces no code changes.

## Findings

### F1 — Root cause, confirmed

`models/constraints.py:88-97`:
```python
self.frame_constraints = self.semantics.frame_constraints   # reference, not a copy
...
self.all_constraints = (
    self.frame_constraints + self.model_constraints
    + self.premise_constraints + self.conclusion_constraints
)
```
`self.frame_constraints` aliases `semantics.frame_constraints` **by reference**, so it keeps
picking up later `extend()` calls from `finalize_certificate()` (bimodal's two-phase design,
decision D6). `self.all_constraints`, built via list concatenation, is a **new list object**
copying the elements present *at that moment* — before `BimodalStructure._setup_solver` ever runs
`finalize_certificate()`. It is frozen from then on for the lifetime of that `ModelConstraints`
instance.

Empirical confirmation (live `BM_CM_1`, non-iterated first model):
`all_constraints` length **2**, true solved constraint count (`frame + model + premise +
conclusion`, read fresh after solving) **132**. This is worse than the dispatch's framing
suggested: the gap affects **every** bimodal solve (the very first model, not only iterated
ones), because `ModelConstraints.__init__` always runs before `_setup_solver`/
`finalize_certificate` for every theory, and bimodal is the only theory where that ordering
matters (its `frame_constraints` starts empty and grows later; the other three theories populate
their component lists synchronously in `__init__` with nothing added afterward, so their
`all_constraints` snapshot is already accurate today).

### F2 — `all_constraints` is dead code for the actual solve, for every theory

`models/structure.py:162-195`'s `_setup_solver` (the base implementation; logos, exclusion, and
imposition never override it, and bimodal's own override at
`theory_lib/bimodal/semantic/model.py:106` calls `finalize_certificate()` then delegates to
`super()._setup_solver(...)`) builds its four `assert_tracked` groups directly from
`model_constraints.frame_constraints` / `.model_constraints` / `.premise_constraints` /
`.conclusion_constraints`. It never reads `all_constraints`. This was already documented for
bimodal in `A2_GAP.md` ("`models/structure.py`'s `_setup_solver` never reads `all_constraints`");
this research confirms it holds identically for all four theories, because they all share the
same base `_setup_solver`. Consequence: **no reader of `all_constraints` can affect what Z3 is
actually asked to solve** — every reader is either diagnostic/display, or (reader 1) an
intermediate value that is itself discarded before the real solve runs. This substantially
narrows the blast radius of any fix.

### F3 — Reader 1 (`iterate/models.py:93`/`:152`): unreachable for bimodal today, but only because of an existing, separate workaround

Trace for bimodal's `build_new_model_structure`:
1. `for constraint in model_constraints.all_constraints: temp_solver.add(constraint)` (line 93) —
   adds the **stale, near-empty** snapshot (frame_constraints is still whatever it was at the
   *previous* `ModelConstraints.__init__`, i.e. before `finalize_certificate` populated it for
   *this* fresh instance).
2. `self.iterator._pin_theory_specific_values(temp_solver, z3_model, model_constraints)` —
   bimodal's override (`theory_lib/bimodal/iterate.py:190`) calls `finalize_certificate()`
   itself (idempotent) to allocate every lasso/bit/guess, then for every certificate variable
   does **both** `temp_solver.add(pinned)` **and** `semantics.frame_constraints.append(pinned)`.
   The second call is the load-bearing one: `frame_constraints` is the live list
   `model_constraints.frame_constraints` aliases and the one `_setup_solver` will read next.
3. `model_constraints.all_constraints = list(temp_solver.assertions())` (line 152) — overwrites
   `all_constraints` with an intermediate value that is itself never read again (per F2).
4. `model_structure_class(model_constraints, settings)` constructs the rebuilt structure;
   `BimodalStructure._setup_solver` calls `finalize_certificate()` (no-op, already done) then
   reads the four live lists — which now contain (C1)-(C4) *and* every pin — directly.

**Empirical test** (live `BM_CM_1`, `iterate: 3`, real `BuildExample`/`BimodalModelIterator`, no
mocks): all three yielded models' certificates pass the independent S3 `recheck()`
(`semantic/certificate.py`) with `status: "countermodel"` (i.e. every one of (C1)-(C4) genuinely
holds), even though the rebuilt models' `all_constraints` (78 entries) remains far short of the
live four-list total (208 entries) that `_setup_solver` actually used. This directly answers the
dispatch's question: **unreachable, and here is why** — not because `all_constraints`'s staleness
is harmless in general, but because bimodal's iterator already routes around it via the
`frame_constraints.append()` pattern, a fix that predates this task (see the "second" and "third
discovered bug" docstrings in `theory_lib/bimodal/iterate.py:130-262`).

### F4 — New finding: the same dead-`all_constraints` write breaks generic pinning for logos/exclusion/imposition

`iterate/models.py`'s generic pinning loop (world/possible/verify/falsify, lines ~100-132) has
**no theory-specific override for logos, exclusion, or imposition** (only bimodal defines
`_pin_theory_specific_values`; confirmed by grep — no other theory implements it). Their pins are
added only to `temp_solver`, then captured into `model_constraints.all_constraints` at line 152 —
which, per F2, nothing downstream reads. Unlike bimodal's hook, nothing appends these pins into
`frame_constraints`/`model_constraints`/etc.

**Empirical test** (live logos, `N=2`, `[] |- ¬A`, `iterate: 3`, real non-mocked path via
`iterate_example`): the search found 2 models before timing out. The rebuilt second model's
`is_world` bit-signature genuinely differs from the first (`(True, False, False, False)` vs.
`(False, True, True, False)`), and its `all_constraints` (23, capturing the discarded pins) is
larger than the live four-list total actually solved (7, unpinned) — the inverse mismatch
direction from bimodal, confirming the pins never reached the real solve. There is no downstream
consistency check (`iterate/core.py`'s main loop only rejects a rebuild for `None` or zero world
states, never for a values mismatch against the model the differencing search found) that would
catch a divergent rebuild. This means the *displayed* "model 2" for logos/exclusion/imposition is
not verified to be the specific values the iterator's own difference/isomorphism search found —
only that some independent, unpinned resolve of the base constraints happened to be satisfiable
and, in this instance, happened to differ from model 1.

This is a **real, currently-live gap**, mechanistically identical in origin to reader 1 (an
attribute nothing reads is treated as if it were load-bearing) but affecting three theories this
task was not opened to fix, and not something the dispatch anticipated (it frames "single-phase
theories" as "currently correct", which is true of `all_constraints`'s own snapshot accuracy for
those theories, but not of this separate pin-propagation gap). Recommendation: **flag for a
follow-up task** (see Recommendations) rather than fold into this task's fix — it needs its own
theory-by-theory reproduction and severity assessment, and this task's scope (per its own
description) is `all_constraints` correctness, not the pinning mechanism's design.

### F5 — Reader 2 (`iterate/constraints.py:51-52`): dead code

```python
original_constraints = []
if hasattr(build_example, 'model_constraints') and hasattr(build_example.model_constraints, 'all_constraints'):
    original_constraints = build_example.model_constraints.all_constraints
logger.debug(f"Preserved {len(original_constraints)} original constraints for iteration")
```
`original_constraints` is read once more, only inside that `logger.debug` call. Nothing else in
the file (or, per grep, anywhere) references it. The persistent search solver
(`_create_persistent_solver`, same file) is built by copying `build_example.model_structure.
solver.assertions()` directly — not from `all_constraints` at all. Impact of the staleness here is
purely a wrong debug-log count; zero functional impact.

### F6 — Reader 3 (`models/structure.py`'s `_get_relevant_constraints`) and the newly found fourth reader

`_get_relevant_constraints` (lines 415-438) returns `model_constraints.all_constraints` in two
branches: the SAT "SATISFIABLE CONSTRAINTS:" display, and the UNSAT-with-empty-core fallback.
Both are display paths (`print_grouped_constraints`, called from `print_to` when
`print_constraints` is set) — confirmed not on the solve path (F2). For bimodal this means the
printed/`--save`d constraint listing under-reports what was actually solved (2 of 132 for the
non-iterated case above), which is user-visible but not a soundness problem, exactly as the
dispatch anticipated.

**Fourth reader, not named in the dispatch**: `theory_lib/bimodal/semantic/model.py:344-349`'s
`save_to` override (bimodal's `--save`-with-constraints path) independently reads
`self.model_constraints.all_constraints` and prints it verbatim under `# Satisfiable constraints`.
Same severity class as reader 3 (display-only), same theory, same root cause; any fix to
`all_constraints` fixes this reader for free without a separate call-site change, since it already
reads the attribute rather than reconstructing anything locally.

### F7 — The test tree's `full_constraints()` is the right shape for the fix

`theory_lib/bimodal/tests/_pinned_eval.py:391-411`'s `full_constraints(structure)` already
reconstructs the correct value on demand:
```python
def full_constraints(structure):
    mc = structure.model_constraints
    return (
        list(mc.frame_constraints) + list(mc.model_constraints)
        + list(mc.premise_constraints) + list(mc.conclusion_constraints)
    )
```
Its own docstring states the identical root-cause analysis this task confirms independently.
Promoting this shape into `ModelConstraints` itself (as a property) is directly what closes F1,
F3 (defense in depth beyond the existing workaround), F6, and the fourth reader in F6 — all in one
change, without a single reader call site needing to change its own code.

## Decisions

- **Root cause is confirmed as localized in the dispatch; no re-derivation was needed.** F1 adds
  one correction of scope: the gap affects every bimodal solve, not only iterated ones.
- **Reader 1 (iterate/models.py) is confirmed unreachable for bimodal**, evidenced by a live,
  non-mocked `iterate: 3` run whose every rebuilt model passes the independent S3 `recheck()`.
  This is due to an existing, separate defensive fix in `theory_lib/bimodal/iterate.py`, not
  because `all_constraints` is safe in general — any fix must not regress that existing bypass.
- **Reader 2 is dead code** (debug-log-only); no test or behavior depends on its value beyond a
  logged count.
- **Reader 3, plus a fourth reader found in `bimodal/semantic/model.py`'s `save_to`, are both
  display-only**, confirmed by F2 (the solve path never reads `all_constraints`, for any theory).
- **A new, distinct, currently-live gap (F4) was found and is out of this task's scope** to fix —
  it affects logos/exclusion/imposition's iterator rebuild pinning, not `all_constraints`'s
  snapshot timing, and deserves its own reproduction/plan.

## Recommendations

1. **Adopt the computed-property fix direction** for `ModelConstraints.all_constraints`:
   ```python
   @property
   def all_constraints(self) -> List["ExprRef"]:
       return (
           self.frame_constraints + self.model_constraints
           + self.premise_constraints + self.conclusion_constraints
       )
   ```
   This is the `full_constraints()` shape (F7) promoted into production, satisfies "must not
   silently change behaviour for the single-phase theories" (their component lists never mutate
   after `__init__`, so the property returns the identical list, element-for-element, that today's
   eager snapshot returns), and fixes F1/F6/fourth-reader for every reader with zero call-site
   changes, since they only ever *read* the attribute.
2. **The one write site, `iterate/models.py:152`, must be migrated deliberately**, not deleted
   silently — a bare `@property` (no setter) makes `model_constraints.all_constraints = list(
   temp_solver.assertions())` raise `AttributeError` immediately, which is a feature here: it
   forces an explicit decision at the exact place F4's gap lives. Recommend folding this line into
   the same "append the pin literals into the live component lists" pattern bimodal's own
   `_pin_theory_specific_values` already established (`theory_lib/bimodal/iterate.py:260-280`) —
   e.g. append each pin computed in the generic loop (lines ~100-132) directly to
   `model_constraints.frame_constraints` as it is created, rather than only to `temp_solver`. This
   would incidentally close F4 for logos/exclusion/imposition as a side effect of making the
   property change land at all — but implementing that is a judgment call for the planning phase,
   not settled here; at minimum, the property change forces this call site to be visited and a
   decision made rather than silently left stale.
3. **Update the dead append sites** (`inject_z3_model_values` in `logos/exclusion/bimodal`'s
   `semantic/core.py`, reachable only via the unused `IteratorBuildExample.create_with_z3_model`
   factory — confirmed zero production callers by grep) to either match the new read-only
   property (append into the live component lists instead of `all_constraints`) or be left as-is
   if that dead path is deliberately not maintained; flag this decision explicitly in the plan
   rather than silently breaking `hasattr`/append-based unit tests that exercise this dead path
   (`models/tests/integration/test_constraints_injection.py`,
   `theory_lib/{logos,exclusion,bimodal,imposition}/tests/integration/test_injection.py`).
4. **Open a follow-up task for F4** (generic `is_world`/`verify`/`falsify` pinning in
   `iterate/models.py` never reaching the rebuilt structure's actual solve for logos/exclusion/
   imposition) — distinct root symptom from this task's `all_constraints` timing bug, same
   underlying "dead attribute treated as load-bearing" mechanism, worth its own reproduction and
   severity write-up rather than silently riding along with this task's fix.
5. **Verification for the eventual implementation**: run the CI gate's own two-invocation shape,
   not just the bimodal suite (per the dispatch's CONSTRAINTS):
   ```
   cd code
   PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread
   PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread
   ```
   (from `.github/workflows/tests.yml`), plus the bimodal suite explicitly (`PYTHONPATH=code/src
   pytest code/src/model_checker/theory_lib/bimodal/ -v`) since it carries the two-phase-specific
   regression coverage and, per `code/docs/core/TESTING_GUIDE.md` section 8.14, the earlier
   blanket `development`-marker exclusion for bimodal has been retired — bimodal now gates CI like
   any other theory, so it must not be treated as advisory-only when verifying this fix.

## Risks & Mitigations

- **Risk**: converting `all_constraints` to a property breaks any code that assigns to it (only
  `iterate/models.py:152` in production; several unit/integration tests too).
  **Mitigation**: Recommendation 2/3 above name every such site explicitly; none are silently
  missed by this audit.
- **Risk**: a future reader over-reads F4 as "this task's fix must also cover logos/exclusion/
  imposition pinning."
  **Mitigation**: Recommendation 4 states explicitly that F4 is a distinct defect proposed for a
  separate follow-up, mirroring the dispatch's own instruction (borrowed from A2_GAP.md's own
  precedent) to state severity precisely so a future reader does not over- or under-read it.
- **Risk**: `full_constraints()`'s test-tree callers regress if the production property and the
  test helper diverge silently.
  **Mitigation**: they are now provably identical in shape (F7); the planning phase should either
  have `full_constraints()` delegate to the new property directly, or leave it as-is with a
  docstring update noting the production attribute has caught up — either preserves existing
  green tests without narrowing any assertion (per the dispatch's constraint).

## Appendix

- Bimodal probe evidence (live `BM_CM_1`, `iterate: 3`): `all_constraints` lengths `[2, 78, 78]`
  vs. true four-list totals `[132, 208, 208]`; independent `recheck()` status `"countermodel"` for
  all three models.
- Logos probe evidence (live `N=2`, `[] |- ¬A`, `iterate: 3`, 2 models found before timeout):
  `all_constraints` lengths `[7, 23]` vs. true four-list totals `[7, 7]`; `is_world` signatures
  `(True, False, False, False)` and `(False, True, True, False)` (pairwise distinct, but not
  verified against the search's own difference-constraint witness).
- Every production (non-test) site touching `all_constraints`, by grep:
  `models/constraints.py:97` (definition), `iterate/models.py:93,152`, `iterate/constraints.py:
  51-52`, `models/structure.py:429,435`, `theory_lib/bimodal/semantic/model.py:344,349`,
  `theory_lib/{logos,exclusion,bimodal}/semantic/core.py` (`inject_z3_model_values`, dead path).
