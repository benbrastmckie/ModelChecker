# Research Report: Rotation-invariant bimodal isomorphism rejection

- **Task**: 190 - Rotation invariant bimodal isomorphism rejection
- **Started**: 2026-09-26T01:38:10Z
- **Completed**: 2026-09-26T01:45:10Z
- **Effort**: ~1.5 hours
- **Dependencies**: 189 (fix_shared_iterator_is_world_assumption) — status `completed`
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/iterate.py` (module docstring, all methods)
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` (`wrap`, slot layout)
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (`LabelledLasso`,
    `WitnessFamily`, `recheck`, window helpers)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`extract_certificate`)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` (current
    coverage, `TestLiveIteration`)
  - `code/src/model_checker/iterate/core.py` (three extension-point call sites and signatures)
  - `code/src/model_checker/iterate/graph.py` (`IsomorphismChecker.check_isomorphism`, the
    base-class pairing convention this task's override must mirror)
  - `code/src/model_checker/iterate/README.md` ("Extension Guide" table)
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
    (Phase 15's reasoned exclusions)
  - `specs/189_fix_shared_iterator_is_world_assumption/` report, plan, and summary
  - `specs/state.json` (task 189/190 status and dependency)
  - `~/Projects/BimodalLogic/FormalSystem/Semantics/ShiftSet.lean` (`total_eq_orbit`, the
    Lean-side semantic notion of history-orbit equivalence this task's rejection should track)
- **Artifacts**: `specs/190_rotation_invariant_bimodal_isomorphism_rejection/reports/01_rotation-invariant-isomorphism-rejection.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **The stated blocker no longer holds.** Task 190's description says it is "BLOCKED on the
  shared-iterator extension point task"; that task is task 189, which now has
  `"status": "completed"` in `specs/state.json`. `iterate.py`'s own module docstring and
  `tests/integration/test_iterate.py`'s `TestLiveIteration` class confirm the live
  `iterate_generator()` loop now genuinely calls `BimodalModelIterator`'s
  `_create_difference_constraint`/`_check_model_isomorphism`/`_create_non_isomorphic_constraint`
  overrides — there is something real to exercise this feature against. **Task 190 is
  unblocked**; the dependency should be treated as satisfied going into planning.
- **`_check_model_isomorphism` is the load-bearing hook, not `_create_non_isomorphic_constraint`
  alone.** `iterate.py:120-140` unconditionally returns `(False, None)`, so
  `_create_non_isomorphic_constraint` (`iterate.py:168-174`) is currently *unreachable* from the
  live loop for this theory — its own docstring says so explicitly ("moot for this theory in
  practice"). Richening `_create_non_isomorphic_constraint`'s definition alone, without also
  making `_check_model_isomorphism` actually detect rotation/permutation equivalence, would be a
  no-op change: the live loop would still never call it. The two hooks must be co-designed.
- **Detection and exclusion are naturally two different representations of the model.**
  Detection (comparing a new certificate against every previously-found one for
  rotation/permutation equivalence) is far more tractable at the *decoded* `WitnessFamily`/
  `LabelledLasso` level (`semantic/core.py`'s `extract_certificate`, already stored as
  `model_structure.certificate`) than at the raw Z3 boolean level. Exclusion (building the Z3
  blocking clause once a match is found) must operate on the raw `WitnessRegistry._bits`/
  `_guesses` Z3 variables, using `WitnessRegistry.wrap`'s slot layout to define the finite
  rotation group's action on variable keys.
- **The symmetry group is finite and, for the current example set, small.** For `L` total
  lassos (1 main + `k` witnesses) with back/fwd lengths `nb`/`nf`, the group is
  `(Z/nb x Z/nf)^L ⋊ S_k` (independent per-lasso back/fwd rotation, times permutation of the
  witness-lasso indices `1..k`, holding index `0` fixed) — at the repository's current defaults
  (`nb=nf=2`, `k<=2` per the Phase 16 reasoned-exclusions table) this is at most `4^3 x 2 = 128`
  elements, well within reach of a conjunctive Z3 clause.
- **One mathematical risk is open and should be closed (or explicitly scoped) before
  implementation, not assumed.** Whether a per-lasso back/fwd rotation is actually guaranteed to
  preserve local coherence (C1) and fulfilment (C2) — both of which reference the *absolute*
  structural boundaries `nb`/`nm`/`nf` (`_scan_forward_bound`/`_scan_backward_bound` in
  `certificate.py`), not a translation-invariant neighbourhood — is not proven anywhere in this
  repository or (as far as this research could determine without reading the full Lean
  development) shown to be a corollary of an existing Lean lemma. See Risks & Mitigations.
- **Recommended architecture**: implement detection in `_check_model_isomorphism` via a
  canonical-form comparison over decoded certificates (Python-level, cheap, and testable without
  Z3), and implement exclusion in `_create_non_isomorphic_constraint` via an explicit enumeration
  of the finite group acting on `WitnessRegistry`'s raw variables (Z3-level, using `wrap`'s slot
  ranges). This is a genuinely different design shape from the current exact-bit
  `_blocking_clause` reuse, not a small edit to it.

## Context & Scope

Task 190 asks `BimodalModelIterator._create_non_isomorphic_constraint`
(`code/src/model_checker/theory_lib/bimodal/iterate.py`) to reject models that are rotations of a
previously-seen lasso's periodic segments, or relabelings of its witness lassos, rather than only
exact bit-for-bit duplicates — closing a reasoned exclusion recorded in the certificate-redesign
plan's Phase 15 (`specs/184_.../plans/01_witness-family-certificate-redesign.md:995-1002`) and in
`iterate.py`'s own module docstring (lines 45-56). The task was recorded as `BLOCKED` on task 189
("the shared-iterator extension point task") because, until the live loop actually called
bimodal's own extension-point methods, there was nothing live to exercise a richer
`_create_non_isomorphic_constraint` against.

This report's scope is: (1) verify whether that blocker still holds; (2) characterize precisely
what "rotation of back/fwd segments" and "permutation of witness lassos" mean given the actual
`WitnessRegistry`/`LabelledLasso`/`WitnessFamily` data model; (3) identify where in the
`BaseModelIterator` extension-point architecture the fix belongs; (4) surface any mathematical
risk that a future implementation phase would need to resolve. Implementation itself is out of
scope for this report.

## Findings

### 1. The blocker is resolved

- `specs/state.json` records task 189 (`fix_shared_iterator_is_world_assumption`) as
  `"status": "completed"`, and task 190 lists `"dependencies": [189]`.
- `iterate.py`'s module docstring (lines 17-43) now states, in the present tense, that "the live
  loop now genuinely consults" `_pin_theory_specific_values`, `_build_exclusion_constraints`
  (which calls `_create_difference_constraint`), and `_check_model_isomorphism` — this is a
  rewrite from the historical framing task 190's description quotes ("nothing to exercise this
  against").
- `tests/integration/test_iterate.py`'s `TestLiveIteration` class (lines 294-377) already
  exercises a real, non-mocked `iterate: 3` run end-to-end, including a specific test
  (`test_exclusion_constraint_for_model_two_is_enforced_not_coincidental`) proving the exclusion
  constraint is genuinely enforced, not coincidental. This is the harness task 190 needs to
  extend, and it already exists and passes green (per task 189's summary: 7/7 phases completed,
  cross-theory regression gate green).
- **Conclusion**: task 190 should be treated as unblocked for planning purposes. The dependency
  on 189 is satisfied; no further upstream work is required before this task can proceed.

### 2. Why `_create_non_isomorphic_constraint` alone is not enough

`_check_model_isomorphism` (`iterate.py:120-140`) unconditionally returns `(False, None)` and its
own docstring states plainly that distinctness for this theory is enforced by
`_create_difference_constraint` instead, and that `_create_non_isomorphic_constraint` is "moot
for this theory in practice" because this override never reports an isomorphism. Tracing the live
loop (`iterate/core.py:331-356`) confirms this: `_create_non_isomorphic_constraint` is only ever
invoked (via `_build_stronger_constraint`, `iterate/core.py:818-850`) when
`_check_model_isomorphism` reports `is_isomorphic=True`. As written, that branch is dead code for
bimodal. A change that only rewrites `_create_non_isomorphic_constraint`'s clause-building logic,
without also changing `_check_model_isomorphism`'s unconditional `False`, would have **zero**
effect on any live `iterate: N` run — the richer clause would never be called, exactly as today.

The two hooks must therefore be designed together: `_check_model_isomorphism` needs to become the
actual detector (deciding *whether* a newly-built model is a rotation/permutation-duplicate of
some already-found model), and `_create_non_isomorphic_constraint` needs to become the actual
excluder (building the Z3 clause that keeps the solver from returning that duplicate, or its
whole orbit, again).

### 3. What "rotation" and "permutation" mean in this data model

- `WitnessRegistry.wrap(t)` (`witness_registry.py:124-131`) maps an absolute integer position `t`
  to one of `back + mid + fwd` slots, laid out contiguously as `[0, nb)` (back), `[nb, nb+nm)`
  (mid), `[nb+nm, nb+nm+nf)` (fwd) — this is the slot-index space the task description points to
  ("`WitnessRegistry.wrap`'s existing slot arithmetic").
- `LabelledLasso.label(t)` (`certificate.py:97-103`) decodes `back[t % nb]` for `t<0`, `mid[t]`
  for `0<=t<nm`, and `fwd[(t-nm) % nf]` for `t>=nm`. A *rotation by `r`* of the back segment
  (`new_back[i] := back[(i+r) % nb]`) or of the fwd segment (analogously) is exactly a relabeling
  of which tuple entry sits at which slot — the natural action of the cyclic group `Z/nb` (resp.
  `Z/nf`) on the slot range `[0, nb)` (resp. `[nb+nm, nb+nm+nf)`), independently per lasso.
- `WitnessFamily.lassos[0]` is always the main lasso, where `Target` (C4) is read at a specific
  `target_time` (`certificate.py:350-355`). `allocate_witness_lasso` (`witness_registry.py:155-168`)
  hands out indices `1..k` for witness lassos, one per boxed subformula whose guess is false,
  memoized by formula. The module's own "Witness lassos and sharing" section states witness
  lassos are anonymous carriers — a lasso index has no semantic meaning beyond "the content the
  solver put there" — which is exactly why permuting indices `1..k` (never index `0`, which is
  the semantically distinguished "main" lasso the target condition reads) is the right symmetry
  to quotient by. This matches the plan's own phrasing, "permutation of the witness lassos
  (lasso 0 fixed)."
- The Lean-side semantic grounding for treating two representations as "the same" is
  `ShiftSet.total_eq_orbit` (`~/Projects/BimodalLogic/FormalSystem/Semantics/ShiftSet.lean:252-257`):
  every world history equals the orbit through its own state-at-0, and `Box`'s range is exactly
  the set of orbits — i.e. what matters semantically is *which orbit* a lasso realizes, not the
  particular phase/index at which the solver happened to store it. This is the intuition task
  190's description is drawing on, even though the Lean development reasons about the paper's
  frames rather than about `LabelledLasso` directly.

### 4. Detection is a decoded-object problem, not a raw-Z3 problem

`semantic/core.py`'s `extract_certificate` (`core.py:340-...`) already decodes a satisfying Z3
model into a `WitnessFamily` of `LabelledLasso`s (label sets per position, not Z3 booleans), and
every built model structure stores this as `.certificate` (confirmed by
`_calculate_differences`'s existing use of `new_structure.certificate`/`previous_structure.certificate`,
`iterate.py:181-236`). Rotation/permutation-equivalence is naturally checked at this decoded
level: build a canonical form of a `WitnessFamily` (e.g. per lasso, the lexicographically-least
rotation of its `back` tuple and of its `fwd` tuple; then sort the witness lassos `1..k` by their
own canonicalized content, holding lasso `0` fixed) and compare canonical forms directly —
`LabelledLasso`/`WitnessFamily` are already `@dataclass(frozen=True)`, so structural `__eq__` on
tuples-of-frozensets is free once in canonical form. `_check_model_isomorphism(new_structure,
new_model)` is called before `new_structure`/`new_model` are appended to
`self.model_structures`/`self.found_models` (`iterate/core.py:722-752`, mirroring the base
`IsomorphismChecker.check_isomorphism`'s `zip(previous_structures, previous_models)` convention,
`iterate/graph.py:365-390`), so `zip(self.model_structures, self.found_models)` already gives the
exact index-aligned `(structure, z3_model)` pairs a bimodal override needs to scan.

### 5. Exclusion is necessarily a raw-Z3-variable problem

Whatever `_check_model_isomorphism` decides, `_create_non_isomorphic_constraint` must return a
`z3.BoolRef` built from `WitnessRegistry._bits`/`_guesses` (the same variable set
`_certificate_variables`/`_blocking_clause` already use, `iterate.py:81-153`), because that is
the only representation the live solver call
(`self.constraint_generator.check_satisfiability`) understands. The natural generalization of the
existing `_blocking_clause` helper is: instead of comparing each variable only to *its own* value
in `isomorphic_model`, compare it to the value `isomorphic_model` assigns to *the variable that
maps to it under group element `g`*, for every `g` in the finite symmetry group, and require the
new model to differ from `isomorphic_model`-under-every-`g` in at least one variable:

```
And over g in G:  Or over var:  var != value_in(isomorphic_model, g(var))
```

`g` acts on a `_bits` key `(lasso, slot, formula)` by (a) leaving `formula` and non-witness
lassos untouched, (b) remapping `slot` within its own segment range by the per-lasso back/fwd
rotation component of `g` (using exactly the `[0, nb)`/`[nb+nm, nb+nm+nf)` ranges `wrap` already
establishes — mid-segment slots, `[nb, nb+nm)`, are never rotated, since `mid` is read directly
by absolute position and has no periodic structure to rotate), and (c) remapping `lasso` by `g`'s
permutation component (identity on lasso `0`). `_guesses` keys are per-formula only (not
per-lasso), so no boxed-formula guess variable is ever touched by `g` — permuting/rotating
witness-lasso *content* does not change which formulas are guessed true or false, only where
their supporting label content lives.

This is a genuinely different implementation from richening `_blocking_clause` in place — it
needs the group enumeration to live somewhere (a new helper, not a one-line change), and it needs
`WitnessRegistry`'s segment boundaries (`nb`, `nm`, `nf`, and the count of allocated witness
lassos) to be available to `iterate.py`, which they already are via
`semantics.witness_registry.nb/nm/nf` and `len(semantics.witness_registry._witness_lassos)`.

## Decisions

- **Task 190's `BLOCKED` status should be lifted going into planning.** Task 189 is complete and
  the live loop demonstrably consults bimodal's iterator hooks; there is no remaining blocker.
- **The fix spans two hooks, not one.** A plan for this task must budget for changes to both
  `_check_model_isomorphism` (detector) and `_create_non_isomorphic_constraint` (excluder),
  co-designed, rather than treating the task as a single-method edit.
- **Detection should be implemented against decoded `WitnessFamily`/`LabelledLasso` objects**
  (via `model_structure.certificate`), not against raw Z3 variables — this is both the more
  natural representation and the one that is unit-testable without a live Z3 solve (a canonical-
  form function can be tested directly against hand-built `LabelledLasso`/`WitnessFamily`
  fixtures, as `TestCalculateDifferences` already does for a related concern).
- **Exclusion should be implemented against `WitnessRegistry`'s raw `_bits`/`_guesses`**, using
  `wrap`'s per-segment slot ranges to define the group action on variable keys, mirroring (and
  generalizing) the existing `_blocking_clause` helper rather than replacing its overall shape.

## Recommendations

1. **Plan phase should scope two sub-features explicitly**: (a) a canonical-form / orbit-membership
   detector over `WitnessFamily`, exposed as a small, independently unit-testable function (e.g.
   `_certificate_orbit_key` or similar, living in `iterate.py` or a new helper module); (b) a
   group-action exclusion-clause builder over `WitnessRegistry`'s Z3 variables, parameterized by
   the same group the detector uses, so the two cannot drift apart (mirroring how
   `witness_constraints.py` and `certificate.py` already share exactly one definition of the
   fulfilment window per the certificate.py module docstring's own stated design principle).
2. **Resolve the open mathematical question (Finding above, "Risks") before or during
   implementation, not after**: confirm, by direct argument or by testing against the wide
   `_coherence_window`, whether a per-lasso back/fwd rotation by any amount in `Z/nb`/`Z/nf`
   provably preserves local coherence (C1) and fulfilment (C2) given their absolute-boundary-
   anchored scan bounds (`_scan_forward_bound`/`_scan_backward_bound`), or whether only rotations
   by multiples of a segment's own minimal period are safe. If the general claim cannot be
   established cheaply, the safer fallback (see Risks) is to verify each candidate transform
   against `certificate.py`'s pure-Python `recheck()` before treating it as a rejection target,
   rather than asserting a blanket rotation-invariance the constraint layer cannot itself verify.
3. **Extend `tests/integration/test_iterate.py` with three new test classes**, matching the
   existing module's structure: (a) a `TestCertificateOrbitDetection` class exercising the
   canonical-form/orbit function directly on hand-built `LabelledLasso`/`WitnessFamily` fixtures
   (rotated-but-equivalent, permuted-but-equivalent, and genuinely-different cases — no Z3
   involved, fast); (b) an extension of `TestCheckModelIsomorphism` covering the new detection
   behavior (was: always `(False, None)`; now: `True` against a synthetically rotated/permuted
   duplicate, `False` against a genuinely different model); (c) an extension of
   `TestLiveIteration` with a live `iterate: N` case constructed (or found empirically) to
   surface an actual rotation/permutation duplicate, verifying it is *not* double-counted in the
   yielded model count — this is the test that gives the feature real teeth, per the plan's own
   original task list wording ("a model that is a rotation of a previous one's periodic segments
   is rejected").
4. **Do not conflate this task with `_create_difference_constraint`.** The task description and
   the Phase 15 reasoned exclusion both scope this specifically to
   `_create_non_isomorphic_constraint`/`_check_model_isomorphism`; `_create_difference_constraint`
   already correctly rejects exact duplicates on the live path (task 189) and needs no change
   here.

## Risks & Mitigations

- **Risk**: The rotation-invariance claim (a per-lasso back/fwd rotation always preserves local
  coherence and fulfilment) may not actually hold in general, because `_scan_forward_bound`/
  `_scan_backward_bound` (`certificate.py:221-228`) anchor to the absolute constants `nm`/`nb`/
  `nf`, not to a translation-invariant neighbourhood of `t`. If false in general, a
  `_check_model_isomorphism` override that asserts rotation-equivalence unconditionally could
  either (a) falsely equate two models that are not actually interchangeable (harmless for
  soundness of "not missing real models," since the affected pair would already both be valid
  certificates that happen to look alike, but could hide a genuinely distinct countermodel from
  the user), or (b) build an exclusion clause the solver then finds unsatisfiable against a valid
  future candidate it should not have excluded.
  **Mitigation**: before treating a transform as a rejection target, verify it independently via
  `certificate.py`'s `recheck()` (already exists, already covers exactly the four certificate
  conditions) against the *transformed* `WitnessFamily`, rather than assuming the transform is
  automatically valid. This adds a re-check cost per detection but is strictly safer, and keeps
  the exclusion clause honest without requiring a new Lean-style proof before implementation can
  start.
- **Risk**: Group size growth. `(Z/nb x Z/nf)^L x k!` grows quickly if a future example needs
  larger back/fwd segments or more witness lassos (the `max_witnesses` reasoned exclusion in
  Phase 16 already flags this as a live possibility). At the current defaults this is a
  non-issue (<=128 elements), but a plan should note the growth formula so a future example with,
  say, `nb=nf=4` and 3 witnesses does not silently blow up clause size (`8^4 x 6 = 24576`
  elements) without anyone having budgeted for it.
  **Mitigation**: gate the full group enumeration behind a size check with a documented fallback
  (e.g. cap to identity + single-lasso rotations + adjacent-pair transpositions if the full group
  would exceed some threshold), analogous to how `max_witnesses` already trades completeness for
  bounded search elsewhere in this module.
- **Risk**: `_check_model_isomorphism`'s current unconditional `(False, None)` has a documented
  rationale (avoiding the shared `ModelGraph`'s false-positive-on-empty-graphs bug). A rewrite
  must preserve that reasoning for the *general* case (this theory truly cannot use `ModelGraph`)
  while adding the *new*, theory-specific detection — i.e. the override should remain a complete
  opt-out of the generic graph path, just no longer a complete opt-out of isomorphism detection
  altogether. This distinction should be stated explicitly in the rewritten docstring so a future
  reader does not mistake the new behavior for a re-adoption of `ModelGraph`.

## Appendix

- `iterate.py`'s Phase-15-era module docstring (lines 45-56) is the primary internal record of
  this exclusion and already names `WitnessRegistry.wrap`'s slot arithmetic as the intended tool
  — this report's Finding 5 is a concretization of that pointer, not a new direction.
- `code/src/model_checker/iterate/README.md`'s "Extension Guide" table (`README.md:283-306`) is
  the authoritative statement of each hook's call site, base-class default, and override
  condition; any plan for this task should cite it directly rather than re-deriving the hook
  contract from `iterate/core.py` each time.
- Task 189's summary (`specs/189_fix_shared_iterator_is_world_assumption/summaries/01_iterator-theory-extension-points-summary.md`)
  records the cross-theory regression gate this task must not regress (logos, imposition,
  exclusion all still satisfy the `is_world`-gated generic path).
