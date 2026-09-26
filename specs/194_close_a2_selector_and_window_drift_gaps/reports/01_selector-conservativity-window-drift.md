# Research Report: Close the A2 selector and window-drift gaps
- **Task**: 194 - Close the two residual encoder-versus-specification gaps in the A2
  encoding-completeness argument
- **Started**: 2026-09-26T16:20:00Z
- **Completed**: 2026-09-26T16:35:00Z
- **Effort**: ~1 hour (research only)
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 5.2, 5.3, 7.3)
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`extract_certificate`,
    `DEFAULT_EXAMPLE_SETTINGS`)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py`
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`
  - `specs/archive/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
    (decisions D5, D7)
- **Artifacts**: `specs/194_close_a2_selector_and_window_drift_gaps/reports/01_selector-conservativity-window-drift.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The one-hot selector (`WitnessConstraintGenerator.sel`/`target_constraints`,
  `witness_constraints.py:137-163`) is provably conservative: it is a faithful, lossless
  Skolemization of (C4) Target's existential `t`, not an extra constraint the encoder imposes
  beyond (C1)-(C4). The argument is short and purely algebraic (periodicity of `LabelledLasso.label`
  plus the fact `sel`'s window is exactly one representative position per slot); it belongs in
  ADEQUACY.md section 7.3 as recorded reasoning, not just tribal knowledge.
- No existing test isolates the selector mechanism from (C1)-(C3). `test_witness_constraints.py`'s
  `TestTargetConstraints` exercises `target_constraints` in isolation but only spot-checks
  individual clauses (exactly-one, one premise, one conclusion), never the full equivalence "SAT
  with `sel[t]` true for some `t` <=> the corresponding family satisfies (C4) at target time `t`"
  against `certificate._target_holds`/`recheck` directly. `test_certificate_a2_triangle.py`
  exercises the whole encoding (C1)-(C4) together and only at the aggregate level (`accepted > 0`
  == Z3 SAT), so it cannot by itself localize a future defect to the selector versus the other
  three conditions.
- Window drift is real but currently latent, not manifest: `WitnessRegistry.target_window()`
  (`witness_registry.py:170-173`) and `certificate._box_window()` (`certificate.py:216-218`)
  compute the textually identical formula `range(-nb, nm+nf)` over the same `nb`/`nm`/`nf`
  attributes, but as two independent source-of-truth definitions with no test or import tying
  them together. `target_window()` is load-bearing well beyond the selector: `extract_certificate`
  (`core.py:340-376`) also uses it, in slot order, to reconstruct label segments from the raw Z3
  model, and `test_certificate_a2_triangle.py`'s `_candidates()` uses it to size the target-time
  enumeration. A silent edit to one formula without the other would desynchronize box faithfulness,
  certificate extraction, and the A2-triangle test all at once, with no failure until a specific
  edge case is hit.
- Recommendation: share a single definition (delegate `target_window()` to `_box_window`) rather
  than merely asserting agreement, since the two are already provably the same window in fact, not
  just in shape, and the codebase already establishes this exact "encoder imports the re-checker's
  window helper" pattern for `_coherence_window`/`_scan_forward_bound`/`_scan_backward_bound`
  (`witness_constraints.py:72`). A property-style agreement test across a swept `(nb, nm, nf)` range
  is a reasonable belt-and-suspenders addition but should not replace the delegation.
- No behavioral change is implied by either recommendation: `_box_window(registry)` and
  `registry.target_window()` already return `range` objects with identical bounds for every valid
  `(nb, nm, nf)` triple, so delegating one to the other is a refactor, not a behavior change.

## Context & Scope

`docs/ADEQUACY.md` section 7.3 states that A2 (encoding completeness) holds iff "the Z3 constraint
set is exactly the conjunction of (C1)-(C4) ... with no extra constraint," and names
`test_certificate_a2_triangle.py` as the deciding test. Decision D5
(`specs/archive/184.../plans/01_witness-family-certificate-redesign.md:101-106`) records that
`Target` (C4) is *existential* in `t`, and that the encoder represents this existential with a
one-hot Boolean selector `sel[t]` over a finite window plus guarded implications — structure that
does not appear anywhere in (C1)-(C4)'s own statement (`certificate.py`'s `_target_holds`, which
takes `target_time` as a plain parameter, not a selector). This task's first half asks: is that
extra structure conservative (adds no soundness/completeness risk of its own), and is that fact
established and directly tested, so a future A2-triangle disagreement cannot be wrongly attributed
to the selector.

The second half concerns `WitnessRegistry.target_window()`, which `certificate.py`'s own module
comment (`certificate.py:198-207`) flags as "the one place encoder and re-checker can silently
diverge on a window" — independently defined rather than imported from `certificate.py`, unlike
the three other window/bound helpers the encoder does import
(`_coherence_window`/`_scan_forward_bound`/`_scan_backward_bound`, `witness_constraints.py:72`).

## Findings

### F1 — The selector's conservativity is a provable, short algebraic fact

Three properties of the existing code jointly establish conservativity:

1. **The window is exactly one representative position per slot, in slot order.**
   `WitnessRegistry.target_window()` returns `range(-nb, nm+nf)`, which has exactly
   `nb + nm + nf == slots_per_lasso` elements (`witness_registry.py:119-122, 170-173`), and
   `WitnessRegistry.wrap` (`witness_registry.py:124-131`) is a bijection from this window onto
   `[0, slots_per_lasso)` — confirmed already by
   `test_witness_registry.py::TestTargetWindow.test_target_window_hits_every_slot_exactly_once`.
2. **`sel[t]`'s guarded implications, restricted to the main lasso, read exactly the same Z3
   terms `certificate._target_holds` reads.** `target_constraints` writes
   `Implies(sel[t], registry.bit(0, t, p))` for each premise and
   `Implies(sel[t], Not(registry.bit(0, t, c)))` for each conclusion
   (`witness_constraints.py:157-162`). `extract_certificate` reconstructs
   `family.main.label(t)` for each window `t` from exactly these same bits
   (`core.py:363-376`), so — for a fixed valuation of the label bits — `sel[t]` being forced true
   and satisfiable is equivalent to `_target_holds(family, premises, conclusions, t)`
   (`certificate.py:350-355`) being true of the corresponding extracted family. This is not an
   analogy; it is definitionally the same predicate over the same Z3 terms.
3. **Periodicity means the window loses no target time.** `LabelledLasso.label(t)`
   (`certificate.py:97-103`) is exactly periodic: any integer `t` and its window representative
   `t'` sharing a slot (`wrap(t) == wrap(t')`) index the identical label. So
   `_target_holds(family, ..., t) == _target_holds(family, ..., t')` for every `t`, not just those
   inside the window — restricting `sel`'s domain to one representative per slot cannot discard a
   satisfying target time that exists outside the window; it can only discard a *duplicate*
   representation of one already inside it. This is exactly what D5's own remark half-states
   ("Fixing `t0 = 0` would be sound but would lose certificates that exist ... with the target
   elsewhere") without spelling out that a full-period window is not just "wide enough" but
   *exactly* lossless — one slot, one representative, no more and no fewer.

Together: **the encoding is SAT with some `sel[t]` true exactly when a certificate satisfying
(C1)-(C4) exists with target time `t`** (for `t` ranging over all of `Z`, via periodicity reducing
to the window). The selector is a Skolemization of C4's existential quantifier, not additional
structure beyond it — so a future A2-triangle disagreement cannot be caused by the selector
mechanism itself, only by (C1)-(C3)'s own constraint families or a bug in how bits are wired
(which items 2-3 above already rule out for the target/selector wiring specifically).

This argument is currently nowhere written down: `witness_constraints.py`'s module docstring
documents *why the wide window is needed for local coherence* (lines 24-56) at length, but
`target_constraints`/`sel`'s own docstrings (lines 137-163) do not carry the corresponding argument
for C4, and ADEQUACY.md section 7.3 does not mention the selector at all.

### F2 — No test isolates the selector from (C1)-(C3)

- `test_witness_constraints.py::TestTargetConstraints` (lines 109-179) tests `target_constraints`
  in isolation from (C1)-(C3) (good), but only spot-checks: exactly-one is satisfiable, two
  selectors true is UNSAT, no selector true is UNSAT, a selected position must carry every premise/
  must not carry any conclusion, and an unselected position is unconstrained. None of these tests
  cross-check against `certificate._target_holds`/`recheck` directly, and none sweep multiple label
  assignments or multiple `t` — each test hand-picks one scenario and hand-derives the expected
  SAT/UNSAT verdict rather than deriving it from the re-checker.
- `test_certificate_a2_triangle.py` is the only test that ties the *whole* encoder (all of
  (C1)-(C4) together) to the whole re-checker, and only at the aggregate level: `accepted > 0`
  (leg i, any candidate accepted at any `t` in `target_window()`) must equal Z3's SAT/UNSAT verdict
  (leg iii). This is the right test for A2 as a whole but, by construction, cannot localize a
  disagreement to the selector versus (C1)-(C3) — exactly the gap this task names.
- No test exists that fixes label bits directly (bypassing (C1)-(C3) entirely, as
  `TestTargetConstraints` already does) across *multiple* label patterns and *multiple* target
  times and asserts the Z3-side verdict against `certificate._target_holds` computed on the same
  labels, which is what F1's equivalence claim needs a direct regression for.

### F3 — Window drift is real (two independent definitions, textually identical today) but currently non-manifest

- `certificate._box_window(lasso)` (`certificate.py:216-218`): `range(-lasso.nb, lasso.nm + lasso.nf)`.
- `WitnessRegistry.target_window(self)` (`witness_registry.py:170-173`): `range(-self.nb, self.nm + self.nf)`.

These are the same formula over the same three attributes (`WitnessRegistry` duck-types
`nb`/`nm`/`nf` identically to `LabelledLasso`, per `witness_constraints.py`'s own module comment,
lines 198-207), so no test failure exists today. But:

- `witness_constraints.py::box_faithfulness_constraints` uses `_box_window(registry)` directly
  (imported from `certificate.py`, line 227), while `target_constraints` uses
  `self.registry.target_window()` (line 152) — two call sites computing the same window through
  two different code paths for two different constraint families in the *same class*.
- `core.py::extract_certificate` (lines 340-376) additionally depends on `target_window()`
  returning results in exactly slot order (`back`-then-`mid`-then-`fwd`) with exactly
  `slots_per_lasso` elements, since it slices the resulting label list with
  `labels[:registry.nb]` / `labels[registry.nb:registry.nb+registry.nm]` /
  `labels[registry.nb+registry.nm:]` (lines 373-375). Any future edit to `target_window()` alone
  (e.g. to special-case `mid == 0`, or to change the tie-break at the `mid`/`fwd` boundary) would
  silently break certificate extraction and, separately, silently desynchronize box faithfulness's
  soundness (which cites the Lean-proved `mem_all_iff_window`, ADEQUACY.md section 5.2) from
  whatever `target_window()` had drifted to — two failure modes from one edit, in two unrelated
  subsystems, with no test today that would catch the divergence directly (only indirectly, and
  only if the drift happened to change the aggregate SAT/UNSAT verdict of some example in
  `test_certificate_a2_triangle.py` or the four-theory gate).
- `certificate.py`'s own module comment (lines 198-207) already documents this as a deliberate but
  acknowledged risk: the split was chosen because `target_window` is "also reused for the unrelated
  one-hot target selector" and "the two are simple, identical one-line formulas" — a judgment call
  about risk being low, not a technical obstacle to sharing.

## Decisions

- **Selector conservativity is a documentation-plus-test gap, not an open question.** The proof
  is already implicit in the existing code (F1); no new encoder logic is needed, only (a) a written
  record of the argument (ADEQUACY.md section 7.3, plus docstrings on `sel`/`target_constraints`/
  `target_window`) and (b) a direct test.
- **Window drift should be closed by sharing a single definition, not merely asserting agreement.**
  The two formulas are not merely "expected to agree by coincidence" — they are the same
  mathematical object (`_box_window` is exactly `mem_all_iff_window`'s proved bound, ADEQUACY.md
  section 5.2, and `target_window` is that same bound reused for the selector and for extraction,
  per `certificate.py`'s own comment). The codebase already has the matching precedent: encoder-side
  `_coherence_window`/`_scan_forward_bound`/`_scan_backward_bound` are imported directly from
  `certificate.py` rather than redefined (`witness_constraints.py:72`), specifically so "the encoder
  and the re-checker share exactly one definition ... and cannot drift apart" (comment at
  `certificate.py:203`). `target_window` should join that list: have
  `WitnessRegistry.target_window()` delegate to `_box_window(self)` (importing it from
  `.certificate`, no import cycle — `certificate.py` does not import `witness_registry.py`). This
  is a pure refactor (`_box_window(registry)` and `registry.target_window()` already return
  identical `range` objects for every valid `(nb, nm, nf)`), so no behavioral change results, and
  every call site (`box_faithfulness_constraints`, `target_constraints`, `extract_certificate`,
  `test_certificate_a2_triangle.py`'s `_candidates`) continues to compile and pass unchanged.
- **A swept-range agreement test is a reasonable addition alongside the delegation, not instead of
  it.** Once `target_window()` delegates to `_box_window`, the two can never drift again by
  construction, which is strictly stronger than a test that merely asserts they currently agree
  over a finite sample. A regression test is still worth adding to guard the delegation itself
  (i.e., to fail loudly if a future edit reintroduces an independent `target_window` body) — but it
  should not be the *only* fix, since an assert-agreement test only catches drift after the fact,
  over whatever finite range it happens to sweep, exactly the "the two windows must not be treated
  as the same" caution ADEQUACY.md section 5.2 already gives for a structurally analogous pair
  (the wide coherence window versus the narrow box window).

## Recommendations

1. **Record the selector-conservativity argument (F1) in three places:**
   - `docs/ADEQUACY.md` section 7.3: add a short paragraph noting that the one-hot selector `sel[t]`
     is a lossless Skolemization of (C4)'s existential `t` — conservative by periodicity plus
     the window's one-representative-per-slot property — so it is not a source of encoding
     incompleteness/unsoundness distinct from (C1)-(C3).
   - `witness_constraints.py`'s `sel`/`target_constraints` docstrings (lines 137-163): reference
     this argument the way the module docstring already does for local coherence's wide window
     (lines 24-56).
   - `witness_registry.py`'s `target_window` docstring (lines 170-173): note it is now the shared
     definition also used for box faithfulness, not an independent one.
2. **Add a direct selector-conservativity test**, isolated from (C1)-(C3) the way
   `TestTargetConstraints` already is, but strengthened to assert the *equivalence* against
   `certificate._target_holds`/`recheck` rather than a hand-derived expectation:
   - Build a `WitnessRegistry` + `WitnessConstraintGenerator` with only `target_constraints`
     asserted (no local coherence/fulfilment/box faithfulness).
   - Parametrize (or loop) over several small, explicit label assignments for the main lasso
     (fixing `registry.bit(0, t, formula)` for every closure formula and every `t` in
     `target_window()`, mirroring how a `LabelledLasso`'s back/mid/fwd tuples would read) and over
     both premise-present/absent and conclusion-present/absent combinations.
   - For each assignment, compute the *expected* set of satisfying `t` via
     `certificate._target_holds` (or `recheck`'s C4 sub-check) on the corresponding hand-built
     `WitnessFamily`, and assert the Z3 solver's outcome agrees: SAT iff that set is non-empty, and
     when SAT, every model has `sel[t]` true only for `t` in that expected set.
   - Additionally test the periodicity corollary directly: pick a `t` outside `target_window()`
     and its in-window representative `t'` (same `wrap` value), and assert
     `_target_holds(family, ..., t) == _target_holds(family, ..., t')` for a hand-built family —
     a cheap, direct regression for F1 item 3 that needs no Z3 solve at all.
3. **Close the window-drift gap by delegation**: change `WitnessRegistry.target_window()`
   (`witness_registry.py:170-173`) to `return _box_window(self)`, importing `_box_window` from
   `.certificate`. Update the two module comments (`certificate.py:198-207`,
   `witness_registry.py`'s own header docstring) to state the encoder now shares this window
   definition for both box faithfulness and the selector/extraction, removing the
   "independently defined" language that is no longer accurate.
4. **Add a lightweight swept-range regression** (e.g. `nb`, `nm` in `1..3`, `fwd` in `1..3`,
   including `mid == 0`) asserting `WitnessRegistry(back, mid, fwd, closure=[]).target_window() ==
   range(-back, mid + fwd)` — cheap insurance against a future accidental re-divergence of the
   delegation, matching the "assert the two formulas agree" alternative the task names, but as a
   supplement to recommendation 3, not a replacement for it.
5. **Verification**: after 3-4, run the full bimodal suite
   (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v`, including the
   `slow`-marked `test_certificate_a2_triangle.py` cases) and the four-theory gate
   (`PYTHONPATH=code/src pytest code/tests/ -v`, or whatever command the four-theory gate
   documentation names) to confirm no behavioral change, per the task description's explicit
   "no behavioral change is intended."

## Risks & Mitigations

- **Risk**: delegating `target_window()` to `_box_window` could be read as conflating two
  "unrelated" concepts (box faithfulness's proved bound vs. the selector's Skolemization window)
  that happen to share a formula only by coincidence, inviting a future edit to one without
  noticing the other use. **Mitigation**: the updated docstrings (recommendation 1, 3) should say
  explicitly that the *reason* they must stay identical is F1's window-completeness argument for
  the selector and ADEQUACY.md section 5.2's proved bound for box faithfulness — both require
  exactly `[-nb, nm+nf)`, so sharing the definition is the technically correct outcome, not a
  cosmetic convenience.
- **Risk**: the new selector-isolation test (recommendation 2) could become another "hand-derived
  expectation" test if the expected-satisfying-`t` set is computed by re-implementing C4's logic
  inline rather than calling `certificate._target_holds`/`recheck`. **Mitigation**: recommendation 2
  is written to call the re-checker function directly, not re-derive it — this should be enforced
  at review/implementation time, not left to a docstring's aspiration.
- **Risk**: none of the four items above changes behavior, but the swept-range test
  (recommendation 4) could become flaky or overly slow if the range is too large. **Mitigation**:
  keep the sweep to the same order of magnitude as `DEFAULT_EXAMPLE_SETTINGS`'s defaults
  (`back=2, mid=1, fwd=2`, `core.py:108-125`) — small integers, not a stress test.

## Appendix

- `_target_holds` (C4): `certificate.py:350-355`.
- `_box_window` (box faithfulness's proved window): `certificate.py:216-218`.
- `WitnessRegistry.target_window`: `witness_registry.py:170-173`.
- `WitnessConstraintGenerator.sel`/`target_constraints`: `witness_constraints.py:137-163`.
- `extract_certificate`'s use of `target_window()` for label reconstruction: `core.py:340-376`.
- Existing selector unit tests: `test_witness_constraints.py:109-179`
  (`TestTargetConstraints`).
- Existing window-hits-every-slot test: `test_witness_registry.py`
  (`TestTargetWindow.test_target_window_hits_every_slot_exactly_once`).
- A2-triangle aggregate test: `test_certificate_a2_triangle.py` (whole module).
- ADEQUACY.md section 7.3 (A2's statement and named deciding test) and section 5.2 (the four
  window-collapse results, including box faithfulness's proved `[-nb, nm+nf)`).
- Decision D5 (one-hot selector) and D7 (window bounds):
  `specs/archive/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md:101-134`.
