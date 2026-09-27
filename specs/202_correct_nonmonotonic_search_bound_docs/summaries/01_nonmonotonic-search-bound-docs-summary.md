# Implementation Summary: Task #202

- **Task**: 202 - correct_nonmonotonic_search_bound_docs
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T01:30:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None (task 201, disjoint scope, already committed)
- **Artifacts**: plans/01_nonmonotonic-search-bound-docs.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Corrected the false claim, duplicated across the bimodal theory's documentation and code
comments, that `back`/`mid`/`fwd` are all "maximum segment lengths" and that raising any of the
three monotonically enlarges the search. `WitnessRegistry.wrap()` folds `back` and `fwd`
positions by **exact period** (`t % back`, `(t - mid) % fwd`), so a lasso family with back-period
`p` is representable at configured `back = n` iff `p` divides `n` — raising `back`/`fwd` can
therefore discard a family a smaller value represented. `mid` is unaffected: it is read directly
with no modulo and genuinely is a maximum. Every carrier site now states the exact-period
mechanism, the divisibility consequence, and the operative rule (choose `back`/`fwd` as a
multiple of the period of interest; `mid` may be raised freely), all cited back to
`docs/SETTINGS.md` as the single canonical explanation. This was documentation and code-comment
work only — no search semantics changed.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` — rewrote the `back`/`fwd`/`mid`
  bullets, the `back + mid + fwd` paragraph (now states the divisibility condition and the
  measured SAT/UNSAT-by-divisibility example), Tips #2, and added a caveat under the
  "longer periodic segment" illustration. This is the canonical wording every other site cites.
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` — rewrote the D4 docstring
  paragraph (exact-period framing plus the divisibility consequence and a pointer to
  `docs/SETTINGS.md`) and the `DEFAULT_EXAMPLE_SETTINGS` inline comment. Comment/docstring-only;
  `DEFAULT_EXAMPLE_SETTINGS` values (`back=2, mid=1, fwd=2`) unchanged, module still imports.
- `code/src/model_checker/theory_lib/bimodal/README.md` — corrected three spots: the Key Classes
  settings summary, the duplicated `DEFAULT_EXAMPLE_SETTINGS` comment (kept byte-identical to
  `core.py`'s), and the `back`/`mid`/`fwd` explanatory paragraph.
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` — corrected the settings-list
  bullet, the three inline example comments, and the Bimodal-Specific Considerations bullet
  named in the plan, plus two additional instances of the same false claim (Performance tips and
  Troubleshooting) surfaced by this phase's own scope-hypothesis grep.
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` — corrected the Key
  Attributes line and Debugging Tips #3.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — corrected the three coordinated
  spots: the `(ADEQ)` lede (now a representability condition, not a bare `≥ f(|C|)`), the A3 table
  row, and 7.1 condition (iii), which now names the two available (unimplemented) routes to a
  genuine sufficient condition — an `lcm`-based common-multiple bound (correct but
  `e^{O(f)}`-sized, impractical) or an `f^3`-call grid sweep — plus the mechanism/evidence
  sentence. A0/A1/A2 status and `A2_GAP.md` untouched.
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` — **not in the original plan's
  six-file scope**; Phase 6's own re-sweep found this file restates the false claim at two spots
  (Performance Tips #1, Troubleshooting). Corrected both, per the plan's Scope Hypothesis
  instruction to fix any additional carrier the gate discovers.

## Decisions

- Kept the plan's canonical-wording-once, cite-elsewhere structure: `SETTINGS.md` is the single
  authoritative explanation; every other site states the claim at the length that site allows and
  links back rather than re-deriving the mechanism.
- Preserved the `mid` carve-out throughout: no corrected sentence ever groups `mid` with
  `back`/`fwd` when stating non-monotonicity; every corrected site says "`back` and `fwd`," never
  "all three."
- In `ADEQUACY.md`, restated `(ADEQ)`/A3/7.1(iii) as a **representability** condition (common
  multiples of periods) rather than trying to patch the bare `≥ f(|C|)` magnitude condition —
  sufficiency here really is a divisibility fact, and softening it to "raise the multiplier" would
  have been a second false claim.

## Plan Deviations

- **Phase 6 task 6.1** (re-run sweep grep): the plan's Scope Hypothesis asserted exactly six
  carrier files. The sweep surfaced a seventh, `docs/ITERATE.md` (two spots), which the original
  research report's sweep had missed. Corrected in-scope in Phase 6 per the plan's own
  contingency instruction rather than deferred; recorded here and in the phase's Testing &
  Validation checklist annotation.
- **Phase 4 task 4.6** (SETTINGS.md pointers): the plan asserted five carrier spots across
  `USER_GUIDE.md`/`API_REFERENCE.md`. The phase's own scope-hypothesis grep surfaced two
  additional instances in `USER_GUIDE.md` (Performance tips, Troubleshooting), both corrected
  in-scope.

## Verification

- Build: N/A (documentation and comments only)
- Tests: Passed — `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`:
  508 passed both before (149.31s) and after (140.33s) the change set; identical pass count.
- Files verified: Yes — all seven touched files read through end-to-end; `git diff` for each
  confirmed comment/prose-only hunks (no executable Python line, no settings value changed);
  `DEFAULT_EXAMPLE_SETTINGS` module import still succeeds and reads `back=2, mid=1, fwd=2`;
  `README.md`'s and `core.py`'s duplicated settings comment blocks are byte-identical.

## Impacts

- Users configuring `back`/`fwd` now see the correct exact-period mechanism and the operative
  rule (choose a multiple of the period of interest) at every site they might encounter it,
  instead of being told that raising a bound is always at least as good as a smaller one.
- No behavior change: the search semantics (exact-period folding in `WitnessRegistry.wrap()`) are
  unchanged; only the documentation and code comments describing that pre-existing behavior were
  corrected.

## Follow-ups

- A standing regression test for the measured SAT/UNSAT-by-divisibility case (SAT at
  `(3,1,3)`/`(6,1,6)`, genuinely UNSAT at `(4,1,4)`/`(5,1,5)`) was named as a forward pointer only,
  per the plan's Non-Goals — not added here.
- A `context/project/math/` periodicity note, recommended by the research report, was named as a
  forward pointer only, per the plan's Non-Goals — not created here.
- Whether to change the search semantics itself (e.g. sweep or `lcm`-based `back`/`fwd` selection)
  is explicitly out of scope, per both the task description and `ADEQUACY.md`'s now-honest 7.1(iii)
  — deferred to a separate task.

## Addendum: Phase 7 — eighth carrier (`examples.py`)

A follow-up round (forced re-dispatch on this already-completed task) found a further carrier
missed by both the original research sweep and Phase 6's own gate:
`code/src/model_checker/theory_lib/bimodal/examples.py`'s module docstring "Settings Options"
block (lines 68 and 70), which is the module users read and copy from first.

- `code/src/model_checker/theory_lib/bimodal/examples.py` — rewrote the `back` and `fwd` bullets
  from "Maximum length of a witness-family lasso's repeating back/forward segment" to the
  exact-period wording matching `docs/SETTINGS.md`'s canonical bullets ("exact cyclic period ...
  not an upper bound on it"). The `mid` bullet (line 69) was left untouched — `mid` is read
  directly and genuinely is a maximum.
- Re-ran the Phase 6 cross-file gate grep
  (`grep -rn "maximum length\|maximum segment\|max segment\|enlarge\|raising\|raise"
  code/src/model_checker/theory_lib/bimodal/ --include="*.py" --include="*.md"`) extended to
  cover `examples.py`. The only remaining "maximum length of a witness-family lasso" hit anywhere
  under the theory is the correct `mid` bullet; no other `.py` module in the theory exposes a
  "Settings Options" docstring block at all, so the eighth-carrier fix closes the sweep.
- Verified `python3 -c "import ast; ast.parse(...)"` on `examples.py` succeeds (docstring-only
  change; no executable line or default value touched).
- Re-ran the bimodal test suite: `PYTHONPATH=code/src pytest
  code/src/model_checker/theory_lib/bimodal/tests/ -q` — 508 passed in 179.49s, matching the
  Phase 6 baseline pass count (no regression).
- Recorded as Phase 7 in the plan (`[COMPLETED]`), depending on Phase 6.

This is documentation/comment-only, identical in kind to the original six-file (then
seven-file) sweep; no search semantics changed.

## References

- `specs/202_correct_nonmonotonic_search_bound_docs/plans/01_nonmonotonic-search-bound-docs.md`
- `specs/202_correct_nonmonotonic_search_bound_docs/reports/01_nonmonotonic-search-bound-fixes.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` (the `wrap()` mechanism
  every corrected site now describes)
- `code/src/model_checker/theory_lib/bimodal/examples.py` (eighth carrier, corrected in the
  Phase 7 addendum above)
