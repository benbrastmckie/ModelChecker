# Implementation Summary: Task #211

- **Task**: 211 - Correct kernel-checked-proof overclaim
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T07:09:21Z
- **Completed**: 2026-09-28T08:15:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_kernel-checked-proof-overclaim.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Resolved a live self-contradiction in the bimodal trust documentation about what an
`"acceptance":"entailment"` verdict licenses, retired the dead `BIMODAL_LOGIC_COMMIT` pin, and
corrected a now-stale claim that the Lean-side half of obligation S4 was unattempted. A sweep
pass (Phase 5) found and fixed one additional stale S4 site beyond the plan's original scope
hypothesis, and reworded one docstring to fully retire the dead constant's literal name, not
just its declaration.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — Rewrote the two overclaiming
  `"kernel-checked proof"` sites (§6.1 `"acceptance"` paragraph, §6.2 entailment paragraph) to
  the accurate narrower wording already landed in `SETTINGS.md`/`semantic/model.py`; aligned the
  S4 obligation-table row and the transcription-audit Residual paragraph with the corrected S4
  position; fixed a third stale S4 site (a translation-elimination note) found during the Phase
  5 sweep, not enumerated in the original plan.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — Corrected the "What
  remains" opening paragraph and the "In the Lean development" table row: the Lean-side S4
  truth-preservation theorem (`sat_iff`, `SentenceTruth.lean`) has landed upstream in
  BimodalLogic, along with a `translate_sentence` executable and a fixture corpus; added a new
  "In this repository" row naming the remaining wiring work (diffing this repository's own
  translation against the fixture).
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` — Deleted the unconsumed
  `BIMODAL_LOGIC_COMMIT` constant and its `__all__` export.
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` — Re-tensed the "capability
  handshake" docstring sentence that narrated `BIMODAL_LOGIC_COMMIT` in the present tense;
  reworded it a second time (Phase 5) to drop the literal constant name entirely while
  preserving the drift evidence (`d55e2760` → `d1a24b30`, observed same-day).

## Decisions

- Copied `SETTINGS.md`/`semantic/model.py`'s already-landed, reviewed wording verbatim into
  `ADEQUACY.md` rather than paraphrasing, per the dispatch's explicit instruction.
- Retired `BIMODAL_LOGIC_COMMIT` rather than auto-tracking it: enforcement already lives in
  `semantic/checker.py`'s capability handshake (verifying the binary's actual behaviour), and the
  constant had drifted repeatedly while being consumed by nothing.
- Item 3 (S4 deferral) was corrected as a fresh probe rather than deferring to task 209's
  findings, per the dispatch's conditional: task 209 had not landed and its declared scope
  excludes this documentation correction.
- Preserved the distinction that the upstream `sat_iff` theorem certifies BimodalLogic's own
  reference translation, not this repository's implementation — explicitly stated in every
  rewritten site rather than left implicit.

## Plan Deviations

- **Phase 2** altered: the plan's own Verification bullet required
  `grep -rn "BIMODAL_LOGIC_COMMIT" /home/benjamin/Projects/ModelChecker` to return nothing, but
  the initial docstring rewrite in `semantic/checker.py` still used the literal constant name in
  prose (to "preserve the drift evidence"). Reworded a second time in Phase 5 to describe the
  retired constant without repeating its literal name, satisfying the zero-hits criterion while
  still preserving the drift evidence (commit hashes and dates).
- **Phase 5** found and fixed a stale S4 site at `ADEQUACY.md:567` (a translation-elimination
  note in the transcription-audit discussion) that Phase 4's scope hypothesis had not enumerated
  (it named only lines 80 and 300). Folded into Phase 5's sweep per its own instruction to treat
  any additional S4-contradiction hit as in scope.

## Verification

- Build: N/A (documentation + dead-code removal)
- Tests: Passed — `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
  (640 passed); `PYTHONPATH=code/src pytest code/tests/ -q` (645 passed, 5 skipped, 0 failed on
  the second full run — see Follow-ups for the one flaky first-run segfault, unrelated to this
  task's scope).
- Files verified: Yes — all four modified files re-read after editing; `git diff --stat` confirmed
  only the intended file changed per phase; `git log`/`git status` confirmed no foreign work from
  concurrent task 209 (which shares `tests/_lean_check.py` in its `file_scope`) was swept in.

## Impacts

- `docs/ADEQUACY.md`, `docs/TRUST_PIPELINE.md`, `docs/A2_GAP.md`, and `docs/SETTINGS.md` now
  agree on both claims: what `"acceptance":"entailment"` licenses, and where the Lean-side S4
  theorem stands. A reader consulting any one of the four documents gets the same answer.
- The overclaim never reached users (`semantic/model.py`'s `_verification_label` was already
  written from the Lean docstring directly), so this closes a documentation-consistency defect
  rather than a false user-facing claim — no runtime behavior changed.
- `BIMODAL_LOGIC_COMMIT` no longer exists anywhere in the tree; the capability handshake in
  `semantic/checker.py` remains the sole enforcement mechanism, now correctly narrated in the
  past tense.

## Follow-ups

- A Z3-internal segfault in `code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building`
  was observed on the first full-suite run of `code/tests/` (thread-contention crash inside
  `Z3_substitute`, in unrelated logos/solver code). It passed 3/3 in isolation and the full suite
  passed cleanly (645 passed, 5 skipped, 0 failed) on a second run with that one test deselected.
  This is a pre-existing environmental flake, not a regression from this task's documentation and
  dead-constant changes — worth a dedicated investigation if it recurs, but out of this task's
  scope.
- Consuming the upstream `translate_sentence`/`sat_iff` fixture from this repository's own
  translation (the sentence-translation conformance work) remains open; this task only corrected
  the documentation's description of where that work stands, per its declared non-goals.

## References

- Plan: specs/211_correct_kernel_checked_proof_overclaim/plans/01_kernel-checked-proof-overclaim.md
- Research report: specs/211_correct_kernel_checked_proof_overclaim/reports/01_kernel-checked-proof-overclaim.md
- Dispatch: specs/211_correct_kernel_checked_proof_overclaim/.dispatch/6.md
