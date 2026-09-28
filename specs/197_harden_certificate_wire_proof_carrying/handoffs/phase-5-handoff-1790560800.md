# Phase 5 Handoff: Parse-echo verification (axis 2) — gated

- **Status**: [COMPLETED]

## Admission gate: PASSED (measured fresh at this phase's start)

- `git -C ~/Projects/BimodalLogic log --oneline -1` → `d55e2760e task 678: complete implementation`
- `git -C ~/Projects/BimodalLogic log -1 --format=%s -- BimodalTools/CertificateImport.lean` →
  `task 678 phase 9: the echo field, the defect guards, and the joint contract`
- `grep -n "jointly gated, and has not landed" BimodalTools/README.md` → no output (the README
  now reads "both halves have now landed on this side")
- Live probe of `01_positive_box.json` → `{"status":"countermodel","time":0,
  "acceptance":"entailment","echo":"…"}` — `"echo"` present.
- Overall `git status --porcelain` in that checkout was non-empty (four unrelated `FormalSystem/`
  files, same set Phase 3 recorded), but neither `CertificateImport.lean` nor `README.md` was
  among them.

Both gate conditions held, so this phase was **implemented**, not closed with exclusions.

## What changed

- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`: added
  `run_check_certificate_with_sent` (returns `(verdict, sent)`; `run_check_certificate` is now a
  thin wrapper over it, unchanged for its three pre-existing consumers) and
  `assert_echo_matches_sent` (the bytewise comparison, classified as a protocol error on
  mismatch or a missing `"echo"` where one is expected; `"error"` verdicts asserted to carry no
  `"echo"` at all). Both added to `__all__`. Module docstring gained an axis-2 paragraph.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`:
  `TestLeanAgreement` and both `TestErrorPaths` tests now use `run_check_certificate_with_sent`
  and call `assert_echo_matches_sent` — covering all four corpus fixtures (positive and negative
  echo cases) plus the two protocol-error fixtures.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py`:
  `TestExportedCertificateAgreesWithLeanBinary` extended the same way on the live-extracted
  certificate — the one place a certificate this repository actually built (not a hand-written
  fixture) is echo-compared, catching a `bx`-iteration-order or atom-escaping defect the corpus
  cannot.
- `docs/ADEQUACY.md` §6.1: corrected the wire-contract output shapes to record `"echo"` on both
  `countermodel` and `rejected` (not `countermodel` only, as Phase 4's edit had understated), and
  added an `"echo"` explanation paragraph. This is a wire-contract accuracy fix surfaced by this
  phase's own measurement (M3), not the Phase-6-scoped joint trust-base claim.

## Verification performed

- `test_certificate_lean_agreement.py -v`: 11 passed (echo comparison exercised on all 4
  fixtures plus both error-path fixtures).
- `test_semantics_core.py -k Lean -v`: 1 passed, confirmed run (not skipped) — live-certificate
  echo comparison holds, no `bx`-order or escaping divergence found.
- Perturbed the sent bytes locally (reordered a `bx` entry's atom name) and called
  `assert_echo_matches_sent` directly: raised `AssertionError` whose message contains "protocol"
  and not "rejected". Confirmed by direct invocation (not a permanent test).
- `PYTHONPATH=code/src pytest code/tests/ -q`: 645 passed, 5 skipped (pre-existing, unrelated).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`: **601
  passed, 0 failed** — the full bimodal suite is completely green, including the two tests that
  saw transient CPU-contention timeouts during Phase 2's verification (both now pass consistently
  now that the concurrent `lake build` in the BimodalLogic checkout has finished).

## Deviations from plan

None. Every task-list item completed as written; the ADEQUACY.md §6.1 correction (echo also on
`rejected`) is an accuracy fix within §6.1's own scope, not a deviation from Phase 5's task list.

## Research gathered for Phase 6 (not yet written)

Read BimodalLogic's committed `BimodalTools/CertificateImport.lean` and `BimodalTools/README.md`
in full for Phase 6's citation requirements:

- The theorem's fully-qualified name is `BimodalTools.CanonicalWire.print_parse_canonical`
  (the plan abbreviates it as `print_parse_canonical`).
- The README's own post-phase-9 section ("The joint canonical contract") states verbatim: "The
  downstream payoff was jointly gated, and both halves have now landed on this side, ... What
  remains is on the consuming side: it must actually perform the comparison, and pin
  `ensure_ascii=False` in its exporter." **This repository has now done both** (Phase 1 pinned
  `ensure_ascii=False`; Phase 5 performs the comparison) — so the joint claim is now fully
  licensed on both sides, scoped as the plan requires to the differential test tier versus the
  live path.

## Next phase

Phase 6: the joint trust-base claim, gated on Phase 5 executing — admitted, since Phase 5 closed
`[COMPLETED]`.
