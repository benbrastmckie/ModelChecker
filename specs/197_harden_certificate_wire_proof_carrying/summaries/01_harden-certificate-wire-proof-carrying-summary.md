# Implementation Summary: Harden Certificate Wire Proof-Carrying

- **Task**: 197 - Harden certificate wire proof carrying
- **Plan**: `plans/01_harden-certificate-wire-proof-carrying.md`
- **Status**: All six phases `[COMPLETED]`

## Overview

The certificate wire protocol between this repository and `lake exe check_certificate` had gone
stale on two axes at once: the differential test tier was silently dead (a canonical-bytes-only
parser on the consuming side rejected this repository's non-canonical `json.dumps` whitespace,
and the failure was swallowed by the skip machinery), and neither axis of BimodalLogic's
proof-carrying upgrade (constructed entailment, parse-echo verification) was consumed. This
implementation restored the tier, hardened it against a repeat of the same silent failure, and
consumed both landed axes.

## What was built, phase by phase

1. **Canonical wire bytes** (`certificate.py`'s `canonical_wire_bytes`): the single authoritative
   serializer — compact separators, `ensure_ascii=False`, canonical-by-construction key order.
   `_lean_check.py`'s `run_check_certificate` now uses it. This alone revived the differential
   tier from a clean-skip to running and green.
2. **Loud protocol failures**: `_lean_check.py`'s `probe()` now splits environment absence
   (`SKIP_REASON`) from protocol disagreement (`PROTOCOL_FAILURE`), asserted `None` by a dedicated
   test — so a future protocol drift fails loudly instead of silently deleting the tier again, as
   demonstrated by reverting Phase 1's change locally and observing the loud failure.
3. **The `"acceptance"` key (axis 1)**: `countermodel` verdicts' `"acceptance"` field is now read
   and asserted `"entailment"` against the current binary, on both the fixture corpus and the
   live-extracted certificate, with the absent-reads-as-`"decided"` rule encoded in the assertion
   message itself.
4. **Doc corrections**: `ADEQUACY.md` §6.1/§6.2, `TRUST_PIPELINE.md`, and `A2_GAP.md` route (f)
   updated to state the narrower true claim, without asserting the joint trust-base demotion
   before axis 2 landed.
5. **Parse-echo verification (axis 2)**: the plan's admission gate, which the plan expected might
   fail (BimodalLogic's echo interface was uncommitted at plan-authoring time), instead **passed**
   — BimodalLogic committed the echo-field phase while this task was in flight. Implemented
   `run_check_certificate_with_sent` and `assert_echo_matches_sent`, comparing the Lean side's
   `"echo"` bytewise against the bytes actually sent, on the whole fixture corpus (both positive
   and negative cases) and the live-extracted certificate, classified as a protocol error on
   mismatch.
6. **The joint trust-base claim**: with both axes consumed, recorded — scoped precisely to the
   differential test tier, leaving the live path (`semantic/model.py`) unaffected since it never
   calls the binary — that the Python re-checker there has become a fast pre-filter, citing
   `BimodalTools.CanonicalWire.print_parse_canonical` as the theorem the guarantee rests on.

## Significant finding: the plan's gate assumption flipped mid-implementation

The plan carried axis 2 as gated-likely-closed, since BimodalLogic's echo interface was
uncommitted at plan-authoring time (M2). While Phase 3 was in flight, BimodalLogic committed the
echo-field phase and two further completion commits. Phase 5's admission gate, re-measured fresh
at its own start per the plan's discipline, passed — so axis 2 was implemented in full rather than
closed with exclusions, and Phase 6 (also gated on Phase 5) executed as well.

## Verification

- `code/tests/`: 645 passed, 5 skipped (pre-existing, unrelated).
- `code/src/model_checker/theory_lib/bimodal/tests/` with the checkout present: 601 passed, 0
  failed.
- Same suite with `BIMODAL_LOGIC_PATH=/nonexistent`: 586 passed, 15 skipped, 0 failed —
  environment-absence skip discipline intact.
- Transient CPU-contention timeouts were observed twice during implementation (a concurrent
  `lake build` compiling the entire BimodalLogic checkout); every affected test passed cleanly in
  isolation once re-run, confirmed unrelated to this task's changes.
- One unrelated failure was observed during a full-suite run
  (`test_iterate.py::TestAllConstraintsReflectsCertificateAfterSolve`), traced via `git log` to a
  concurrent sibling task's own deliberate TDD RED-phase commit in this shared working tree —
  not this task's regression.

## Plan Deviations

- Phase 2: `probe()`'s protocol-failure condition is `status != "countermodel"` (any unexpected
  answer from a responding binary), not the narrower literal `status == "error"` the task text
  named — already the pre-existing condition in the old single-vocabulary `probe()`; Phase 2 only
  reclassified which bucket it lands in. Recorded inline in the plan.
- Phase 5: `docs/ADEQUACY.md` §6.1 was corrected to record `"echo"` on `rejected` verdicts too
  (Phase 4's edit had understated it as `countermodel`-only) — a wire-contract accuracy fix
  surfaced by Phase 5's own measurement (M3), not a deviation from either phase's task list.
- No other deviations. Every task-list item across all six phases was completed as planned.

## Files Changed

- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
