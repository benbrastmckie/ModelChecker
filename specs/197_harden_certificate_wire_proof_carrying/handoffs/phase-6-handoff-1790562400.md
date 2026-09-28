# Phase 6 Handoff: The joint trust-base claim — gated on Phase 5 executing

- **Status**: [COMPLETED]

## Admission

Phase 5 closed `[COMPLETED]` — admitted.

## What changed

- `docs/TRUST_PIPELINE.md`: "The trust base" list's re-checker bullet rewritten to be scoped by
  path, not a blanket claim — differential test tier: fast pre-filter (both halves landed and
  consumed); live path: still fully in the trust base. "What remains" row for axis 2 relabeled
  "done" with the scoped demotion sentence appended.
- `docs/ADEQUACY.md` §6.2: added a paragraph naming
  `BimodalTools.CanonicalWire.print_parse_canonical` as the theorem the joint guarantee rests on,
  scoped identically (differential test tier only; live path unaffected, cross-referencing
  `TRUST_PIPELINE.md`).
- `docs/A2_GAP.md` route (f): Cost/status cell updated to "both halves landed and consumed",
  scoped to the differential test tier; what route (f) buys is unchanged.

## Grounding

Re-read BimodalLogic's committed `BimodalTools/README.md` "The joint canonical contract" section
and `BimodalTools/CertificateImport.lean`'s header in full before writing. The README's own
post-phase-9 wording: "The downstream payoff was jointly gated, and both halves have now landed
on this side... What remains is on the consuming side: it must actually perform the comparison,
and pin `ensure_ascii=False` in its exporter." This repository has now done both (Phase 1 pinned
`ensure_ascii=False`; Phase 5 performs the comparison), so the joint claim is licensed by the
producing side's own contract prose, not merely inferred.

## Verification performed

- `grep -n "print_parse_canonical" docs/ADEQUACY.md`: found.
- Diff read-through: every changed hunk is prose; every demotion sentence carries its scope
  (test tier versus live path).
- `grep -rni "pre-filter\|no longer in the trust base" docs/`: 3 matches, all in this phase's own
  scoped sentences (the prohibition enforced in Phase 4 applied only up to this phase).

## Full plan-level Testing & Validation checklist (run at this phase's close)

- `SKIP_REASON` prints `None` with the checkout present — tier alive.
- `PYTHONPATH=code/src pytest code/tests/ -q`: 645 passed, 5 skipped (pre-existing, unrelated).
- `grep -rn "json.dumps" .../bimodal/`: every remaining hit is a comment, docstring, or a
  self-contained round-trip test that never feeds the Lean binary (`test_certificate.py`'s
  `test_json_round_trips_through_stdlib_json` and its own `sort_keys` demonstration test,
  `test_formula.py`'s round-trip test) — no site feeds the binary without
  `canonical_wire_bytes`.
- `git diff .../certificate.py .../formula.py` grepped for `back/mid/fwd/bx/lassos/target`:
  empty — no input-schema key was renamed or extended.
- `BIMODAL_LOGIC_PATH=/nonexistent pytest .../bimodal/tests/ -q`: in progress at handoff time
  (background); Phase 2 and Phase 5 each already confirmed this independently (585 passed / 15
  skipped, and again clean in Phase 5's own full-suite run).
- Full `.../bimodal/tests/ -v` (checkout present): 601 passed, 0 failed (confirmed at Phase 5's
  close, re-confirmed unaffected by Phase 6's doc-only changes).

## Deviations from plan

None.

## Plan status

All six phases `[COMPLETED]`. This is the final phase — proceeding to the implementation summary
and final metadata.
