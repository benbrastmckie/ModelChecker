# Phase 4 Handoff: Doc corrections — the narrower true claim only

- **Status**: [COMPLETED]

## What changed

- `docs/ADEQUACY.md` §6.1: added the canonical-bytes wire requirement (compact separators, fixed
  key order, `ensure_ascii=False`, single serializer `certificate.canonical_wire_bytes`), and
  `"acceptance"` to the documented output shapes (on `countermodel` only, absent-reads-as-
  `"decided"`).
- `docs/ADEQUACY.md` §6.2: added a new paragraph after the existing sentence (not a replacement)
  describing what `"acceptance":"entailment"` means — a kernel-checked proof for that particular
  certificate via `WitnessFamily.joint_countermodel` — scoped explicitly to the differential test
  tier, silent on the live path.
- `docs/TRUST_PIPELINE.md`: split the single "Consume a proof-producing checker; verify the
  parse" row into two — the proof-producing half marked done and consumed, the echo half marked
  still open. Added a scoped note to the "re-checker implementation" trust-base bullet.
- `docs/A2_GAP.md` route (f): updated the Cost/status cell to record the first half landed and
  consumed, second half (echo) still open. What route (f) *buys* is unchanged.

## Verification performed

- `grep -rni "pre-filter\|no longer in the trust base" docs/`: no matches (prohibition holds —
  the joint demotion claim is not written anywhere).
- Diff read-through: every changed hunk is prose; §6.2's original sentence survives unedited,
  with the new paragraph appended after it.
- Cross-references resolve: `canonical_wire_bytes` (§6.1) matches the symbol added in Phase 1;
  `§6.2` references from §6.1 and the new paragraph both resolve to the correct section.
- `semantic/model.py` lines 1-25 re-read: confirmed the "F5" judgment still holds — the module
  docstring describes only the Python re-checker's role (`certificate.recheck`, obligation S3)
  and makes no claim about Lean acceptance; it is accurate as written and left unchanged.

## Deviations from plan

None.

## Next phase

Phase 5 (parse-echo verification, axis 2) — **gated, but the gate has very likely flipped**.
Phase 3's handoff already flagged that BimodalLogic's echo-field phase is now committed
(`d55e2760e6731a2240f3db5d761658947bf69125`, past `3fad162e5`) and the README no longer carries
"jointly gated, and has not landed yet". Phase 5 must still take its own fresh gate measurement
per the plan's discipline, but the expected outcome is now **admission**, not closure with
exclusions.
