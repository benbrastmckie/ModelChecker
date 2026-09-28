# Phase 3 Handoff: Consume the `"acceptance"` key (axis 1)

- **Status**: [COMPLETED]

## What changed

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`:
  `TestLeanAgreement.test_lean_verdict_matches_expected` now asserts, on fixtures whose expected
  status is `countermodel`, that `verdict.get("acceptance", "decided")` is one of
  `{"entailment", "decided"}` and equals `"entailment"` against the current binary. Docstring
  gained an `"acceptance"` section and a refreshed provenance line.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py`:
  `TestExportedCertificateAgreesWithLeanBinary` extended the same way on the live-extracted
  certificate. Class docstring gained the same explanation.
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`: `BIMODAL_LOGIC_COMMIT`
  refreshed to `d55e2760e6731a2240f3db5d761658947bf69125`.

## Significant finding: BimodalLogic advanced past the plan's M2 snapshot

While this phase was in flight, BimodalLogic's checkout moved forward substantially:
- `git -C ~/Projects/BimodalLogic log --oneline -3` now shows the echo-field phase committed
  (`3fad162e5`) plus two further "complete implementation" commits, HEAD
  `d55e2760e6731a2240f3db5d761658947bf69125`.
- `BimodalTools/README.md` no longer carries "jointly gated, and has not landed yet" — it now
  reads "both halves have now landed on this side."
- A live probe confirms both `"acceptance":"entailment"` **and** `"echo"` are present on a
  `countermodel` verdict.

**This means Phase 5's admission gate (axis 2, parse-echo verification) will very likely PASS**
when Phase 5 runs its own gate measurement — the interface is now committed, not merely present
in a working tree. Phase 5 must still take its own fresh measurement per the plan's own
discipline ("a measurement taken at Phase 5's own start, not a fact inherited from this plan"),
but the direction is now toward *implementing* axis 2, not closing it with exclusions.

The overall `git status --porcelain` in that checkout is still non-empty (four `FormalSystem/`
files unrelated to the certificate protocol), so the pin follows the plan's dirty-tree discipline:
HEAD pinned, with the caveat scoped to the specific unrelated files rather than a blanket claim.

## Verification performed

- `pytest .../test_certificate_lean_agreement.py .../test_semantics_core.py -v`: 29 passed.
- Full corpus + live certificate both assert `acceptance == "entailment"` against the current
  binary; no fixture or live case reads as `"decided"`.

## Deviations from plan

None beyond the M2-supersession finding recorded above (an update, not a deviation from the
task list itself — every task-list item was completed as written).

## Next phase

Phase 4: doc corrections (the narrower true claim only) — `ADEQUACY.md` §6.1/§6.2,
`TRUST_PIPELINE.md`, `A2_GAP.md`. Given the M2-supersession finding above, Phase 5's implementer
should re-run the admission gate fresh rather than assume Phase 4's docs will still describe axis
2 as closed.
