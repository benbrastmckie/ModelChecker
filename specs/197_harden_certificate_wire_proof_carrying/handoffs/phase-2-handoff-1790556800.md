# Phase 2 Handoff: A protocol failure is loud, never a clean skip

- **Status**: [COMPLETED]

## What changed

- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`: `probe()` now returns
  `(skip_reason, protocol_failure)` instead of a single failure string. `SKIP_REASON` keeps its
  existing meaning (environment absence: no checkout, no `lake`, binary never answers) and
  spelling; a new module-level `PROTOCOL_FAILURE: Optional[str]` captures a binary that answers
  but not with `"countermodel"` on the trivial probe. Added `PROTOCOL_FAILURE` to `__all__` and
  a substantial module-docstring section naming the two vocabularies and citing M1 as the
  motivating incident.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`:
  new `TestProtocolFailureIsLoud.test_protocol_failure_is_none`, asserting `PROTOCOL_FAILURE is
  None` with the verdict quoted in the failure message.

## Verification performed

- With the checkout present: `test_certificate_lean_agreement.py` — 11 passed (including the new
  test).
- Reverted Phase 1's `canonical_wire_bytes` call locally (`input=json.dumps(payload)`) and
  re-ran `TestProtocolFailureIsLoud` alone: **failed loudly**, not skipped, with message:
  `probe certificate produced unexpected verdict: {'status': 'error', 'message': 'expected a
  decimal numeral'}`. Restored the serializer call immediately after, confirmed green again.
- `BIMODAL_LOGIC_PATH=/nonexistent PYTHONPATH=code/src pytest .../bimodal/tests/ -q`: 585 passed,
  15 skipped, 0 failed — environment absence still skips cleanly, unaffected by the split.
- Full `.../bimodal/tests/ -q` (checkout present): 600 passed, 1 failed
  (`test_iterate.py::TestAllConstraintsReflectsCertificateAfterSolve::...`). This is sibling task
  207's own deliberate TDD RED-phase test, committed concurrently in this same working tree
  (`git log`: `1485c3e3 task 207 phase 1: baseline and failing tests (RED)`, touching
  `iterate/models.py` and `models/constraints.py`) — not caused by this phase's changes.
- A second full-suite pass surfaced two more failures in this task's own certificate tests
  (`test_certificate_a2_triangle.py::TestBoundedLeanCrossCheck` and
  `test_semantics_core.py::TestExportedCertificateAgreesWithLeanBinary`), both timing out under
  heavy concurrent CPU load: `ps aux` showed a `lake build` compiling the entire BimodalLogic
  checkout at the same time (load average 14.6, several `lean` processes at 100%+ CPU each).
  Both tests pass cleanly in isolation once re-run (`boxed_closure_sat` took 46.73s, close to but
  under its bound) — confirmed transient/environmental, not a code regression from this phase.

## Deviations from plan

`probe()`'s protocol-failure condition is `status != "countermodel"` (any unexpected answer from
a responding binary), not the narrower literal `status == "error"` the task text names — this was
already the pre-existing condition in the old single-vocabulary `probe()`; Phase 2 only
reclassifies which bucket it lands in, and a `"rejected"` or other unexpected status is equally a
protocol disagreement on this engineered-to-be-`countermodel` trivial probe. Recorded inline in
the plan's Phase 2 task list too.

## Next phase

Phase 3: consume the `"acceptance"` key on `countermodel` verdicts (axis 1).
