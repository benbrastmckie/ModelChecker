# Phase 2 Handoff: Verify the fix and audit sibling boundary sites

- **Status**: COMPLETED
- **Files modified**: `oracle/bimodal_logic/tests/test_oracle_interface.py`

## Primary target verification

5/5 isolated runs of `test_all_sat_task_relation_ternary` PASSED: 53.79s, 63.80s, 52.46s, 51.19s,
50.98s wall clock (call durations 53.59/63.55/52.29/50.99/50.79s). Max 63.55s = 35.3% of the
180000ms budget, comfortably under the 120000ms escalation bar. `TestTernarySerializationAll`
passes end to end (2 passed in 50.47s).

## Sibling audit and widening applied

Widened `TEMPORAL_SOLVE_TIMEOUT_MS` at three additional sites:
- Line 739 (`test_enriched_vs_primitive_sat_agreement`'s depth>0 timeout expression) — the `next`
  parametrize case measured 104.02s combined (enriched+primitive), same M=3 boundary as the
  primary fix.
- Line 815 (`test_mixed_and_neg_some_future`) — measured 38.54s pre-edit, >30000ms threshold.
- Line 959 (`test_spot_check_individual_countermodels`'s F5 call) — isolated single-call timing
  showed only 0.64s (widening was not strictly necessary here but is harmless).

Left unchanged with measured headroom: `test_mixed_and_box_next` (14.21s), `test_mixed_or_diamond_prev`
(1.33s), `test_mixed_and_all_future_neg` (21.62s) — all >=2x headroom under the existing 60000ms.

Left unchanged by design (tolerate `None`): `test_deeply_nested_enriched` (60.34s, at its own
ceiling) and the `valid_formulas` loop (F4/F7/F9/F10, ~241s/4 calls).

## Deviation from plan's site enumeration

The plan listed "line 951-952 and line 964" as both asserting non-`None`. Direct inspection shows
only the F5 call (line 951-952, now 959) asserts non-`None`; the loop starting at the plan's
"line 964" (now line 972) asserts `result is None` for F4/F7/F9/F10. Corrected: only F5 is in the
assert-non-`None` cohort; the loop is treated as a tolerates-`None` site and left unchanged.

## Finding for the downstream full-suite task (not fixed here — out of scope per this plan's own
anti-scope-creep mitigation)

Isolated instrumentation of the `all_future` enriched/primitive pair shows **both forms time out
even at the new 180000ms budget** (enriched: 195.47s, primitive: 187.63s, both returning `None`).
The parametrized test still passes because both sides agree (`None == None`), but this is very
likely a masked timeout-equivalence rather than a verified semantic agreement, and the same
pathology already existed at the original 60000ms budget. This is a genuinely slow query, not a
boundary flake — recorded as a finding, not fixed, consistent with the plan's Non-Goals (no
solver-performance work). `test_deeply_nested_enriched` and the `valid_formulas` loop show the
same tolerate-`None` pattern near their own 60000ms ceiling and may have the same masking issue.

## Verification commands run (all inside `nix develop`)

- 5x isolated primary target run — all PASSED, see above.
- `TestTernarySerializationAll` class run — 2 passed.
- `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement` (11 parametrized cases) — all
  11 PASSED, run post-widening-edit.
- `TestMixedFormulas` (5 tests) — all 5 PASSED, run post-widening-edit.
- `TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` — PASSED, run
  post-widening-edit.
- `grep -n "60000" oracle/bimodal_logic/tests/test_oracle_interface.py` — remaining occurrences
  (823, 830, 837, 845, 972) all correspond to sites explicitly left unchanged above.

Note: the plan's single combined `-k "enriched_vs_primitive or mixed_ or ternary"` verification
command exceeded a 10-minute tool timeout when run as one invocation (the `all_future` case alone
now takes ~380s post-widening); it was run instead as three separate sequential invocations
(enriched_vs_primitive, mixed_, ternary/class-level), each completing well within its own
timeout, with identical pass/fail semantics to the combined form.

## Deviations from plan

- Site-enumeration correction for the `valid_formulas` loop (see above) — reclassified from
  assert-non-`None` to tolerates-`None`.
- Verification split into three sequential commands instead of one combined `-k` invocation, due
  to wall-clock growth from the `all_future` finding (10-minute tool timeout, not a plan
  deviation in outcome — same tests, same pass results).
- New finding recorded (not a deviation, an addition): `all_future` enriched/primitive pair
  genuinely exceeds 180000ms; reported for the downstream task rather than fixed.

## Next

Proceed to Phase 3: correct the task's `completion_summary` in `specs/state.json`, write the
implementation summary, and record the verified full-suite handoff invocation.
