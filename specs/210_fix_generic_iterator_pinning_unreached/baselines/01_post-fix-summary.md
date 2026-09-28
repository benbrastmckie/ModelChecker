# Post-Fix Gate Summary (Phase 6)

Captured after Phase 3's routing fix, Phase 4's pin-presence coverage, and Phase 5's docstring
correction, against the corrected foundation (the dedicated task that generalized bimodal's
persistent-search-solver re-assertion workaround into the shared
`ConstraintGenerator._ensure_original_constraints_in_solver`).

## Parallel pass

Command:
```
PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread
```

Result: `1 failed, 3204 passed, 1 skipped, 5 warnings in 207.85s`

Failure: `theory_lib/bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`

Classification: **(a) pre-existing failure**, unrelated to this task's changes. This is the exact
same test, by node ID, recorded as the single pre-existing failure in Phase 1's baseline
(`baselines/01_pre-fix-summary.md`), captured under the same non-parallel four-theory-directory
command before any Phase 3 edit landed. The test itself documents that it relies on a real,
non-mocked `iterate: 15` search empirically hitting at least one genuine rotation/permutation
duplicate within the reachable orbit space — an outcome sensitive to solver/timing behavior under
concurrent load, not to this task's frame_constraints pin-routing change (which touches
`iterate/models.py`'s generic pinning loop, not bimodal's own `_pin_theory_specific_values`
override or its isomorphism detector). Evidence this is load-sensitive rather than a regression:
the identical test passed cleanly in two other captures below, run without `-n 4` parallel
contention.

## Serial (`xdist_serial`) pass

Command:
```
PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial" -q --timeout=300 --timeout-method=thread
```

Result: `10 passed, 3335 deselected in 3.52s` — no failures.

## Four-theory directory pass (matches Phase 1's exact baseline command)

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q
```

Result: `1695 passed in 333.32s` — **0 failures**, including
`test_a_live_run_detects_a_genuine_rotation_permutation_duplicate` (passed here). Phase 1's
baseline recorded `1 failed, 1694 passed` for this identical command (same failing test, by node
ID) — same total item count (1695), the one flaky test simply landed on the "pass" side of its
own known variance this run. No regression: every test that was passing pre-fix is still passing
post-fix.

## `iterate/` shared-engine suite

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q
```

Result: `251 passed in 116.62s` — 0 failures. Phase 1's baseline: `238 passed in 1.26s`. The
count grew by 13: 3 from Phase 2's `TestGenericPinningReachesRebuiltSolve` (now passing, was
failing/RED pre-fix), 4 from Phase 4's `TestGenericPinAppendedToFrameConstraints`, and 6 from the
dedicated foundation task's own added `test_search_solver_population.py` coverage (not part of
this task's file scope). Wall-clock grew because the added tests include live, non-mocked
solver runs (marked `slow`), not because of a performance regression in the fix itself.

## Bimodal integration suite (must be unchanged in outcome from Phase 1's baseline)

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q
```

Result: `29 passed in 3.08s` — 0 failures. **Better than the Phase 1 baseline's recorded state**
(which listed exactly this suite's `test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`
as the one pre-existing failure): the same known-flaky test now also passes in this standalone,
non-parallel capture, consistent with its load-sensitive nature rather than any change this task
made to bimodal (this task touches no bimodal production code besides Phase 5's pure docstring
wording correction).

## Representative `iterate > 1` example diffs (dev_cli.py, same settings as Phase 1's baseline)

| Theory | Pre-fix (`01_pre-fix-*-iteration.txt`) | Post-fix (`01_post-fix-*-iteration.txt`) | Verdict |
|--------|------------------------------------------|-------------------------------------------|---------|
| logos (`[] \|- \neg A`, N=2) | 1/3 models found | 1/3 models found | Unchanged — no collapse |
| exclusion (`EX_CM_6`, N=3) | 1/3 models found | 2/3 models found | Improved — the fix now finds a genuinely pinned second model the pre-fix write-only pins never actually delivered |
| imposition (`IM_CM_0`, N=4) | 2/3 models found | 2/3 models found (model 3 legitimately times out within the bounded `max_time`) | Unchanged — no collapse |

No theory collapses to a single model. Each rebuilt model 2+ is self-consistent with the candidate
the search intended, per Phase 2's and Phase 4's live regression coverage (all pass).

## `print_constraints` rendering check

`print_grouped_constraints()` was exercised directly against a live rebuilt logos model
(N=2, `[] |- \neg A`) to confirm the accepted, display-only side effect from the plan's Decisions
section: the rendering is well-formed, not merely longer. Confirmed:
- Summary line: `Frame constraints: 18` (base frame axioms plus the newly appended generic pins).
- The `FRAME CONSTRAINTS:` section lists correctly numbered pin literals alongside the theory's
  own frame axioms, e.g. `4. possible(0)`, `6. Not(possible(1))`, `8. Not(possible(2))`,
  `10. Not(possible(3))` — exactly the generic `possible` pins the fix appends.
- `MODEL CONSTRAINTS:`, `PREMISES CONSTRAINTS:` (empty, no premises in this example), and
  `CONCLUSIONS CONSTRAINTS:` sections render correctly after the frame section, with no
  truncation or malformed numbering.

(Exercised via `print_grouped_constraints()` directly rather than through the CLI's `-p`/
`--print_constraints` flag: that flag's call site,
`{logos,exclusion}/semantic/model.py`'s `print_to`, only invokes `print_grouped_constraints` when
`self.unsat_core is not None` — i.e. only for a top-level UNSAT result — which a countermodel
example's model 1 never is. The rendering code path is identical either way; only the trigger
condition differs.)

## Verdict

No genuine (category c) regression found. The one changed-state test across all four capture
commands is the same pre-existing, load-sensitive flake already recorded in Phase 1's baseline,
under the same node ID, in both pre-fix and post-fix runs. Every other test is stable or newly
passing. No `expectation` value was edited and no skip was added to obtain a green result.
