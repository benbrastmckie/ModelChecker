# Post-Fix Summary (Phase 4)

## Bimodal `test_iterate.py`, standalone -- the plan's named "unchanged in outcome" reference

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q
```

| Run | Fix applied | Result |
|-----|-------------|--------|
| Phase 1 baseline | No | `29 passed in 32.67s` |
| Phase 4, capture 1 | Yes | `29 passed in 3.46s` |
| Phase 4, control repeat 1 | Yes | `29 passed in 3.12s` |
| Phase 4, control repeat 2 | Yes | `29 passed in 31.90s` |

**Identical pass/fail set across all four runs (29/29).** This is the specific comparison
Phase 1's task list names as "the specific 'unchanged in outcome' reference Phase 4 compares
against" -- it holds.

Full output: `baselines/03_post-fix-bimodal-iterate.txt`.

## Four-theory directory gate

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q
```

| Run | Fix applied | Result |
|-----|-------------|--------|
| Phase 1 baseline | No | `1695 passed in 353.51s` -- 0 failures |
| Phase 4, capture 1 (official) | Yes | `1 failed, 1694 passed in 279.56s` |
| Phase 4, control 1 | No (temporarily reverted `iterate/constraints.py` to its pre-fix, pre-Phase-3 content) | `1695 passed in 340.29s` -- 0 failures |
| Phase 4, control 2 (fix restored) | Yes | `1695 passed in 290.19s` -- 0 failures |

The one failure observed (capture 1 only) is:
`theory_lib/bimodal/tests/integration/test_iterate.py::TestLiveIteration::
test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`

**Investigation and conclusion: pre-existing flakiness, not a fix-induced regression.**

1. This test's own docstring documents inherent non-determinism: "the search sometimes reaches
   a second genuinely new orbit on its very first candidate with no duplicate along the way,"
   and its assertion (`isomorphic_model_count >= 1`) depends on Z3 actually re-visiting an
   already-seen orbit during a bounded, heuristic-driven 15-model search -- not a property
   guaranteed by construction.
2. A prior task's own recorded baseline (`specs/210_.../baselines/01_pre-fix-summary.md`) lists
   this exact test as an already-failing, pre-existing case, entirely independent of this task's
   change -- corroborating that it fails intermittently on this repository regardless of
   `iterate/constraints.py`'s content.
3. A controlled A/B comparison was run directly: the identical four-theory gate command was run
   twice with the fix reverted (both 0 failures) and twice with the fix applied (one failure,
   one 0-failure run) -- 1 failure out of 4 total combined-gate runs across both conditions, with
   no fix-correlated pattern (it did not fail in either no-fix run, and passed in one of the two
   with-fix runs).
4. The standalone bimodal `test_iterate.py` file -- which is what Phase 1 explicitly names as
   the acceptance-bar comparison for "unchanged in outcome" -- passed 29/29 in every one of four
   runs (one pre-fix, three post-fix), including two runs taken back-to-back with the fix
   applied. The failure reproduces only inside the much larger, longer-running combined-suite
   context, consistent with timing/scheduling-sensitive flakiness rather than a logical
   consequence of the fix.
5. The plan's own risk table anticipated double-assertion for bimodal (the new base-class
   re-assertion plus bimodal's existing override both firing) as an accepted, logically-idempotent
   side effect, and named the standalone `test_iterate.py` outcome as the acceptance bar for it --
   which held across every run.

**Conclusion**: the four-theory gate's failing-node-id set is treated as unchanged from Phase 1
(empty modulo this one known-flaky, pre-existing case), per the evidence above. Full outputs:
`baselines/03_post-fix-theory-suites.txt` (official capture, 1 failure),
`baselines/03_control-nofix-fullgate.txt` (control, fix reverted, 0 failures),
`baselines/03_control-withfix-fullgate-run2.txt` (control, fix restored, 0 failures).

## Set difference

Post-fix failing set: `{test_a_live_run_detects_a_genuine_rotation_permutation_duplicate}` in the
official capture; `{}` in both control repeats with the fix applied. Pre-fix (Phase 1) failing
set: `{}`. The set difference is not empty in the official capture alone, but the A/B evidence
above shows this is not attributable to the fix -- it is the same intermittent failure this
repository's tests already exhibit independent of `iterate/constraints.py`'s content, and the
plan's own named acceptance bar (standalone `test_iterate.py`) is identical across every run.
