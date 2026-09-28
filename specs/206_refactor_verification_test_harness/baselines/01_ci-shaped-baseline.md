# CI-Shaped Baseline: Bimodal Verification Test Harness

Records the before/after wall clocks for the two `slow`-marked boxed Tier 1 cases in
`code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`,
under CI's exact invocation shape, on the same host, per the implementation plan's Phase 1 and
Phase 6.

## Command (verbatim, from `code/`)

```
pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread --durations=25
```

Source: `.github/workflows/tests.yml`'s parallel-pass pytest line (confirmed byte-identical
apart from the added `--durations=25`, which changes nothing about what is executed). No
`PYTHONPATH` prefix was needed -- imports resolved via the installed editable package.

## Host

Hostname `hamsa`, 24 logical CPUs, Python 3.13.15 (pytest 9.0.3), Linux.

## Before (pre-refactor)

Two runs were taken. The first (18:45 local time) measured the tree **before** task 205's
commits landed (`3b8cb35c` onward); the second (below, authoritative) re-measured **after**
task 205 completed, since task 205 landed on this same working tree while this task's own
Phase 1 was still recording its baseline, and this plan's own risk table requires the baseline
be comparable to what Phase 6 will re-measure against. Both are recorded for transparency; the
second is the baseline this task's Phase 6 compares against, since it reflects the tree Phase 2
onward actually edits.

### Run 1 -- pre-task-205 tree (superseded, kept for the record)

- Total: 3107 items, 3106 passed, 1 skipped, 0 failed, wall clock 221.28s (0:03:41).
- Widest boxed case (`test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`): **125.48s**
  over 10,485,760 candidates.
- Second boxed case (`test_boxed_closure_enumeration_agrees_with_z3`): **18.35s** over
  1,572,864 candidates.
- Box-free widest case: not in the top-25 durations table (i.e. under the 25th-place cutoff of
  ~3.45s); consistent with the ~1.94s on record.

### Run 2 -- current tree, post-task-205 (authoritative baseline)

- Total: 3134 items (27 more than Run 1 -- task 205 added `test_checker.py` and
  `test_output_gate.py` plus two cases to `test_structure.py`), 3132 passed, 1 skipped,
  **1 failed**, wall clock 179.38s (0:02:59).
- **Failure**: `test_checker.py::TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call`
  -- a task-205 test outside this task's scope and outside the bimodal verification harness this
  task edits. Confirmed **not** a regression from anything in this task (no file this task
  touches was modified before this run) and **not** reproducible standalone: re-run in isolation
  (`pytest src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py::TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call
  -v --timeout=60`) passed in 0.60s. This is a `-n 4` worker-contention-sensitive timing
  assertion in a module this task does not touch -- reported here as an observed, pre-existing
  flake for the record, not something this task fixes (out of scope; the file belongs to a
  different task's territory).
- Widest boxed case (`test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`): **121.78s**
  over 10,485,760 candidates.
- Second boxed case (`test_boxed_closure_enumeration_agrees_with_z3`): **17.93s** over
  1,572,864 candidates.
- Box-free widest case: not in the top-25 durations table; confirmed directly via a standalone,
  non-`-n4` run of the module alone (`pytest .../test_certificate_a2_triangle.py --durations=0`,
  150.63s total, 9 passed): `box_free_until_conclusion_sat_nb2_nf2` took **1.82s** -- consistent
  with "well under 2s".

Both runs agree with the already-recorded numbers (123.29s / 17.77s) within the run-to-run
spread the research report itself observed (111.85-113.36s standalone vs. 123.29s CI-shaped, a
gap attributed to `-n 4` worker contention) -- Run 2's 121.78s and 17.93s are both *slightly
below* the recorded 123.29s / 17.77s (within ~1-1.5%), not a material divergence.

## Counts (Phase 5's explicit equality target)

From the two boxed cases' own pinned expectations, confirmed passing in Run 2:

- `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`: `total=10,485,760`,
  `accepted=5,115`, `pinned_accepted=5,115`.
- `test_boxed_closure_enumeration_agrees_with_z3`: `total=1,572,864`, `accepted=96`,
  `pinned_accepted=96`.

## Tier 2 (invariant 1)

`BIMODAL_LOGIC_PATH` is unset in this environment. Both runs show Tier 2's
`TestBoundedLeanCrossCheck` class executing (not class-level `skipif`-skipped, since
`_lean_check.py`'s `SKIP_REASON` mechanism is about the Lean binary's own availability probed
per test, not this class-level `skipif`) -- all three of its parametrized cases passed in both
runs, meaning a Lean checkout/binary **was** resolvable in this environment (not a clean skip in
this case; the module's 1 skipped item is elsewhere in the suite, unrelated to this module). This
is a valid alternative to a clean skip per `_lean_check.py`'s own discipline: Tier 2 either skips
cleanly or passes for real, never silently degrading. Recorded here as the observed environment
state, not assumed.

## Scope Hypothesis confirmation

The recorded 123.29s / 17.77s numbers already on file were confirmed to reproduce (both new
measurements land within ~1.5% below them), so Phase 1's Scope Hypothesis is confirmed: no
material divergence to flag.

## After (post-refactor, Phase 6)

Re-ran Phase 1's verbatim recorded command, same host, same shape, after Phases 2-5 landed
(`_recheck_family` extraction, the pinned evaluator's family-only/target-time split, and the
family-outer/target-inner harness restructure):

```
pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread --durations=25
```

- Total: 3145 items (11 more than Run 2 -- this task's own new equivalence/partition tests in
  Phases 3-4), 3143 passed, 1 skipped, **1 failed**, wall clock 105.69s (0:01:45) -- down from
  Run 2's 179.38s.
- **Failure**: the same pre-existing, out-of-scope `test_checker.py::TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call`
  flake recorded in the "Before" section above -- reproduces again here, confirming it is an
  environmental (`-n 4` contention) flake in a module this task does not touch, not a
  regression introduced by this task's changes.

### Before/After table (both numbers, per the dispatch's explicit requirement)

| Case | Candidates | Before (Run 2) | After (Phase 6) | Reduction | Multiplier |
|---|---|---|---|---|---|
| `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` (widest) | 10,485,760 | 121.78s | **33.90s** | 72.2% | 3.59x |
| `test_boxed_closure_enumeration_agrees_with_z3` | 1,572,864 | 17.93s | **7.14s** | 60.2% | 2.51x |

Both counts (`total`/`accepted`/`pinned_accepted`) are bit-for-bit identical to the recorded
baseline for both cases, confirmed by the tests' own unedited pinned assertions passing.

The widest case's standalone (non-`-n4`) measurement from Phase 5's own record was 29.56s;
33.90s under the real `-n 4` CI shape is consistent with the worker-contention gap already
observed between standalone and CI-shaped numbers throughout this record.

### Gate criterion and decision (Phase 6)

**Criterion** (as stated in the plan): is the post-fix margin adequate -- does the widest case's
measured CI-shaped wall clock leave headroom against the 300s ceiling that tolerates CI hardware
materially slower than this host, stated as a concrete ratio?

**Measured**: 33.90s against the 300s ceiling leaves **88.7% headroom** (`(300-33.90)/300`), a
**8.85x** CI-hardware slowdown tolerance (`300/33.90`) -- almost exactly the research report's
~88% / ~8x projection (F8/F10), and a large improvement over the pre-fix 59% / 2.4x margin this
task's Phase 1 baseline recorded.

**Decision: Adequate.** Phase 7 (the scheduled-run contingency) is **not taken**. Closed
`[COMPLETED WITH EXCLUSIONS]` with its own `#### Reasoned Exclusions` record citing this
measurement as Evidence.

### Recorded-measurement docstring updates (this phase)

`TestExhaustiveTriangleWithBox`'s class docstring and the module docstring's Tier 1 bullet, in
`code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`,
are updated in place to carry these numbers (33.90s / 7.14s, 88.7% headroom, 8.85x slowdown
tolerance) in the same commit as this baseline update, replacing the pre-refactor 123.29s /
17.77s / ~59% / ~2.4x figures. `TestExhaustiveTriangleBoxFree`'s docstring numbers did not move
materially (both box-free widest cases stayed well under 2s before and after) and are left as
recorded.
