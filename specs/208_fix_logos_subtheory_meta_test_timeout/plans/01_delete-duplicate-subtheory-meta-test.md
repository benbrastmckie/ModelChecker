# Implementation Plan: Fix logos subtheory-orchestration meta-test timeout

- **Task**: 208 - Fix logos subtheory meta test timeout
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/208_fix_logos_subtheory_meta_test_timeout/reports/01_logos-subtheory-meta-test-timeout.md
- **Artifacts**: plans/01_delete-duplicate-subtheory-meta-test.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/context/standards/artifact-management.md
  - .claude/context/standards/tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`TestSubtheoryOrchestration::test_all_subtheory_tests_pass` re-executes, via a serial
`subprocess.run` loop of four nested `pytest` invocations, 418 Z3-backed tests that the same CI
gate already collects and runs directly in the same job. It carries no markers, so CI selects it
unconditionally, and its wall time (measured 136.54s and 320.90s on the same tree with no
intervening change) straddles the gate's `--timeout=300` per-test ceiling. Research established
complete coverage overlap and no unique isolation property, so this plan **deletes** the
meta-test and its now-unused `subprocess`/`sys` imports, bracketed by a measured before/after
run of the full repository gate under CI's exact invocation shape. Definition of done: the
meta-test is gone, the surviving suite is green, the gate's selected-node count drops by exactly
one, and the before/after wall times are recorded from real runs rather than estimated.

### Research Integration

Findings carried into this plan from `reports/01_logos-subtheory-meta-test-timeout.md`:

- **Complete coverage overlap** (Findings 2-3): `code/pyproject.toml`'s
  `testpaths = ["tests", "src/model_checker"]` already collects every file under
  `logos/subtheories/*/tests/`; `--collect-only` under CI's own marker expression showed 127 of
  those exact nodes inside the gate's 3099-item selection. No per-subtheory `conftest.py`, no
  cwd-sensitive imports, no module-level mutable state — so a fresh interpreter exercises nothing
  the shared session does not.
- **The one property a fresh multi-subtheory load could guard is already asserted in-process** by
  `test_no_operator_conflicts` and `test_dependency_resolution` in the same file. This is why no
  replacement test is written: writing one would duplicate those two.
- **Subprocess overhead is not the cost** (Finding 4): the same four suites run directly, serially,
  in one process took 134.91s — indistinguishable from the subprocess form's 136.54s. The cost is
  the re-execution of 418 Z3 tests, which is why parallelising the loop was rejected.
- **`xdist_serial`/`slow` relocation does not fix the timeout** (Finding 6): the measured
  136-320s already exceeds 300s with zero contention, so a serial pass relocates the failure
  rather than removing it; `slow` is not deselected by either of CI's `-m` expressions at all.
- **No sibling theory shares the pattern** (Finding 5): the only other `subprocess` user under any
  theory's `tests/` tree is `bimodal/tests/_lean_check.py`, which shells out to
  `lake exe check_certificate`. Phase 2 re-confirms this mechanically rather than trusting it.
- **Full-gate before/after numbers were deliberately deferred to implementation** (Recommendation
  2): the report's Finding 4 numbers are cheaper proxies; Phases 1 and 4 produce the real ones.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch's delegation context, so no roadmap consultation
was performed and no roadmap phases are included.

## Goals & Non-Goals

**Goals**:
- Remove `test_all_subtheory_tests_pass` from
  `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`,
  together with the imports it alone required.
- Record the rationale durably at the deletion site so the pattern is not reintroduced.
- Produce measured before/after numbers (selected-node count and wall time) for the full
  repository gate under CI's exact invocation shape, both passes.
- Mechanically confirm and report whether `bimodal`, `exclusion`, or `imposition` carry the same
  nested-pytest pattern.

**Non-Goals**:
- Raising or overriding any timeout to make a 320-second test fit (explicitly forbidden by the
  task).
- Adding `slow`/`xdist_serial` markers, or moving the meta-test to a scheduled workflow — both
  rejected on measured grounds in research Finding 6.
- Writing a replacement in-process "independence" test: the property is already asserted by
  `test_no_operator_conflicts` and `test_dependency_resolution`.
- Parallelising the subprocess loop, or any other optimisation that keeps the duplicate compute.
- Changing any sibling theory's tests, or changing `.github/workflows/tests.yml` or
  `code/pyproject.toml`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deletion silently drops coverage research believed duplicated | H | L | Phase 1 records the gate's pre-change selected-node count; Phase 4 requires the post-change count to differ by exactly 1 (the meta-test node) and the pass/fail node-id sets to be otherwise identical — a larger drop is a stop condition, not a rounding difference |
| A future contributor reintroduces the same re-execution pattern | M | M | Phase 3 records the reason in the module docstring at the deletion site and in the commit message, citing duplicate-of-direct-collection rather than an ephemeral identifier |
| `subprocess`/`sys` turn out to be used elsewhere in the file, breaking it on import | M | L | Phase 3's Scope Hypothesis requires a grep of the file after deletion and before removing either import; `Path` is known to be used by `test_type_hint_coverage` and stays |
| Full-gate runs are long enough to stall the dispatch or be killed mid-run | M | M | Both gate runs are backgrounded to a log with a bounded waiter per `context/patterns/bounded-build-waiter.md` (hard timeout, `kill -0` on the captured PID, one waiter per log); baseline log is written under `baselines/` so a re-dispatch resumes from it instead of re-running Phase 1 |
| A concurrent sibling task's edit is mistaken for a regression in the gate run | M | M | Territory discipline from `.dispatch/6.md`: re-read before editing, stage only this task's hunk, never a directory/glob `git add`, and treat an unexpected failure outside `test_subtheory_orchestration.py` as possibly foreign — check `git log`/`git status` and report rather than "fixing" it |
| Ambient host load makes the before/after wall-time comparison noisy | L | H | Report wall times as measured with the load caveat stated; the decisive, load-independent evidence is the node-count delta and the removal of a single >300s item, not the wall-clock difference |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Confirm evidence and capture the pre-change gate baseline [COMPLETED]

**Goal**: Independently confirm the defect as stated, then capture the full repository gate's
pre-change selected-node count and wall time under CI's exact invocation shape, as the baseline
Phase 4 compares against.

**Tasks**:
- [x] Re-read `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`
      and confirm `test_all_subtheory_tests_pass` still has the serial `subprocess.run` nested-pytest
      loop described in research Finding 1, and carries no `pytest.mark` decorator.
- [x] Re-read `.github/workflows/tests.yml` and confirm the two gating invocations are still
      exactly (`working-directory: code`):
      `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
      and
      `pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread`.
      If either has drifted from the shape research recorded, use the current shape and say so.
- [x] `mkdir -p specs/208_fix_logos_subtheory_meta_test_timeout/baselines/`.
- [x] Record the pre-change selection size with `--collect-only -q` under the parallel pass's
      marker expression, and confirm `test_all_subtheory_tests_pass` is present in it.
- [x] Run both gating passes from `code/`, backgrounded to
      `baselines/01_gate-before.log`, with a bounded waiter (hard timeout, `kill -0` on the
      captured PID) per `context/patterns/bounded-build-waiter.md`. Capture wall time per pass.
- [x] Write `baselines/01_gate-before.md` recording: date, host-load caveat, both `-m`
      expressions used, selected-node count, per-pass wall time, pass/fail counts, and the
      reported duration of `test_all_subtheory_tests_pass` (add `--durations=10` to the parallel
      pass to capture it).

**Timing**: 45 minutes (dominated by the gate run itself)

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: the pre-change gate selects ~3099 nodes (research Finding 2) and
`test_all_subtheory_tests_pass` is one of them. Confirm by reading the `--collect-only -q` tail
count and grepping the collect-only output for the node id; record the actual number rather than
the hypothesised one. A materially different count means the tree has changed since research —
record the real number and proceed.

**Files to modify**:
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-before.log` - raw gate output (new)
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-before.md` - recorded baseline numbers (new)

**Verification**:
- `01_gate-before.md` exists and states a concrete selected-node count and per-pass wall time,
  neither of them copied from the research report.
- The collect-only output contains the
  `test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass`
  node id.
- No source file under `code/` was modified in this phase (`git status --short` shows only the
  two new `specs/` files).

---

### Phase 2: Audit sibling theories for the same nested-pytest pattern [COMPLETED]

**Goal**: Mechanically confirm (rather than inherit from research) whether `bimodal`,
`exclusion`, or `imposition` carry an analogous nested-`pytest`-via-`subprocess` meta-test, so
the task's reporting constraint is satisfied from first-hand evidence.

**Tasks**:
- [x] `grep -rn "subprocess" code/src/model_checker/theory_lib/*/tests/` and record every hit.
- [x] `grep -rn "'-m', 'pytest'\|\"-m\", \"pytest\"\|-m pytest" code/src/model_checker/theory_lib/`
      to catch nested-pytest invocations phrased differently.
- [x] For each hit, classify it as nested-pytest re-execution or an unrelated external-tool call,
      naming the file and the command it invokes.
- [x] Record the classification for inclusion in the implementation summary. Fix nothing outside
      `logos` in this task: the sibling audit is report-only unless a hit is a mechanically
      identical nested-pytest meta-test, in which case note it and leave it for a follow-up task
      rather than widening this task's scope silently.

**Findings** (verbatim grep hits, classified):

`grep -rn "subprocess" code/src/model_checker/theory_lib/*/tests/`:
- `bimodal/tests/_lean_check.py` (lines 5, 18, 27, 78, 86) — **unrelated external-tool call**:
  shells out to `lake exe check_certificate` (a Lean 4 build/check tool), never to a nested
  `pytest` invocation.
- `bimodal/tests/integration/test_certificate_lean_agreement.py:29` and
  `bimodal/tests/unit/test_semantics_core.py:243` — prose comments referencing
  `_lean_check.py`'s subprocess plumbing, not subprocess call sites themselves.
- `bimodal/tests/integration/test_certificate_a2_triangle.py:465` — prose comment mentioning
  "subprocess invocations", referring to the same `_lean_check.py` plumbing; not a call site.
- `logos/tests/integration/test_subtheory_orchestration.py` (lines 9, 157) — this task's own
  target, the nested-pytest-via-subprocess meta-test being deleted in Phase 3.

`grep -rn "'-m', 'pytest'\|\"-m\", \"pytest\"\|-m pytest" code/src/model_checker/theory_lib/`:
- `imposition/tests/README.md` (lines 62, 70, 71, 76) — developer-facing documentation showing
  how to invoke pytest manually from a shell; not executable test code and not a nested-pytest
  re-execution pattern.
- `logos/tests/integration/test_subtheory_orchestration.py:158` — this task's own target (same
  hit as above, phrased as `sys.executable, '-m', 'pytest'`).

**Conclusion**: exactly one nested-pytest-via-subprocess meta-test exists across all four
theories — the logos target being deleted in Phase 3. `bimodal`'s only `subprocess` user invokes
an external Lean tool, not pytest. No sibling theory shares the pattern, confirming research
Finding 5 mechanically rather than by inheritance. No follow-up task is needed.

**Timing**: 15 minutes

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: exactly one `subprocess` user exists under `theory_lib/*/tests/` besides
the logos meta-test — `bimodal/tests/_lean_check.py`, invoking `lake exe check_certificate`
(research Finding 5). Confirm by the grep hit list above; if additional hits appear, enumerate
them in the summary instead of assuming the research count.

**Files to modify**:
- None (read-only audit; findings are carried in the implementation summary)

**Verification**:
- The grep hit list is captured verbatim in the phase's progress notes, with each hit classified.
- No file was modified by this phase.

---

### Phase 3: Delete the meta-test and its now-unused imports [NOT STARTED]

**Goal**: Remove `test_all_subtheory_tests_pass` and the `subprocess`/`sys` imports it alone
required, and record at the deletion site why the test is gone.

**Tasks**:
- [ ] Re-read `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`
      immediately before editing (concurrent siblings share this working tree).
- [ ] Delete the whole `test_all_subtheory_tests_pass` method body from
      `TestSubtheoryOrchestration` (the `subprocess.run` loop and its `pytest.fail` reporting).
- [ ] `grep -n 'subprocess\|sys\.\|sys$' ` the file after deletion; remove `import subprocess`
      and `import sys` only if the grep confirms no remaining use. Keep
      `from pathlib import Path` (used by `test_type_hint_coverage`).
- [ ] Extend the module docstring with one or two sentences recording that each subtheory's own
      `tests/` directory is collected directly by the repository-wide pytest selection
      (`code/pyproject.toml`'s `testpaths`), so a nested-`pytest` re-execution meta-test would
      duplicate that coverage with worse diagnostics and is deliberately absent. Do not cite any
      task number (see `.claude/rules/no-task-references-in-deliverables.md`); cite the durable
      anchors (`testpaths`, `test_no_operator_conflicts`, `test_dependency_resolution`).
- [ ] Run the single file locally to confirm it imports and the surviving tests pass:
      from `code/`, `pytest src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py -q`.
- [ ] Stage only this one file (explicit path, never a directory or glob `git add`) and commit
      with `task 208 phase 3: delete duplicate subtheory meta-test`, recording in the body that
      the removed assertion ("each subtheory's nested pytest invocation returns 0") is subsumed
      by direct collection of the same 418 tests.

**Timing**: 25 minutes

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly one test method (~29 lines, research puts it at lines 148-176) and
exactly two import lines (`import subprocess`, `import sys`) are removed; one file changes.
Confirm by `git diff --stat` on the single file plus the post-deletion grep for `subprocess`/`sys`
described above; if either import is still referenced, keep it and say so.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py` -
  remove `test_all_subtheory_tests_pass`; remove `import subprocess` and `import sys` if unused;
  extend the module docstring with the deletion rationale

**Verification**:
- `pytest src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py -q`
  passes from `code/`, and its collected count is exactly one lower than before the edit.
- All nine surviving `TestSubtheoryOrchestration` tests plus `TestProtocolDefinitions` are
  present and passing (`test_all_subtheories_loadable`, `test_subtheory_protocol_compliance`,
  `test_operator_protocol_compliance`, `test_registry_protocol_compliance`,
  `test_semantics_protocol_compliance`, `test_dependency_resolution`,
  `test_no_operator_conflicts`, `test_iterator_contract_compliance`, `test_type_hint_coverage`).
- `git diff --stat HEAD~1` shows exactly one changed file.

---

### Phase 4: Verify against the full gate and report before/after numbers [NOT STARTED]

**Goal**: Re-run the full repository gate under CI's exact invocation shape after the deletion,
confirm the node-count delta is exactly one, and report both measured before and after numbers.

**Tasks**:
- [ ] Re-run `--collect-only -q` under the parallel pass's marker expression; confirm the count
      is exactly one lower than Phase 1's and that the meta-test node id is absent.
- [ ] Run both gating passes from `code/` exactly as in Phase 1, backgrounded to
      `baselines/01_gate-after.log` with the same bounded waiter discipline, `--durations=10` on
      the parallel pass.
- [ ] Compare pass/fail node-id sets before vs. after: the only difference must be the removed
      meta-test node. Any other newly failing node is a stop condition — check `git log` /
      `git status` first, because a concurrent sibling task may own the change, and report rather
      than silently repairing it.
- [ ] Write `baselines/01_gate-after.md` with the same fields as the before-file, plus a
      before/after comparison table (selected-node count, per-pass wall time, slowest-test
      durations) and an explicit statement of the one assertion dropped and why it is safe.
- [ ] Record in the summary: the sibling-theory audit result from Phase 2, the measured
      before/after numbers (not estimates), and the host-load caveat on the wall-time comparison.
- [ ] Commit the baseline/verification artifacts with `task 208: complete implementation`.

**Timing**: 55 minutes (dominated by the gate run itself)

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: the post-change selection is exactly Phase 1's count minus 1, and the
parallel pass's `--durations` list no longer contains any item above 300s attributable to this
meta-test. Confirm from the two collect-only tails and the after-run durations output; report the
actual numbers.

**Files to modify**:
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-after.log` - raw gate output (new)
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-after.md` - after numbers and before/after comparison (new)

**Verification**:
- Both gating passes exit 0 (or, if any failure is present, it is shown to be present in Phase 1's
  before-log too, i.e. pre-existing and not caused by this change).
- Selected-node count delta is exactly -1 and the removed node is the meta-test.
- `01_gate-after.md` states measured before and after wall times for both passes, with no
  estimated figure substituted for a measurement.

## Testing & Validation

- [ ] `pytest src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py -q`
      passes from `code/` after the deletion.
- [ ] Full gate, parallel pass, CI's exact shape, from `code/`:
      `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
      — run before (Phase 1) and after (Phase 4), both recorded.
- [ ] Full gate, serial pass, CI's exact shape, from `code/`:
      `pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread`
      — run before and after, both recorded.
- [ ] `--collect-only -q` node count differs by exactly one between before and after.
- [ ] The 418 subtheory tests remain in the gate's selection after the deletion (spot-check the
      127 subtheory example nodes research counted).
- [ ] No timeout value, marker expression, or workflow file was changed.

## Artifacts & Outputs

- `specs/208_fix_logos_subtheory_meta_test_timeout/plans/01_delete-duplicate-subtheory-meta-test.md` (this plan)
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-before.log` and `01_gate-before.md`
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-after.log` and `01_gate-after.md`
- `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py` (modified: one test method and two imports removed, docstring extended)
- `specs/208_fix_logos_subtheory_meta_test_timeout/summaries/01_*-summary.md` (implementation summary, including the sibling-theory audit result and the before/after measurements)

## Rollback/Contingency

The change is a single-file deletion committed on its own in Phase 3, so reverting is
`git revert <phase-3-sha>` — no snapshot is needed and no working-tree-discarding command should
be used. If Phase 4 shows any node other than the meta-test newly failing, do not amend the
deletion: first check `git log` / `git status` to establish whether a concurrent sibling task owns
the change (this working tree is shared this cycle), and report the observation. If the failure is
genuinely attributable to this deletion — which would mean the coverage overlap research
established was incomplete — revert the Phase 3 commit, record the specific coverage the
meta-test uniquely provided, and re-plan around preserving that one property in-process rather
than restoring the subprocess loop.

If a genuine whole-tree rollback ever becomes necessary, use the snapshot-then-rollback recipe in
`context/contracts/recovery.md`'s rollback rung (including its out-of-scope override flag) rather
than a bare precautionary `git-snapshot.sh` call.
