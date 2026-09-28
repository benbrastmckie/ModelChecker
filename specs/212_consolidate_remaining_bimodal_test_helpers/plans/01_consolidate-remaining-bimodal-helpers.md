# Implementation Plan: Consolidate Remaining Bimodal Test Helpers

- **Task**: 212 - Consolidate remaining bimodal test helpers onto `_build_support.py`
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/212_consolidate_remaining_bimodal_test_helpers/reports/01_consolidate-remaining-bimodal-helpers.md
- **Artifacts**: plans/01_consolidate-remaining-bimodal-helpers.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/context/standards/artifact-management.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/no-task-references-in-deliverables.md
  - code/docs/core/TESTING_GUIDE.md
- **Type**: python
- **Lean Intent**: false

## Overview

The bimodal test tree has a shared example-build module,
`code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`, exporting `_settings` and
`_build`. Four call sites were folded onto it when it was introduced; the remainder still restate
the same helpers locally. This plan consolidates the genuinely duplicated call sites onto the
shared module, preserves the one documented behavioral exception, and leaves the one grep false
positive untouched. Done means: every duplicated `_settings`/`_build` body in the bimodal test
tree is replaced by an import of `_build_support`, no dead imports remain behind, every
non-equivalent helper that survives carries a written reason in its own module, and the full
four-theory gate is green.

### Research Integration

The research report re-ran the discovery grep and then read every matched helper body against
`_build_support.py`'s, rather than trusting the name match. That read splits the ten grep hits
into four groups, and this plan's phase structure follows that split directly:

- **Group A** (2 modules): full duplicates of *both* `_settings` and `_build`, each trailing six
  now-dead imports once the bodies go (`ModelConstraints`, `Syntax`, `bimodal_operators`,
  `BimodalSemantics`, `BimodalStructure`, `BimodalProposition`) — in these two modules
  `BimodalSemantics` is referenced *only* inside the doomed function bodies.
- **Group B** (5 modules): `_settings`-only duplicates with no local `_build`; `BimodalSemantics`
  is used elsewhere in each file, so only the `_settings` def is removable.
- **Group C** (1 module): `integration/test_injection.py`, whose `_build_solved` is behaviorally
  identical to the shared `_build` under a different local name at 3 call sites.
- **Non-candidates** (2 modules): `unit/test_structure.py` (dispatch-excluded documented
  `'verify'='off'` wrapper) and `unit/test_witness_constraints.py` (a grep false positive —
  `_build_selector_family` shares nothing with `_build_support`'s shape).

The report also flagged two traps this plan carries forward explicitly: `test_output_gate.py`'s
docstring *claims* to mirror `test_structure.py`'s `'verify'` wrapper but its body has no such
override (the docstring is stale, the code is a plain duplicate), and
`test_iterate.py`'s `_mock_build_example`/`_real_build_example` are Mock/`BuildExample` test
doubles that must not be touched.

### Prior Plan Reference

No prior plan for this task. The precedent task that introduced `_build_support.py`
(`specs/206_refactor_verification_test_harness/plans/01_refactor-verification-test-harness.md`,
Phase 2) established both the shared-helper shape and the documented-local-wrapper escape hatch
this plan reuses; its scoping note deliberately deferred the remaining call sites to this task.

### Roadmap Alignment

No `roadmap_path` was provided in the dispatch context; no ROADMAP.md was consulted or modified.

## Goals & Non-Goals

**Goals**:
- Replace every genuinely duplicated `_settings`/`_build` body in the bimodal test tree with an
  import from `tests/_build_support.py`.
- Remove the import fallout each removal leaves behind, so no module carries a dead import.
- Keep, and document in-module, any helper that is *not* equivalent to the shared one.
- Refresh `_build_support.py`'s own module docstring, which currently enumerates the original
  four call sites and will be stale once this consolidation lands.
- Verify with the full four-theory gate, not the bimodal subset.

**Non-Goals**:
- Touching `unit/test_structure.py`'s documented `'verify'='off'` wrapper.
- Touching `unit/test_witness_constraints.py` (`_build_selector_family` is unrelated).
- Touching `test_iterate.py`'s `_mock_build_example`/`_real_build_example` or
  `test_until_since_integration.py`'s `_run` — different helpers that merely live nearby.
- Consolidating any other duplication in this tree (grid tables, fixture bodies, assertion
  helpers). The mandate is `_settings`/`_build` only.
- Changing any test's assertions, expected values, or runtime behavior. This is a pure
  de-duplication; a behavioral change is a signal that the helper was NOT equivalent.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A helper assumed equivalent is not (e.g. a differing default), silently changing test behavior | H | M | Phase 1 re-reads each body against `_build_support.py`'s before any edit; any divergence found routes to the documented-local-wrapper pattern (Phase 1 task list), never to silent normalization |
| `test_output_gate.py`'s stale docstring is believed over its body, so a `'verify'` default is invented that was never there | H | M | Phase 3 explicitly verifies every `_build(...)` call site in that module passes `verify=` explicitly before dropping the local def; the stale docstring is deleted with the body |
| Dead imports left behind after a body is removed, failing a lint/vulture pass | M | M | Phase 3 re-derives the unused set per module with grep after the edit, rather than trusting the report's enumeration |
| Removing an import that IS still used elsewhere in the same module (Group B's `BimodalSemantics`) | M | M | Per-module grep for each candidate symbol *after* the removal, counting surviving references, before deleting any import line |
| A rename in `test_injection.py` misses a call site | M | L | Phase 4 greps for the old name post-edit and requires zero hits |
| Bimodal subset passes but a cross-theory regression slips through | M | L | Phase 5 runs the full four-theory gate per the dispatch, not the bimodal directory alone |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel — Phases 2, 3, and 4 touch disjoint file
sets (5 modules / 2 modules / 1 module respectively) with no shared edit surface.

---

### Phase 1: Re-derive Scope and Confirm Helper Equivalence [COMPLETED]

**Goal**: Establish, by reading rather than by name match, exactly which modules carry a
consolidatable helper in the tree as it stands right now — and record a pre-change baseline.

**Tasks**:
- [x] Re-run the discovery grep fresh:
      `grep -rln '^def _settings\|^def _build' code/src/model_checker/theory_lib/bimodal/tests/`,
      excluding `_build_support.py` itself. Record the resulting module list. Do not assume it
      matches this plan's list — concurrent work in this tree changes the set.
- [x] Read `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` in full: the
      `_settings` and `_build` bodies plus the module docstring.
- [x] For each module the grep names, read the matched function body in full and compare it
      against `_build_support.py`'s. Classify each as: full duplicate (both helpers),
      `_settings`-only duplicate, same-shape-different-name, documented exception, or
      false positive. Record the classification and the reason.
- [x] For any module NOT in this plan's expected set, or whose classification differs from this
      plan's, note the divergence explicitly and handle it under the rule below rather than
      forcing it into a phase it does not fit.
- [x] **Divergence rule**: a helper that is genuinely not equivalent to the shared one keeps a
      documented local wrapper that *delegates* to `_build_support` (the
      `unit/test_structure.py` pattern), with the reason for the difference written in the
      module. Never force a non-equivalent module onto the shared form, and never leave a full
      duplicate in place unexplained.
- [x] Record the pre-change collection baseline:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q`
      and note the collected test count and clean-import status.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This plan asserts the grep names ten modules, of which eight are
consolidation candidates (2 full duplicates, 5 `_settings`-only, 1 same-shape-different-name) and
two are not (`unit/test_structure.py`, `unit/test_witness_constraints.py`). Confirm by running
the grep fresh and reading each body; if the candidate set differs, update the phase task lists
below to match what the tree actually contains before editing anything.

**Files to modify**: none (read-only phase)

**Verification**:
- The fresh grep output is recorded, and each named module carries a written classification with
  a reason grounded in its actual body, not its function name.
- The `--collect-only` baseline runs clean with a recorded test count.

---

**Confirmation (re-run at implementation time)**: fresh grep matches this plan's ten-module list
exactly, with no additions or removals. Every module's helper body was read against
`_build_support.py`'s and matches this plan's classification with no divergence: Group A (full
duplicate of both `_settings`/`_build`) = `integration/test_data_extraction.py`,
`integration/test_output_gate.py` (8 `_build(...)` call sites, all passing `verify=` explicitly
-- the docstring claiming a `'verify'='off'` mirror of `test_structure.py` is confirmed stale,
the body applies no such override); Group B (`_settings`-only duplicate, byte-identical to
`_build_support._settings`) = `integration/test_iterate.py`,
`integration/test_until_since_integration.py`, `unit/test_operators.py`,
`unit/test_proposition.py`, `unit/test_semantics_core.py`; Group C (same-shape,
differently-named) = `integration/test_injection.py`'s `_build_solved` (3 call sites,
behaviorally identical to the shared `_build`, `BimodalSemantics` used elsewhere in the module at
`BimodalSemantics(_settings())`); non-candidates = `unit/test_structure.py` (documented
`'verify'='off'` wrapper delegating to `_build_support._build`, left untouched) and
`unit/test_witness_constraints.py` (`_build_selector_family` -- confirmed grep false positive,
unrelated shape). Pre-change baseline: `--collect-only` reports 686 tests collected, clean
import, no collection errors.

### Phase 2: Consolidate `_settings`-Only Duplicates [COMPLETED]

**Goal**: Remove the five local `_settings` duplicates that have no local `_build`, replacing
each with an import from `_build_support`.

**Tasks**:
- [x] For each module in the Group B set confirmed by Phase 1, delete the local `def _settings`
      body and add
      `from model_checker.theory_lib.bimodal.tests._build_support import _settings`
      to the module's import block, placed with the other
      `model_checker.theory_lib.bimodal.tests.*` imports and respecting the project's import
      ordering convention (stdlib, third-party, local).
- [x] After each removal, grep the module for every symbol the deleted body referenced
      (`BimodalSemantics` in particular) and count surviving references. Delete an import line
      only when the count drops to zero. In this group `BimodalSemantics` is expected to remain
      in use elsewhere in every module — verify rather than assume.
- [x] Leave `test_iterate.py`'s `_mock_build_example` and `_real_build_example` untouched.
- [x] Leave `test_until_since_integration.py`'s `_run` untouched (it targets the `run_test()`
      API, not the `Syntax -> ModelConstraints -> BimodalStructure` pipeline).
- [x] Run the five modules' tests:
      `PYTHONPATH=code/src pytest <the five module paths> -q` and confirm green.
- [x] Commit at each green sub-step per `.claude/rules/git-workflow.md`.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Five modules are expected in this group —
`integration/test_iterate.py`, `integration/test_until_since_integration.py`,
`unit/test_operators.py`, `unit/test_proposition.py`, `unit/test_semantics_core.py` — each
losing exactly one `_settings` def and no import lines. Confirm against Phase 1's fresh
classification; confirm the "no import lines removed" half with a per-module post-edit grep, not
by assumption.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - drop local `_settings`, import it
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_until_since_integration.py` - drop local `_settings`, import it
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators.py` - drop local `_settings`, import it
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` - drop local `_settings`, import it
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - drop local `_settings`, import it

**Verification**:
- No `^def _settings` remains in any of the five modules.
- Each of the five imports `_settings` from `_build_support`.
- Per-module grep confirms every surviving import is still referenced.
- The five modules' tests pass, with the same test counts as the Phase 1 baseline for those files.

---

**Confirmation (re-run at implementation time)**: all five Group B modules lost exactly one
`_settings` def and zero import lines. Per-module post-edit grep confirms `BimodalSemantics`
remains referenced outside the removed body in every module (28, 3, 13, 13, and 22 remaining
occurrences respectively across `test_iterate.py`, `test_until_since_integration.py`,
`test_operators.py`, `test_proposition.py`, `test_semantics_core.py`), so the import line was
kept in all five, exactly as the Scope Hypothesis predicted. `test_iterate.py`'s
`_mock_build_example`/`_real_build_example` and `test_until_since_integration.py`'s `_run` were
left untouched. `PYTHONPATH=code/src pytest <five modules> -q`: 76 passed, 0 failed.

### Phase 3: Consolidate Full Duplicates and Their Import Fallout [COMPLETED]

**Goal**: Remove both `_settings` and `_build` from the two modules that duplicate the whole
pipeline, and delete every import the removal orphans.

**Tasks**:
- [x] Before editing `integration/test_output_gate.py`, enumerate every `_build(...)` call site
      in it and confirm each passes `verify=` explicitly. The module's local `_build` docstring
      claims to mirror `unit/test_structure.py`'s `'verify'='off'` wrapper, but the body applies
      no such override — the docstring is stale. If any call site turns out to rely on an
      implicit `'verify'` value, STOP and route the module to the documented-local-wrapper
      pattern instead of a bare import.
- [x] For `integration/test_data_extraction.py`, confirm no test in the module inspects
      verification output or labels (the report found it reads `structure.certificate`,
      `extract_states()`, and similar, all unaffected by `'verify'`).
- [x] In each of the two modules: delete the local `def _settings` and `def _build` bodies
      (including the stale `test_output_gate.py` docstring) and add
      `from model_checker.theory_lib.bimodal.tests._build_support import _build, _settings`.
- [x] Re-derive the dead-import set per module *after* the deletion: for each of
      `ModelConstraints`, `Syntax`, `bimodal_operators`, `BimodalSemantics`, `BimodalStructure`,
      `BimodalProposition`, grep the edited module and delete the import line only when zero
      references survive. Do not delete on the strength of this plan's enumeration alone.
- [x] Preserve every other import in `test_output_gate.py` (`sys`, `pytest`, `checker_module`,
      `SKIP_REASON`, `ModelConstructionError`) — they are unrelated to the removed bodies.
- [x] Run the two modules' tests and confirm green.
- [x] Commit at each green sub-step.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Two modules are expected in this group
(`integration/test_data_extraction.py`, `integration/test_output_gate.py`), each losing two
function defs plus six import lines, and `test_output_gate.py` is expected to have 8 `_build(...)`
call sites all passing `verify=` explicitly. Confirm the call-site count and the explicit-`verify`
property by grep before editing, and the six-import figure by post-edit reference counting.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py` - drop local `_settings` + `_build` and the orphaned imports; import from `_build_support`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` - same, plus deletion of the stale `_build` docstring

**Verification**:
- Neither module defines `_settings` or `_build` locally; both import them from `_build_support`.
- Grep confirms no orphaned import remains, and no still-referenced import was deleted.
- Both modules' tests pass with unchanged test counts, including `test_output_gate.py`'s
  `"auto"`/`"off"`/`"required"`/`"paranoid"` cases.

---

**Confirmation (re-run at implementation time)**: `test_output_gate.py` has exactly 8
`_build(...)` call sites, all passing `verify=` explicitly (`"auto"`/`"off"`/`"required"`
(x2)/`"paranoid"`/`"auto"`/`"required"`) -- no implicit-default reliance, so the bare-import
route (not the documented-wrapper route) applies. `test_data_extraction.py` has zero `verify`
references anywhere in the module. Both modules lost their local `_settings`+`_build` defs (and,
in `test_output_gate.py`'s case, the stale mirror-claim docstring) and now import both from
`_build_support`. Post-edit grep confirms all six symbols
(`ModelConstraints`/`Syntax`/`bimodal_operators`/`BimodalSemantics`/`BimodalStructure`/
`BimodalProposition`) have zero surviving references in either module, so all six import lines
were removed from each -- matching the Scope Hypothesis's six-import figure exactly.
`test_output_gate.py` retains `sys`, `pytest`, `checker_module`, `SKIP_REASON`,
`ModelConstructionError` untouched. `PYTHONPATH=code/src pytest <two modules> -q`: 16 passed, 0
failed (9 in `test_data_extraction.py`, 7 in `test_output_gate.py`, matching the Phase 1 baseline
for these files).

### Phase 4: Collapse `test_injection.py`'s Differently-Named Duplicate [COMPLETED]

**Goal**: Replace `integration/test_injection.py`'s `_settings` and `_build_solved` with the
shared helpers, adopting the naming convention the already-migrated call sites use.

**Tasks**:
- [x] Confirm `_build_solved`'s body is the same three-line
      `Syntax -> ModelConstraints -> BimodalStructure` pipeline as `_build_support._build`, with
      no `'verify'` override and no other divergence. If a real difference surfaces, keep a
      documented local wrapper delegating to `_build` instead of completing the rename.
- [x] Delete the local `_settings` and `_build_solved` defs; add
      `from model_checker.theory_lib.bimodal.tests._build_support import _build, _settings`.
- [x] Rename every `_build_solved(...)` call site to `_build(...)` (approach (a) from the
      research report — it matches the convention every already-migrated call site uses). The
      import-alias fallback (`import _build as _build_solved`) is acceptable only if a call-site
      rename proves disruptive; record the reason if taken.
- [x] Grep the module for `_build_solved` and require zero hits.
- [x] Re-derive the dead-import set as in Phase 3. `BimodalSemantics` is expected to survive —
      it is used at a call site outside the removed bodies (`BimodalSemantics(_settings())`) —
      so verify its reference count rather than deleting it by analogy with Phase 3.
- [x] Run the module's tests and confirm green; commit.

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: `_build_solved` is expected to have exactly 3 call sites in this module,
and `BimodalSemantics` is expected to survive the import cleanup while
`ModelConstraints`/`Syntax`/`bimodal_operators`/`BimodalStructure`/`BimodalProposition` do not.
Confirm both by grep before and after the edit.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` - drop local `_settings` + `_build_solved`, import the shared pair, rename call sites, prune orphaned imports

**Verification**:
- Zero occurrences of `_build_solved` remain in the module.
- The module imports `_build` and `_settings` from `_build_support`.
- `BimodalSemantics` remains imported and referenced; no orphaned import survives.
- The module's tests pass with an unchanged test count.

---

**Confirmation (re-run at implementation time)**: `_build_solved`'s body was byte-equivalent in
shape to `_build_support._build` (same three-line pipeline, only differing by an intermediate
`structure = ...; return structure` versus a direct return -- functionally identical, no
`'verify'` override), so the bare rename route applied rather than a documented wrapper. Exactly
3 `_build_solved(...)` call sites were found and renamed to `_build(...)`; a post-edit grep
confirms zero remaining `_build_solved` occurrences. Post-edit reference counts:
`ModelConstraints`/`Syntax`/`bimodal_operators`/`BimodalStructure`/`BimodalProposition` all
dropped to zero references (all five import lines removed), while `BimodalSemantics` survived at
its `BimodalSemantics(_settings())` call site outside the removed body (kept, imported directly
from `semantic.core` since the module doesn't otherwise need `_build_support` to re-export it).
`PYTHONPATH=code/src pytest integration/test_injection.py -q`: 4 passed, 0 failed (unchanged from
the Phase 1 baseline for this file).

### Phase 5: Refresh `_build_support.py` Docstring and Run the Full Four-Theory Gate [NOT STARTED]

**Goal**: Bring the shared module's own documentation in line with the consolidated call-site
set, and verify the whole change against the full gate rather than the bimodal subset.

**Tasks**:
- [ ] Update `_build_support.py`'s module docstring. It currently enumerates the original four
      migrated call sites and says "The other three call sites have no such requirement" — both
      statements go stale with this change. Rewrite it to describe the consolidated set in
      durable terms and keep the documented exception explicit: `unit/test_structure.py` retains
      a local wrapper defaulting `'verify'` to `'off'` for output-gate determinism. Mention
      `unit/test_witness_constraints.py` only if useful as a "not a call site" note — it has no
      relationship to this module. Do **not** cite task numbers in the docstring
      (`.claude/rules/no-task-references-in-deliverables.md`); reference filenames and behavior.
- [ ] Re-run the discovery grep one final time and confirm the only surviving
      `^def _settings`/`^def _build` hits outside `_build_support.py` are the two known
      non-candidates (`unit/test_structure.py`'s documented wrapper,
      `unit/test_witness_constraints.py`'s unrelated `_build_selector_family`) plus any module
      Phase 1 classified as a genuine documented exception.
- [ ] Re-run the collection check:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q`
      and confirm the count matches the Phase 1 baseline exactly — a changed count means a test
      was lost or duplicated by the edits.
- [ ] Run the full four-theory gate: `PYTHONPATH=code/src pytest code/tests/ -v` plus the
      per-theory unit suites for logos, exclusion, imposition, and bimodal per
      `code/docs/core/TESTING_GUIDE.md` and the project CLAUDE.md commands. If the gate is slow,
      background it and wait under `context/patterns/bounded-build-waiter.md` (hard timeout,
      writer liveness via `kill -0` on the captured PID, one waiter per log).
- [ ] Confirm the gate is green with no new failures relative to the pre-change state. Any
      failure is a signal that a consolidated helper was not equivalent — route it back to the
      documented-local-wrapper pattern rather than patching the shared helper.
- [ ] Commit the docstring update and record the gate result.

**Timing**: 0.5 hours

**Depends on**: 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The post-change bimodal collection count is expected to equal the Phase 1
baseline exactly (the report recorded 686 pre-change, but the baseline to compare against is
Phase 1's own fresh measurement, not that figure). Confirm by re-running `--collect-only` and
diffing the count against the recorded baseline.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` - docstring only; `_settings`/`_build` bodies unchanged

**Verification**:
- The docstring accurately describes the consolidated call-site set and the surviving exception,
  with no task-number citations.
- The final discovery grep surfaces only the known, reasoned non-candidates.
- Bimodal collection count matches the Phase 1 baseline.
- The full four-theory gate is green.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q` — count unchanged from the Phase 1 baseline.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` — green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — full four-theory gate green (the dispatch's explicit requirement; the bimodal subset alone is not sufficient).
- [ ] Per-theory unit suites for logos, exclusion, imposition, and bimodal per `code/docs/core/TESTING_GUIDE.md`.
- [ ] `grep -rn '^def _settings\|^def _build' code/src/model_checker/theory_lib/bimodal/tests/` — only `_build_support.py` plus the reasoned exceptions.
- [ ] No module carries an import that nothing references (per-module grep after each removal).
- [ ] No test assertion, expected value, or `'verify'` default was changed anywhere.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_until_since_integration.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` (docstring refreshed)
- `specs/212_consolidate_remaining_bimodal_test_helpers/summaries/01_*-summary.md` (implementation summary)

## Rollback/Contingency

Each phase commits at green sub-steps, so the cheapest rollback is `git revert` of the offending
commit(s) — the edits are import-level and independent per module, so reverting one module's
commit never destabilizes another's.

If a consolidated helper turns out not to be equivalent (a test flips, or a `'verify'`-dependent
assertion changes), do **not** revert the whole task: restore that one module to a documented
local wrapper that delegates to `_build_support`, following `unit/test_structure.py`'s pattern,
and record the behavioral difference in the module. That is the intended landing place for a
non-equivalent helper, not an abandonment condition.

If uncommitted work must be discarded wholesale, take a snapshot first per
`.claude/context/contracts/recovery.md`'s rollback rung — including its out-of-scope override
flag for the deliberate whole-tree case — before running any destructive git command. Do not
emit a bare precautionary `git-snapshot.sh` at the start of a phase; a defensive checkpoint
before risky work uses `--no-revert`.
