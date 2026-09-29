# Implementation Plan: Bimodal Theory-Limits Example Group

- **Task**: 219 - Add a documented THEORY-LIMITS example group to bimodal's examples.py
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (tasks 216 and 217 are concurrent siblings this cycle with undeclared
  file scope; neither is known to touch `code/src/model_checker/theory_lib/bimodal/examples.py`)
- **Research Inputs**: specs/219_bimodal_theory_limits_example_group/reports/01_theory-limits-example-group.md
- **Artifacts**: plans/01_theory-limits-example-group.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Add a new `THEORY-LIMITS` section to `code/src/model_checker/theory_lib/bimodal/examples.py`
whose purpose is to record outcomes that are permanent limits of this theory or of its verified
BimodalLogic counterpart, so they are learned from rather than rediscovered. The section carries
a header comment block stating the group's inclusion criterion and the full corrected account of
the stability-of-since result, plus two real, empirically verified countermodel entries
(`TL_CM_1`, `TL_CM_2`) wired as ordinary regression tests. The stability-modal schema itself is
recorded in prose only, since no `[stab]` operator exists here and adding one is the blocked
extension task's scope. Done means: the section exists with its commentary, both entries pass,
the full bimodal suite plus the four-theory gate are green, and no existing example changed.

### Research Integration

The research report verified every claim in the task description against both live trees and
settled the questions the task left open. Load-bearing findings this plan builds on:

- The two facts are confirmed and must stay visibly separate: the schema is a genuine ℤ-time
  non-validity (`not_plusValidZTime_stabSnce`), and the verified side's certificate class for it
  is provably empty (`not_plusCertifies_stabSnce`, `not_plusCertifies_stabSnce_premise`). The
  second is a completeness gap in a certificate design, not unsoundness and not a defect here.
- Not an axiom problem, checked against live constructor lists: `FormalSystem.Syntax.Formula` has
  exactly atom/bot/imp/box/untl/snce, `FormalSystem.ProofSystem.Axiom` is `Formula -> Type`, and
  `stab` exists only in `FormalSystem.PlusLanguage.PlusFormula`.
- The temporal-asymmetry diagnosis is confirmed superseded. The real mechanism is shape-based:
  a clause of the form "for all j accessible from i, phi holds at i iff a condition on j alone"
  is an invariance axiom derivable from reflexivity alone, and `snce_share_congr`'s entire proof
  is that two-instance chain. The share relation is an equality of representatives, hence an
  equivalence, so invariance runs across the whole class.
- **The Box-versus-stability question is answered, not assumed.** Both nearest-expressible
  probes were run against the live checker and are genuinely invalid here (20/20 runs each,
  under 150ms, stable at enlarged segment lengths). But they fail for a different and unrelated
  reason: `\Box`'s accessibility carries no same-state restriction, and the observed
  countermodels have the two histories disagreeing at the evaluation time itself, which a
  `[stab]`-style share-class would forbid by construction. Same verdict, unrelated mechanism.
- No existing operator is a stability modal, and no operator may be added by this task.
- Baseline is 53/53 on `tests/unit/test_bimodal.py`; both new entries take it to 55.
- `KNOWN_TIMEOUT_EXAMPLES` and `UNSTABLE_EXAMPLES` are both empty and need no new member.
- Citations must be by fully qualified declaration name only, with no `file:line` anchor, since
  BimodalLogic's citation manifest does not yet seed these five names.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation was requested for this dispatch.

## Goals & Non-Goals

**Goals**:
- A `THEORY-LIMITS` section in `examples.py` with a header block covering all six required
  points: the inclusion criterion; facts (1) and (2) kept visibly separate; that this is a limit
  of the verified counterpart's certificate system and not of this checker; the shape mechanism
  with the temporal-asymmetry story explicitly marked superseded; the semi-decision-procedure
  consequence; and the Box-versus-stability answer stated explicitly.
- Two entries, `TL_CM_1` (Since-form) and `TL_CM_2` (`\Past`-form), each with a per-example
  comment following the file's existing convention, wired into `countermodel_examples` and the
  active `example_range`.
- The stability-modal schema recorded in prose as pending, with nothing unchecked asserted.
- The top-of-file docstring's naming-convention list extended with `TL_CM_*`.
- Full test suite green; no existing example's premises, conclusions, or settings altered.

**Non-Goals**:
- Adding a stability-modal operator, or any operator, to `operators.py`. That is the blocked
  extension task's scope and this task must not pre-empt it.
- Editing anything in `/home/benjamin/Projects/BimodalLogic`, including its citation manifest.
- Creating any Python object, active or inactive, for the `[stab]`-form schema itself.
- Changing `test_bimodal.py`, `KNOWN_TIMEOUT_EXAMPLES`, or `UNSTABLE_EXAMPLES`.
- Weakening, reinterpreting, or recalibrating any existing example.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A reader conflates the Box-form countermodels with the `[stab]`-form certificate gap, treating the former as explaining the latter | H | M | The header's Box-versus-stability paragraph states "same verdict, unrelated mechanism" explicitly. It is the single most load-bearing paragraph and must not be trimmed or summarized during implementation. Phase 4 re-reads it against this bar. |
| The superseded temporal-asymmetry diagnosis is reintroduced, since it is already in circulation upstream | H | M | Phase 2 writes the shape-mechanism paragraph verbatim from the research report's draft, which names the diagnosis as refuted before stating the replacement. Phase 4 greps the new block for "asymmetry" to confirm it appears only inside the refutation framing. |
| Fully qualified Lean citations drift if BimodalLogic renames a declaration, with nothing on this side to catch it | M | L | Accepted, consistent with the task's cite-by-name instruction. Phase 1 confirms all five names resolve in the live tree at implementation time; a future BimodalLogic-side manifest seeding is flagged as out of scope. |
| A concurrent sibling task edits `examples.py` between read and write | M | L | Re-read the file immediately before each edit, stage only `examples.py` by explicit path, never a directory or glob add, and never run `git-snapshot.sh` in its reverting default mode. If a foreign commit or foreign uncommitted modification appears, stop and report after checking `git log`. |
| A task number or cross-repository task reference leaks into `code/` | M | L | The draft header text already avoids both. Phase 4 runs the repository's task-reference check over the changed file. |
| Adding entries to `example_range` slows the default CLI run | L | L | Both entries measured under 150ms; `max_time` is set to the file's 10s floor, matching every neighboring example. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: phases 2 and
3 edit the same file and phase 4 gates on both.

---

### Phase 1: Baseline, Citation, and Placement Confirmation [NOT STARTED]

**Goal**: Establish a clean pre-change baseline, re-confirm the research report's load-bearing
facts against the live trees at implementation time, and fix the exact insertion anchor.

**Tasks**:
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -q` and record the passing count. Expect 53.
- [ ] Confirm `git status --short` shows no foreign modification to `code/src/model_checker/theory_lib/bimodal/examples.py`. If one is present, check `git log` and stop-and-report rather than proceeding.
- [ ] Re-read `examples.py` in full immediately before any edit, to pick up any sibling change.
- [ ] Confirm no stability modal exists: grep `code/src/model_checker/theory_lib/bimodal/` `.py` files for `stab` and `stability`, expecting no operator hit.
- [ ] Confirm all five cited declarations resolve by name in the live BimodalLogic tree, read-only: `stabSnceTarget`, `snce_share_congr`, `not_plusCertifies_stabSnce`, `not_plusCertifies_stabSnce_premise`, `not_plusValidZTime_stabSnce`. Do not edit that repository.
- [ ] Confirm `FormalSystem.Syntax.Formula`'s six constructors and that `FormalSystem.ProofSystem.Axiom` is declared over `Formula`, so the "not an axiom problem" paragraph is grounded in the live source.
- [ ] Fix the insertion anchor: immediately after the final `BX7P_LINEAR_S_TH_example` block and before the `### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###` banner. This keeps all theorem definitions contiguous and places the new section after `MD_CM_3` and `BM_CM_1`/`BM_CM_2`, which the header text refers to as "above", and before `TL_CM_1`/`TL_CM_2`, which it refers to as "below".

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the baseline is 53 passing tests in `test_bimodal.py` and exactly one file
(`examples.py`) needs modification. Confirm the count from the pytest summary line before
proceeding; confirm the file count by checking that no docs file enumerates the example-prefix
list (the research report found the prefix list lives only in `examples.py`'s own docstring).

**Files to modify**:
- None. This phase is read-only.

**Verification**:
- pytest reports 53 passed, 0 failed.
- All five declaration names are found in the BimodalLogic tree.
- `git status --short` shows no unexpected modification to `examples.py`.

---

### Phase 2: THEORY-LIMITS Header Block and Docstring Convention Line [NOT STARTED]

**Goal**: Add the section banner and its full header commentary, plus the one-line docstring
naming-convention update. Comments and docstring only, no executable definitions yet.

**Tasks**:
- [ ] Insert the `THEORY-LIMITS` banner and header comment block at the Phase 1 anchor, using the research report's ready-to-use draft (Recommendations, section 1) as the source text.
- [ ] Verify the header states the inclusion criterion: an entry belongs here iff it records either a genuine non-validity this checker correctly reports as a countermodel and whose significance deserves recording, or a completeness gap in the verified side's certificate system. Include the explicit bar that nothing whose real content is a retracted upstream claim may be encoded as a passing assertion.
- [ ] Verify facts (1) and (2) appear under separate, labelled sub-headings and are never merged into one claim.
- [ ] Verify the "not an axiom problem" paragraph names both constructor lists and states that soundness constrains derivability against validity while what failed is the converse obligation.
- [ ] Verify the "limit of the verified side, not of this checker" paragraph is present and points forward to the two entries.
- [ ] Verify the shape-mechanism paragraph names the temporal-asymmetry diagnosis as refuted, then gives the reflexivity-alone two-instance chain and the equality-of-representatives point.
- [ ] Verify the standing-consequence paragraph states the semi-decision-procedure point and cross-references `docs/ADEQUACY.md` section 7.4's never-report-validity rule.
- [ ] Verify the pending-schema paragraph records the `[stab]`-form as not encodable today, with nothing unchecked asserted about it, and names the blocked extension task by description rather than by number.
- [ ] Verify the Box-versus-stability paragraph states the answer explicitly: both nearest-expressible relatives are invalid here too, but for a different and unrelated reason, since `\Box` carries no same-state restriction and its countermodels disagree at the evaluation time itself.
- [ ] Confirm every upstream citation is a fully qualified declaration name with no `file:line` anchor.
- [ ] Update the top-of-file docstring's naming-convention list from `Countermodels: EX_CM_*, MD_CM_*, TN_CM_*, BM_CM_*` to include `TL_CM_*`, and add a Theory-Limits line to the "Example Categories" list in the Module Structure section.
- [ ] Confirm no task number and no cross-repository task number appears anywhere in the added text.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - add the THEORY-LIMITS banner and header comment block at the Phase 1 anchor; extend the module docstring's naming-convention and category lists.

**Verification**:
- `PYTHONPATH=code/src python -c "import model_checker.theory_lib.bimodal.examples"` succeeds, confirming no edit crossed out of a comment or string region.
- `git diff` read-through confirms every changed hunk lies inside a comment or the module docstring.
- The bimodal unit suite still reports 53 passed, unchanged by a comment-only edit.
- The repository's task-reference check reports no finding on the changed file.

---

### Phase 3: TL_CM_1 and TL_CM_2 Entries and Registry Wiring [NOT STARTED]

**Goal**: Add the two expressible countermodel entries with per-example comments and wire them
into both `countermodel_examples` and the active `example_range`.

**Tasks**:
- [ ] Re-read `examples.py` immediately before editing, in case a sibling changed it since Phase 2.
- [ ] Add `TL_CM_1` (premises `['(A \Since B)']`, conclusions `['\Box (A \Since B)']`) below the header block, using the file's existing `_premises`/`_conclusions`/`_settings`/`_example` five-part shape and `back=2, mid=1, fwd=2, max_time=10, expectation=True`.
- [ ] Add `TL_CM_2` (premises `['\Past A']`, conclusions `['\Box \Past A']`) with the same settings shape.
- [ ] Write each per-example comment in the file's existing convention: what the entry is, that it is the nearest expressible translation substituting `\Box` for the absent `[stab]`, a pointer to the header's Box-versus-stability paragraph rather than a restatement of it, and the measurement note (decides well under 150ms at these defaults; stable across 20 consecutive runs and at enlarged segment lengths).
- [ ] Add a "Theory-Limits Countermodels" subsection to `countermodel_examples` with both keys.
- [ ] Add both keys to `example_range`'s countermodels block, with a one-line comment recording why they are active rather than recorded-but-inactive: each entry's expected outcome is "countermodel found", a currently-true and independently re-verified fact about this checker, which makes it a legitimate regression test. This is exactly the property the `[stab]`-form lacks, which is why that schema gets prose only.
- [ ] Create no Python object of any kind for the `[stab]`-form schema, active or inactive, and add no standing test for it in `test_structure.py`.
- [ ] Leave `test_bimodal.py` untouched; both entries flow through the existing `{**countermodel_examples, **theorem_examples}` merge into `unit_tests` and `test_example_range` automatically.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: the unit suite goes from 53 to exactly 55 passing tests, with the two new
names being `TL_CM_1` and `TL_CM_2`. Confirm by diffing the pytest `-q` summary against Phase 1's
recorded baseline and by running `pytest -k "TL_CM"` to see exactly two collected tests.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - add the two entry blocks with their per-example comments; add both keys to `countermodel_examples` and to `example_range`.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -q` reports 55 passed, 0 failed.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -k "TL_CM" -v` collects exactly two tests and both pass.
- `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py` runs and reports a countermodel for both new entries.
- `git diff` confirms no existing example's premises, conclusions, or settings changed.

---

### Phase 4: Full Gates and No-Regression Audit [NOT STARTED]

**Goal**: Run the complete gate set, audit the delivered commentary against the task's stated
bars, and confirm nothing outside this task's scope changed.

**Tasks**:
- [ ] Run the full bimodal suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -q`.
- [ ] Run the four-theory gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -q`.
- [ ] Run the repository-level suite: `PYTHONPATH=code/src pytest code/tests/ -q`.
- [ ] Audit the header block against each of the six required points and confirm none was trimmed, especially the Box-versus-stability paragraph.
- [ ] Grep the new section for `asymmetr` and confirm every occurrence sits inside the refutation framing, never as an asserted explanation.
- [ ] Grep the new section for `:` line anchors on Lean paths and confirm no `file:line` citation was introduced.
- [ ] Run the repository's task-reference check over `code/` and confirm no task number leaked into `examples.py`.
- [ ] Confirm `/home/benjamin/Projects/BimodalLogic` has no modification attributable to this task.
- [ ] Review `git status --short` and `git diff --staged`, staging `examples.py` by explicit path only, never a directory or glob pathspec.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None. This phase is verification and commit only.

**Verification**:
- All three pytest invocations pass with no new failures relative to the Phase 1 baseline.
- The six header points are each present and intact.
- No `file:line` Lean citation, no task number, and no unintended file in the staged diff.

---

## Testing & Validation

- [ ] Bimodal unit suite: 55 passed (53 baseline plus `TL_CM_1` and `TL_CM_2`).
- [ ] `pytest -k "TL_CM"` collects exactly two tests, both passing.
- [ ] Full bimodal package suite green.
- [ ] Four-theory gate green (`code/src/model_checker/theory_lib/`).
- [ ] Repository-level suite green (`code/tests/`).
- [ ] `dev_cli.py` run over `examples.py` reports a countermodel for both new entries.
- [ ] `git diff` shows no change to any existing example's premises, conclusions, or settings.
- [ ] No operator added to `operators.py`; no change to `test_bimodal.py`.
- [ ] No file modified under `/home/benjamin/Projects/BimodalLogic`.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/examples.py` — the `THEORY-LIMITS` section with its
  header commentary, `TL_CM_1` and `TL_CM_2`, registry wiring in `countermodel_examples` and
  `example_range`, and the updated module docstring.
- `specs/219_bimodal_theory_limits_example_group/summaries/01_*-summary.md` — implementation
  summary, written at completion.

## Rollback/Contingency

All changes are confined to one file and are additive. To revert, remove the `THEORY-LIMITS`
section, the two `countermodel_examples` keys, the two `example_range` keys, and the docstring
convention line, then re-run the bimodal unit suite expecting the 53-test baseline.

If a full working-tree rollback is genuinely needed, take a durable checkpoint first rather than
reverting the tree: `bash .claude/scripts/git-snapshot.sh 219 --no-revert`. Only a real rollback
scenario uses the default reverting mode, and given the concurrent sibling tasks on this shared
tree, prefer a targeted `git checkout HEAD -- code/src/model_checker/theory_lib/bimodal/examples.py`
over any whole-tree operation. See `context/contracts/recovery.md`'s rollback rung for the full
invocation shape including its out-of-scope override flag.

Contingency if `TL_CM_1` or `TL_CM_2` turns out not to decide reliably in the implementation
environment: do not weaken the entry or raise `max_time` past the file's floor without recording
the measurement. Keep the entry in `countermodel_examples` and the header commentary intact, move
the affected key out of the active `example_range`, and record the measured timing in the
per-example comment, matching how this file already documents historical cost profiles.
