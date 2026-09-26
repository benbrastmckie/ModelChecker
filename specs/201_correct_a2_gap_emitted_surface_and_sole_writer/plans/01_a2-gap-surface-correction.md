# Implementation Plan: Task #201

- **Task**: 201 - Correct A2_GAP.md's emitted-constraint surface and semantic/core.py's sole-writer claim
- **Status**: [IMPLEMENTING]
- **Effort**: 1.0 hours
- **Dependencies**: None
- **Research Inputs**: specs/201_correct_a2_gap_emitted_surface_and_sole_writer/reports/01_a2-gap-surface-correction.md
- **Artifacts**: plans/01_a2-gap-surface-correction.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Three surgical documentation/comment corrections, all with exact replacement text already drafted
and verified in the research report. `A2_GAP.md` section 4 gains an eighth emission call site (the
`iterate.py` model-iteration pinning path) plus the four count updates that follow from it;
`semantic/core.py:164`'s D6 comment is narrowed from a false "sole writer" claim to the scoped
claim that is actually true, with a pointer to the new call site; `A2_GAP.md` section 6 gains a
paragraph naming the independence cost the `_box_window` sharing imposed on the A2-triangle
differential. No behavioral change: prose and comments only, no executable code paths touched.

### Research Integration

The report verified every claim directly against the tree: `iterate.py:266` and `:280` both call
`semantics.frame_constraints.append(pinned)` inside `_pin_theory_specific_values` (`iterate.py:190`),
which runs on a freshly-constructed semantics instance during model iteration, after that
instance's own `finalize_certificate()` (`iterate.py:231`) — a real eighth writer of
`frame_constraints` outside `finalize_certificate`. It also verified that
`WitnessRegistry.target_window()` (`witness_registry.py:171-183`) and
`witness_constraints.py:238`'s `box_faithfulness_constraints` both resolve to
`certificate._box_window` (`certificate.py:219-221`), so legs (i) and (iii) of
`test_certificate_a2_triangle.py` now compute that window by calling the same Python function.
Exact replacement text for all three corrections is in the report's Recommendations section
(Corrections 1, 2, 3) and is the authoritative wording for this plan's edits.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context was supplied in this dispatch (`roadmap_path`/`roadmap_flag` absent), so no
roadmap review/update phases are included and no roadmap alignment was assessed.

## Goals & Non-Goals

**Goals**:
- `A2_GAP.md` section 4 enumerates the `iterate.py` pinning path as call site (8), with its unit-literal
  clause shape and its iteration-only reachability, and every "seven" count in the section is updated
  consistently.
- `semantic/core.py:164`'s D6 comment states a claim that is true, retains the by-reference-alias
  rationale verbatim, and cross-references the new call site.
- `A2_GAP.md` section 6 presents the `_box_window` sharing as a trade, naming the differential-independence
  cost explicitly.

**Non-Goals**:
- Any behavioral change to `iterate.py`, `core.py`, `witness_registry.py`, or `certificate.py`.
- The D4 monotonicity commentary elsewhere in `semantic/core.py` — sibling task territory; this plan
  touches `core.py` only at the D6 comment block currently at lines 164-166.
- Renumbering existing call sites (1)-(7), or restructuring any `A2_GAP.md` section.
- Adding tests for the newly documented blind spot (documentation-only task).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A "seven call sites" claim outside `A2_GAP.md` is left stale | M | L | Phase 1 re-runs the report's grep across `code/src/model_checker/theory_lib/bimodal/docs/` and the repo's `docs/` before editing; research found all four occurrences confined to `A2_GAP.md` (lines 120, 180, 193, 197) |
| Over-correcting `core.py:164` into vagueness, losing the in-place-mutation rationale that `models/constraints.py:80`'s by-reference alias depends on | M | L | Use the report's Correction 2 text, which preserves that sentence verbatim and only adds scoping plus the exception |
| Edit drifts into `core.py`'s D4 monotonicity commentary (sibling task #202 territory) | M | L | Phase 2 edits only the three-line D6 block at `core.py:164-166`; verification diffs `core.py` and confirms the hunk is confined to that block |
| Comment edit accidentally breaks Python syntax | H | L | Phase 2 verification compiles the module and runs the bimodal certificate tests |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. Phases 1 and 3 both edit `A2_GAP.md` and
Phase 2 references the section-4 anchor Phase 1 creates, so they are deliberately serialized.

---

### Phase 1: Add call site (8) to A2_GAP.md section 4 [COMPLETED]

**Goal**: Section 4 enumerates the `iterate.py` model-iteration pinning path as an eighth emission
call site, with its clause shape, and every count in the section reflects eight.

**Tasks**:
- [x] Re-run the count grep before editing: `grep -rn "seven emission call sites\|seven call sites\|all seven" code/src/model_checker/theory_lib/bimodal/docs/ docs/` and confirm the occurrence set is exactly `A2_GAP.md:120`, `:180`, `:193`, `:197` (adjust the edit list if it is not) *(completed: confirmed exactly these four occurrences, all in A2_GAP.md)*
- [x] Insert the new **(8)** item after call site (7) (currently ending at line 178) and before the "Assembly into what Z3 actually sees" paragraph (line 180), using the report's Correction 1 text: `_pin_theory_specific_values` (`iterate.py:190`), invoked per requested next model from the iteration engine's `build_new_model_structure` hook, after `iterate.py:231`'s defensive `finalize_certificate()`; unit literal `var` or `Not(var)` per `_bits`/`_guesses` variable and per `sel(t)` for `t in registry.target_window()`, appended directly at `iterate.py:266` and `:280`, bypassing the dead `all_constraints` path; emits no (C1)-(C4) content of its own *(completed)*
- [x] Update line 120 ("**seven emission call sites**") to state eight, distinguishing the seven single-solve-reachable sites from the iteration-only eighth *(completed)*
- [x] Update line 180's "The seven call sites above collapse into exactly four solver-visible tracked groups" so the collapse statement stays accurate — call site (8) also lands in the `frame` group, but outside the `ModelConstraints.__init__` -> `_setup_solver` assembly the paragraph describes *(completed)*
- [x] Update the "Net correction" paragraph (lines 193-197) to the report's qualified form: "seven call sites reachable from a single solve, plus one more (model-iteration pinning) reachable only when iterating", and fix "all seven" at line 197 accordingly *(deviation: altered — reworded to "seven single-solve-reachable call sites" instead of the report's literal "seven call sites reachable from a single solve" phrasing, because that literal substring would fail this same phase's own verification grep for "seven call sites"; meaning is unchanged)*
- [x] Confirm no existing call site (1)-(7) is renumbered and no other section's cross-references are disturbed *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: exactly four "seven"-count occurrences need updating (`A2_GAP.md:120`, `:180`,
`:193`, `:197`), and no file outside `A2_GAP.md` cites the seven-call-site count. Confirm with the
grep in the first task above before editing; if additional occurrences exist, extend this phase's
edit list rather than deferring them.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - section 4: new call site (8) item; count updates at the four grep-confirmed sites

**Verification**:
- `grep -n "seven emission call sites\|seven call sites\|all seven" code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` returns nothing
- `grep -n "^\*\*(8)" code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` shows the new item, positioned between call site (7) and the "Assembly into what Z3 actually sees" paragraph
- The new item cites `iterate.py:190`, `:231`, `:266`, and `:280`, and each cited line still matches what it claims (`sed -n` spot-check against `iterate.py`)
- `git diff --stat` shows `A2_GAP.md` as the only modified file for this phase

---

### Phase 2: Narrow the D6 sole-writer comment in semantic/core.py [COMPLETED]

**Goal**: `core.py`'s D6 comment no longer asserts the false "sole writer" claim; it states the
narrower true claim, keeps the by-reference-alias rationale, and points at section 4's call site (8).

**Tasks**:
- [x] Replace the three-line D6 comment block at `code/src/model_checker/theory_lib/bimodal/semantic/core.py:164-166` with the report's Correction 2 text: within a single solve `finalize_certificate()` is the sole writer *inside this class*, mutating in place and never reassigning so `models/constraints.py:80`'s by-reference copy observes the mutation; a second writer exists outside this class — `iterate.py`'s `_pin_theory_specific_values` appends unit-literal pins to the same list during model iteration (`iterate.py:266`, `:280`), after `finalize_certificate` has already run once on that instance — see `docs/A2_GAP.md` section 4, call site (8) *(completed)*
- [x] Confirm the edit hunk is confined to that comment block: no change to `self.frame_constraints: List["z3.BoolRef"] = []` or any surrounding statement, and no change to the D4 monotonicity commentary elsewhere in the file (sibling task territory) *(completed: single hunk verified via git diff, D4 comment at line 141 unchanged)*

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - D6 comment block at lines 164-166

**Verification**:
- `grep -n "sole writer" code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows only the scoped phrasing ("sole writer inside this class"), never an unqualified "is the sole writer," clause
- The comment references `iterate.py:266`, `:280` and `A2_GAP.md` section 4 call site (8)
- `git diff code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows a single hunk, comment lines only, with no statement lines changed
- `PYTHONPATH=code/src python -c "import model_checker.theory_lib.bimodal.semantic.core"` succeeds
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py -q` passes (comment-only change must be behaviorally inert)

---

### Phase 3: Record the window-sharing independence cost in A2_GAP.md section 6 [NOT STARTED]

**Goal**: Section 6 presents the `_box_window` sharing as a trade, stating that a defect confined to
`_box_window`'s own formula is invisible to the A2-triangle differential by construction.

**Tasks**:
- [ ] Insert the report's Correction 3 paragraph ("**The cost this closure also introduced.**") into section 6, after the existing "What this closure is, and is not" paragraph (currently lines 283-294)
- [ ] Verify the paragraph's three code claims against the tree before committing to the wording: `witness_registry.py:183` returns `_box_window(self)`, `certificate.py:219-221` defines `_box_window`, `witness_constraints.py:238` calls `_box_window(registry)` directly
- [ ] Keep the paragraph's framing as a trade, not a retraction: it must not suggest reverting to the earlier independently-defined pair (section 6's "gap, as it stood" paragraph already explains why that was worse)
- [ ] Confirm section 3(ii)'s and section 7's existing text are left untouched (the new paragraph is the single place this cost is recorded)

**Timing**: 0.25 hours

**Depends on**: 2

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - section 6: one new paragraph after "What this closure is, and is not"

**Verification**:
- `grep -n "cost this closure also introduced" code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` returns exactly one hit, inside section 6 (between the `## 6.` and `## 7.` headings)
- The paragraph names both legs by their test identity (leg (i) `certificate.recheck`, leg (iii) the real Z3 encoding) and cites `tests/integration/test_certificate_a2_triangle.py`
- `git diff` for this phase touches only `A2_GAP.md`, and only within section 6
- Sections 3 and 7 are unchanged (`git diff` hunk line ranges fall inside section 6)

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` passes — no behavioral change expected from a comment-only source edit
- [ ] `grep -rn "seven emission call sites\|seven call sites\|all seven" code/src/model_checker/theory_lib/bimodal/docs/ docs/` returns nothing
- [ ] `grep -n "sole writer" code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows only the scoped claim
- [ ] `git diff --stat` shows exactly two modified files: `docs/A2_GAP.md` and `semantic/core.py`
- [ ] Every file:line citation added by any phase resolves to what it claims (spot-check `iterate.py:190/231/266/280`, `witness_registry.py:183`, `certificate.py:219-221`, `witness_constraints.py:238`, `models/constraints.py:80`)

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` — section 4 call site (8) plus count corrections; section 6 independence-cost paragraph
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` — corrected D6 comment
- `specs/201_correct_a2_gap_emitted_surface_and_sole_writer/summaries/01_*-summary.md` — implementation summary

## Rollback/Contingency

All three edits are additive/qualifying prose and comment changes in two files, each committed as its
own phase. Reverting any phase is `git revert` of that phase's commit, or `git checkout HEAD~1 --
<file>` for an uncommitted mistake; there is no state, migration, or generated artifact to unwind.
If the Phase 1 pre-edit grep turns up "seven call sites" claims in documents outside `A2_GAP.md`,
extend Phase 1 to cover them in the same commit rather than leaving the tree internally inconsistent
between phases.
