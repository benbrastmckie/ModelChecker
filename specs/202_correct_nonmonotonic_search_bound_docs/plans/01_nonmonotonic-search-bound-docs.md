# Implementation Plan: Task #202

- **Task**: 202 - correct_nonmonotonic_search_bound_docs
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None (task 201, the sibling that owned `core.py`'s D6 block and `A2_GAP.md`, is
  complete and committed; its scope is disjoint from this plan's)
- **Research Inputs**: `specs/202_correct_nonmonotonic_search_bound_docs/reports/01_nonmonotonic-search-bound-fixes.md`
- **Artifacts**: plans/01_nonmonotonic-search-bound-docs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Six files in the bimodal theory describe `back`/`mid`/`fwd` as *maximum* segment lengths and advise
users to *raise* them to search harder. For `back` and `fwd` this is false: `WitnessRegistry.wrap()`
folds by **exact** period, so a family of back-period `nb'` is representable at configured `nb` iff
`nb' | nb`. Raising `back` or `fwd` can therefore discard families a smaller value represented —
measured: one formula is SAT at `(3,1,3)` and `(6,1,6)` but genuinely UNSAT (`timeout=False`,
sub-second) at `(4,1,4)` and `(5,1,5)`. This plan corrects every site, in one sweep, and gives
users the operative rule. It is documentation and comments only: no search semantics change.

### The `back`/`fwd` vs. `mid` distinction (binding on every phase)

**`mid` is not affected and must not be described as if it were.** `wrap()` reads `0 <= t < mid`
directly as `nb + t`, with no modulo: `mid` genuinely pads freely, and raising it cannot discard a
representable family. Only `back` and `fwd` are period-locked. Every correction in every phase
below says **`back` and `fwd`**, never "all three" and never "back, mid and fwd" — the task
description's own phrasing on this point is wrong, and repeating it would replace one false claim
with another.

### Canonical corrected wording (single source for all phases)

Phase 1 fixes this wording into `SETTINGS.md`; Phases 2-5 restate it at the length each site
allows, and cite `SETTINGS.md` rather than re-deriving it. The three claims every site must carry
(in whatever form fits) are:

1. **Mechanism**: `back` and `fwd` are *exact* cyclic periods of the searched lasso family's
   repeating segments, not upper bounds. `mid` is the one direct-read segment and does bound a
   length.
2. **Consequence**: a family whose back-period is `nb'` is representable at configured `back = nb`
   only when `nb'` divides `nb`. Raising `back` or `fwd` is therefore *not* monotone — it can lose
   a countermodel a smaller setting found.
3. **Operative rule**: choose `back`/`fwd` as a multiple of the period(s) of interest, or try
   several candidate lengths; sufficiency is a matter of divisibility, not magnitude. (`mid` may be
   raised freely.)

### Research Integration

The research report verified the mechanism against `witness_registry.py:125-132`, independently
reproduced the SAT/UNSAT-by-divisibility pattern against the live search this session, and swept
the whole bimodal tree for the false claim. It found **six** carrier files, not the three the task
description names: the sweep added `README.md`, `USER_GUIDE.md`, and `API_REFERENCE.md`, and found
`ADEQUACY.md`'s claim restated in **three** coordinated spots, not the two named. It also
established the `mid` carve-out above. `ARCHITECTURE.md`, `TRUST_PIPELINE.md`, `ITERATE.md`, and
`examples.py` were swept and are clean. This plan's per-location line anchors come from that
report's Findings section 3, re-confirmed against the working tree while planning.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided for this dispatch; no roadmap phases included.

## Goals & Non-Goals

**Goals**:
- Correct the `back`/`fwd` monotonicity and "maximum length" claims at every one of the six carrier
  files, in one round, so no doc page is left stating the old claim.
- State the exact-period mechanism plainly, and give users an operative rule (choose a multiple of
  the periods of interest), not just a retraction.
- Preserve `mid`'s accurate description as a freely-padded, direct-read segment.
- Keep `ADEQUACY.md` internally consistent: the `(ADEQ)` lede, the A3 row, and 7.1(iii) are one
  claim and change together.

**Non-Goals**:
- Changing the search semantics (no length sweep, no `lcm` computation, no `wrap()` change). The
  deliberate decision to keep exact-period folding is a separate task's call.
- Adding the reproducing SAT/UNSAT case as a standing regression test (implementation-scoped;
  named as a forward pointer only).
- Touching `semantic/core.py`'s D6 block or `A2_GAP.md` — task 201 corrected those and its work is
  committed.
- Creating the `context/project/math/` periodicity note the research recommends (follow-up).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Partial sweep: some files corrected, others left stating the old claim | H | M | Phase 6 re-runs the research report's own grep sweep over the whole bimodal tree and fails the phase on any residual "maximum ... segment"/"raise ... larger" framing |
| Overcorrecting onto `mid`, introducing a new false claim | H | M | The binding distinction is stated above and re-stated in every phase's tasks; Phase 6 greps for any text describing `mid` as non-monotone or period-locked |
| `ADEQUACY.md`'s A3 row corrected while the `(ADEQ)` lede still asserts `>= f(|C|)` | M | M | All three `ADEQUACY.md` spots are one phase (Phase 5), not three |
| `README.md`'s settings block drifts from `core.py`'s (they are verbatim duplicates today) | M | M | Phase 3 depends on Phase 2 and copies the new comment text verbatim; Phase 6 diffs the two blocks |
| A reader takes the doc change as a signal the search behavior changed | M | L | Corrected text describes pre-existing behavior being documented accurately; no phase adds a changelog-style "now" or "changed" framing |
| An edit in `core.py` strays outside the comment/docstring region | M | L | Phase 2 is `prose` tier with a diff read-through plus a module import check |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Canonical correction in `docs/SETTINGS.md` [COMPLETED]

**Goal**: Make `SETTINGS.md` the one authoritative, correct explanation of the exact-period
semantics and the operative rule, so every other site can cite it instead of restating it.

**Tasks**:
- [x] Rewrite the `back` bullet (`docs/SETTINGS.md:20-22`): `back` is the *exact* cyclic period of
      the labels strictly before position `0`, not a maximum length. Keep the `LabelledLasso.back_ne`
      positivity note. *(completed)*
- [x] Rewrite the `fwd` bullet (`:27-29`) the same way, for positions `mid` and beyond. *(completed)*
- [x] Leave the `mid` bullet (`:24-25`) describing a maximum/direct-read length, and make explicit
      that `mid` alone is read directly and so pads freely. *(completed)*
- [x] Replace the false clause in the `back + mid + fwd` paragraph (`:31-34`) — currently "raising
      any of the three enlarges the search" — with the non-monotonicity statement: raising `back` or
      `fwd` changes *which* families are representable rather than enlarging the set, because a
      family of period `p` is representable iff `p` divides the configured length; raising `mid`
      does enlarge the search. *(completed)*
- [x] Add the measured example as evidence, in one or two sentences: a formula SAT at
      `(back,mid,fwd) = (3,1,3)` and `(6,1,6)` but genuinely UNSAT (not a timeout) at `(4,1,4)` and
      `(5,1,5)`, exactly as `6 ∤ 4`, `6 ∤ 5` predicts. *(completed)*
- [x] Rewrite Tips #2 (`:132-134`) from "Raise segment lengths ... will need larger `back`/`mid`/
      `fwd`" into the operative rule: choose `back`/`fwd` as a multiple of the period the refutation
      needs (or try several candidate lengths); a larger value is not automatically at least as good
      as a smaller one. `mid` may be raised freely. *(completed)*
- [x] Add a one-line caveat under the "Formula needing a longer periodic segment" example
      (`:81-90`) pointing at the corrected Segment-Length Settings explanation, so the `2,1,2 ->
      3,2,3` illustration is not read as "raise = more search". Do not rewrite the example. *(completed)*
- [x] Verify no sentence in the file now describes `mid` as period-locked or non-monotone. *(completed)*

**Timing**: 40 minutes

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` - segment-length bullets, the
  `back + mid + fwd` paragraph, Tips #2, and a caveat line on the longer-period example

**Verification**:
- `grep -n "maximum length of a lasso" docs/SETTINGS.md` returns only the `mid` bullet.
- `grep -n "enlarges the search" docs/SETTINGS.md` returns no line claiming this for `back`/`fwd`.
- Read the rendered Segment-Length Settings section end to end: the three claims from the canonical
  wording block above are all present, and `mid` is described as direct-read.
- Diff read-through confirms every hunk is markdown prose.

---

### Phase 2: `semantic/core.py` D4 docstring and settings comment [COMPLETED]

**Goal**: Correct the two D4-scoped comment sites in `core.py` so the code's own commentary matches
`witness_registry.py`'s already-accurate "fixed segment lengths" description.

**Tasks**:
- [x] Rewrite the D4 docstring sentence (`semantic/core.py:35-37`): `back`/`fwd` are the *exact*
      cyclic periods of the `LabelledLasso` back/fwd segments (matching `WitnessRegistry`'s
      `nb`/`nf`) and `mid` is the direct-read segment length (`nm`) — replacing "the maximum segment
      lengths of `LabelledLasso`". Keep the rest of D4 (the `N`/`M`, `max_witnesses`,
      `contingent`/`disjoint`, `max_time`/`expectation`/`iterate`/`solver` clauses) untouched. *(completed)*
- [x] Add one sentence to D4 recording the consequence and the pointer: representability is a
      divisibility condition on `back`/`fwd`, so raising either is not monotone; see
      `docs/SETTINGS.md` for the user-facing rule. *(completed)*
- [x] Rewrite the `DEFAULT_EXAMPLE_SETTINGS` inline comment (`:109-110`): drop "Maximum" for
      `back`/`fwd` in favour of exact-period wording, and drop "raised on demand" in favour of
      "raise as a multiple of the period of interest". Keep the `WitnessRegistry` `nb`/`nm`/`nf`
      cross-reference and the comment's two-line shape. *(completed)*
- [x] Do not touch the D6 block (`:164-170`) or any non-comment line. *(completed)*

**Timing**: 25 minutes

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - D4 docstring paragraph and the
  `DEFAULT_EXAMPLE_SETTINGS` inline comment only

**Verification**:
- `git diff -- code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows changed hunks
  entirely inside the module docstring and the `#` comment lines — no statement, no key, no value.
- `PYTHONPATH=code/src python -c "from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics as S; print(S.DEFAULT_EXAMPLE_SETTINGS['back'], S.DEFAULT_EXAMPLE_SETTINGS['mid'], S.DEFAULT_EXAMPLE_SETTINGS['fwd'])"`
  prints `2 1 2` (defaults unchanged, module still imports).
- `grep -n "maximum segment" semantic/core.py` returns nothing.

---

### Phase 3: `README.md` (three spots, including the duplicated settings block) [COMPLETED]

**Goal**: Bring the theory README into line, keeping its `DEFAULT_EXAMPLE_SETTINGS` block a
verbatim duplicate of `core.py`'s.

**Tasks**:
- [x] Copy Phase 2's new `DEFAULT_EXAMPLE_SETTINGS` comment text verbatim into the README's
      duplicated settings block (`README.md:167-168`), so the two remain byte-identical. *(completed)*
- [x] Rewrite the sentence at `:187-188` — "they bound the maximum size of the searched lasso
      family" — to the exact-period framing for `back`/`fwd` plus direct-read for `mid`, with a
      pointer to `docs/SETTINGS.md` for the operative rule. Keep the rest of that paragraph
      (`max_witnesses`/`temporal_depth`, `contingent`/`disjoint`, the display-setting sentence)
      untouched. *(completed)*
- [x] Correct the one-line summary at `:102` — "`back`/`mid`/`fwd` (maximum lasso segment
      lengths)" — to name `back`/`fwd` as exact periods and `mid` as the direct-read length. This
      site is inside an in-scope file and was not separately called out by the research sweep;
      confirm it exists at that line before editing. *(completed)*

**Timing**: 20 minutes

**Depends on**: 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **three** carrier spots in `README.md` (`:102`,
`:167-168`, `:187-188`). Confirm at implementation time with
`grep -n "maximum\|Maximum" code/src/model_checker/theory_lib/bimodal/README.md` restricted to
lines mentioning `back`/`mid`/`fwd`/`segment`; if the grep surfaces a fourth, fix it in this phase
and record the correction rather than deferring it.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md` - the `:102` summary line, the settings
  code block comment, and the `:187-188` explanatory sentence

**Verification**:
- Extract the two `DEFAULT_EXAMPLE_SETTINGS` comment blocks (README's and `core.py`'s) and confirm
  they are identical text, e.g. by diffing the two `grep -A2 'back/mid/fwd segment'` excerpts.
- `grep -n "maximum" README.md | grep -i "back\|mid\|fwd\|segment"` returns nothing (or only an
  accurate `mid`-only usage).
- Diff read-through confirms markdown-only changes.

---

### Phase 4: `docs/USER_GUIDE.md` and `docs/API_REFERENCE.md` [COMPLETED]

**Goal**: Correct the two remaining user-facing pages, including their two "raise these" / "raise
segment lengths" imperatives, which are the sites most likely to mislead a user mid-investigation.

**Tasks**:
- [x] `USER_GUIDE.md:70`: replace "the maximum lengths of the searched lasso family's three
      segments" with `back`/`fwd` as exact periods and `mid` as the direct-read length. *(completed)*
- [x] `USER_GUIDE.md:157-159`: correct the three inline comments in the `settings = {...}` example
      (`# Maximum back-segment length` etc.) — exact-period wording for `back`/`fwd`, retain a
      length description for `mid`. *(completed)*
- [x] `USER_GUIDE.md:166-168`: rewrite the "**`back`/`mid`/`fwd`**: raise these if a formula's
      refutation genuinely needs a longer periodic pattern" bullet into the operative rule — choose
      `back`/`fwd` as a multiple of the needed period, since a larger non-multiple can lose a
      countermodel a smaller value found; `mid` may be raised freely. Keep the "53 examples decide
      at the defaults" clause, which is factual. *(completed)*
- [x] `API_REFERENCE.md:80`: replace "maximum lasso segment lengths" in the Key Attributes list
      with the corrected one-line characterization. *(completed)*
- [x] `API_REFERENCE.md:481`: rewrite Debugging Tips #3 ("some formulas need larger `back`/`mid`/
      `fwd`") into the divisibility rule, keeping the "not a larger `N`/`M` (which no longer exist)"
      clause. *(completed)*
- [x] Point both pages at `docs/SETTINGS.md` for the full explanation rather than duplicating the
      measured example. *(completed: also corrected two additional hits at USER_GUIDE.md:266 and :330 surfaced by the Scope Hypothesis grep)*

**Timing**: 30 minutes

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **five** carrier spots across the two files (three in
`USER_GUIDE.md`, two in `API_REFERENCE.md`). Confirm with
`grep -n "maximum\|Maximum\|[Rr]aise\|larger" docs/USER_GUIDE.md docs/API_REFERENCE.md` filtered to
lines mentioning `back`/`mid`/`fwd`/`segment`; fix any additional hit in this phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - settings-list bullet, the three
  example comments, and the Bimodal-Specific Considerations bullet
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` - Key Attributes line and
  Debugging Tips #3

**Verification**:
- `grep -n "maximum\|Maximum" docs/USER_GUIDE.md docs/API_REFERENCE.md | grep -i "back\|fwd"`
  returns nothing.
- Neither file now advises raising `back`/`fwd` without the divisibility qualifier; read both
  corrected passages end to end to confirm.
- Both files link to `SETTINGS.md` from the corrected passage.

---

### Phase 5: `docs/ADEQUACY.md` — the three coordinated spots [COMPLETED]

**Goal**: Correct the `(ADEQ)` statement, the A3 table row, and 7.1 condition (iii) together, so
the document's headline claim and its components agree that sufficiency is a divisibility
condition, not a magnitude one.

**Tasks**:
- [x] `(ADEQ)` lede (`:519-522`): the direction is currently stated at "segment-length settings
      `back, mid, fwd >= f(|C|)`". Restate the condition so it is satisfiable in principle:
      settings at which the compressed family is *representable* — `back` and `fwd` common
      multiples of the family's periods (with `mid >= ` the needed mid length) — rather than merely
      `>= f(|C|)`. *(completed)*
- [x] A3 row (`:532`): change "Bound realization: configured lengths `>= f(|C|)`" to a
      divisibility/representability formulation, and keep its "Vacuous until A1 supplies `f`"
      status — A3 remains vacuous; what changes is *what* A3 would have to deliver. *(completed)*
- [x] 7.1 condition (iii) (`:590-592`): replace "at a segment length at least that bound" with an
      honest formulation. Name both routes the research recorded, as alternatives, without
      committing to either: `back`/`fwd` a common multiple of every candidate period up to
      `f(|C|)` (correct but `lcm(1..f) = e^{O(f)}`, impractical), or a sweep of `(back, mid, fwd)`
      over the grid up to `f(|C|)` (`f^3` solver calls, cheap). State that neither is implemented. *(completed)*
- [x] Add one sentence (in 7.1, near (iii)) recording the mechanism and its evidence: `wrap()`
      folds `back`/`fwd` by exact period, so representability is `p | n`, measured — SAT at
      `(3,1,3)`/`(6,1,6)`, genuinely UNSAT at `(4,1,4)`/`(5,1,5)`. *(completed)*
- [x] Do not weaken or restate A0/A1/A2 status, and do not touch `A2_GAP.md`. *(completed)*
- [x] Re-read the section 7 header, the table, and 7.1 together to confirm the three corrected
      spots now say the same thing. *(completed)*

**Timing**: 35 minutes

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - the `(ADEQ)` statement in section
  7, the A3 row, and 7.1 condition (iii) plus one evidence sentence

**Verification**:
- `grep -n "f(|C|)" docs/ADEQUACY.md` — no remaining site states a bare `>=`-only sufficiency
  condition for `back`/`fwd`.
- The `(ADEQ)` lede, the A3 row, and 7.1(iii) are mutually consistent on re-read.
- A0/A1/A2 rows and section 7.2/7.3 text are unchanged (`git diff` confirms the hunks are confined
  to the three spots plus the added sentence).

---

### Phase 6: Cross-file consistency sweep and gate [NOT STARTED]

**Goal**: Prove the sweep is complete, that `mid` was not overcorrected, and that nothing outside
comments and prose changed.

**Tasks**:
- [ ] Re-run the research report's own sweep over the whole theory:
      `grep -rn "maximum length\|maximum segment\|max segment\|enlarge\|raising\|raise" code/src/model_checker/theory_lib/bimodal/ --include="*.py" --include="*.md"`
      and confirm every surviving hit is either accurate (a genuine `mid` length, `max_witnesses`,
      `max_time`) or outside this task's subject.
- [ ] Grep for overcorrection: confirm no file describes `mid` as period-locked, non-monotone, or
      subject to divisibility.
- [ ] Confirm every corrected site says `back` and `fwd` (never "all three", never "back, mid and
      fwd") when stating the non-monotonicity.
- [ ] Confirm the `DEFAULT_EXAMPLE_SETTINGS` comment in `README.md` and `semantic/core.py` are
      byte-identical.
- [ ] `git diff --stat` covers exactly the six files; `git diff` shows no executable Python line
      and no settings value changed.
- [ ] Run the bimodal test suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` — expected
      unchanged from the pre-task baseline (record both).
- [ ] Record the two deliberate non-goals as forward pointers in the summary (not in the docs): the
      standing regression test for the measured SAT/UNSAT case, and the
      `context/project/math/` periodicity note.

**Timing**: 30 minutes

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This plan asserts the carrier set is exactly **six** files (`docs/SETTINGS.md`,
`semantic/core.py`, `docs/ADEQUACY.md`, `README.md`, `docs/USER_GUIDE.md`,
`docs/API_REFERENCE.md`) and that `ARCHITECTURE.md`, `TRUST_PIPELINE.md`, `ITERATE.md`, and
`examples.py` are clean. The sweep above is the confirmation. If a seventh carrier file turns up,
correct it in this phase and record it; if one of the six turns out already clean, record that
instead of editing it.

**Files to modify**:
- None (verification only; any correction this phase discovers is an in-scope fix to one of the six)

**Verification**:
- The sweep grep produces no false-claim hit anywhere under `theory_lib/bimodal/`.
- Bimodal test suite result matches the pre-task baseline.
- `git diff` is comment-and-prose-only across all six files.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` — unchanged
      from the baseline recorded before Phase 1 (this is a docs/comments change; any delta is a
      defect in the change, not an expected outcome).
- [ ] `PYTHONPATH=code/src python -c "from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics"`
      succeeds and `DEFAULT_EXAMPLE_SETTINGS` still reads `back=2, mid=1, fwd=2`.
- [ ] Sweep grep (Phase 6) returns no residual "maximum"/"raise for more search" framing for
      `back`/`fwd`.
- [ ] No file describes `mid` as non-monotone or period-locked.
- [ ] `ADEQUACY.md`'s `(ADEQ)` lede, A3 row, and 7.1(iii) agree with each other.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` (corrected; canonical explanation)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (D4 docstring + settings comment)
- `code/src/model_checker/theory_lib/bimodal/README.md` (three spots)
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` (three spots)
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` (two spots)
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (three coordinated spots)
- `specs/202_correct_nonmonotonic_search_bound_docs/summaries/01_*-summary.md` (at completion,
  recording the two forward pointers from Phase 6)

## Rollback/Contingency

Every phase is a scoped, committed-per-substep prose edit to a single file (Phase 3 to one file,
Phase 4 to two), so reverting is `git revert` of the offending phase commit — no working-tree
discard is needed and none should be performed. If a mid-phase edit must be abandoned before
commit, revert the specific hunks by re-applying the original wording from the research report's
Findings section 3, which quotes the pre-change text for every location. Should a genuine
whole-tree rollback ever become necessary, follow `context/contracts/recovery.md`'s rollback rung
for the correct snapshot-then-rollback invocation shape rather than improvising one.
