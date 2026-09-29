# Implementation Plan: Apply Upstream A1 / A1-Γ / A3 Adequacy-Chain Rows

- **Task**: 216 - Apply upstream adequacy chain rows
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None blocking. Sibling task declares
  `code/src/model_checker/theory_lib/bimodal/examples.py` as its file scope; this plan reads
  that file in Phase 1 and edits nothing in it.
- **Research Inputs**: `specs/216_apply_upstream_adequacy_chain_rows/reports/01_apply-adequacy-chain-rows.md`
- **Artifacts**: plans/01_apply-adequacy-chain-rows.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  no-task-references-in-deliverables.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Two documents in `code/src/model_checker/theory_lib/bimodal/docs/` record the (ADEQ) adequacy
chain, and both are now out of step with the live BimodalLogic tree: `ADEQUACY.md` calls A1 flatly
open and A3 vacuous, `TRUST_PIPELINE.md` states A3 in the magnitude form that `ADEQUACY.md` itself
argues is wrong, and every line-number anchor into the `WitnessFamily/` subtree has drifted from
its declaration while every gate in both repositories stayed green. This plan applies the three
corrected component rows, resolves the cross-document contradictions, and migrates that subtree's
citations onto the name + manifest convention so the anchors cannot drift again.

Done means: both documents state only the current status of each component, with no transition
narrative, no dated language, and no line-number anchor into `WitnessFamily/` or its
`Compression/` subdirectory; every declaration name cited resolves in the live tree; the two
documents agree with each other on A1, A1-Γ, and A3.

### Research Integration

The research report verified every claim in the upstream hand-off note independently against the
live BimodalLogic tree rather than trusting the note, and supplies copy-ready replacement text for
every edit site (report sections 5a through 5g). Three findings shape this plan's phase structure:

- **Every declaration this task cites already resolves**, at the file recorded in BimodalLogic's
  `scripts/lean-citation-manifest.json`, whose `C35` gate reports PASS over 86 seeded names. The
  name + manifest convention is live, not aspirational.
- **The line-anchor drift is document-wide, not confined to the two `joint_countermodel`
  occurrences the dispatch names.** The report measured drift at nearly every currently-cited
  `WitnessFamily/` line (+1 to +16). Only six cited lines are still exactly correct. Item 3 is
  therefore scoped as a document-wide sweep over that one subtree.
- **A second cross-document contradiction exists beyond the A3 one the dispatch names**:
  `TRUST_PIPELINE.md`'s A1 row reads "Open — route named, owned by the Lean development," which
  will contradict the corrected `ADEQUACY.md` A1 row in exactly the way Item 2 describes for A3.
  This plan folds it in, because leaving it out reproduces the defect the task exists to fix.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap path was supplied in the dispatch context; no roadmap consultation performed.

## Goals & Non-Goals

**Goals**:

- Replace `ADEQUACY.md` section 7's A1 and A3 component rows and insert a new A1-Γ row, leaving
  A0 and A2 untouched.
- Add a section 7.1a recording A1-Γ as its own open obligation, and bring section 7.1's heading
  and prose onto present-tense status.
- Adopt the representability form of A3 in `TRUST_PIPELINE.md` so the two documents agree, and
  restate the compression / bounded-enumerator row as standing scope.
- Migrate every `WitnessFamily/`-subtree citation in both documents from `file.lean:NNN` to
  name + file, with the provenance note explaining why.
- Leave both documents free of transition narrative, change-log prose, and dated language.

**Non-Goals**:

- Editing anything in `~/Projects/BimodalLogic`. That tree is read-only for this task.
- Editing `code/src/model_checker/theory_lib/bimodal/examples.py`. It is read in Phase 1 for its
  premise and conclusion inventory only, and is a sibling task's declared file scope.
- Converting citations outside the `WitnessFamily/` subtree. `BiLasso/`, `Semantics/`,
  `Metalogic/Independence/`, `Metalogic/Soundness.lean`, and `ProofSystem/Axioms.lean` anchors
  stay exactly as they are.
- Proving, attempting, or estimating the effort of A1-Γ or A3's open clause.
- Any change to Python source, tests, or behavior. This task edits two markdown files.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A bare-filename citation is missed because the sweep greps for the `WitnessFamily` path prefix | H | H | Phase 1 builds the inventory with two greps: one path-prefixed, one over the twelve bare module basenames. Both bare-name sites are already identified below. |
| `Enumerate.lean` is converted at the wrong site: the name exists in both `BiLasso/` (out of scope) and `WitnessFamily/Compression/` (in scope) | H | M | Phase 1 records the one live `Enumerate.lean` anchor as an explicit decoy. Phase 4 verifies the containing sentence's subtree before touching any bare-name site. |
| The mixed-subtree row in the section 4.1 table is over-converted, dropping in-scope-adjacent anchors that belong to a different subtree | M | M | The row is named explicitly in Phase 4's site table with a per-anchor instruction rather than a per-row one. |
| Sibling task changes `examples.py`, invalidating the premise and conclusion counts the A1-Γ row asserts | M | M | Phase 1 re-derives both counts from the live file immediately before they are written, rather than carrying them forward from the report. |
| Transition narrative leaks in from the upstream note's own change-log framing | M | M | Phase 5 greps both documents for the specific banned constructions and reads the edited spans end to end. |
| A declaration name is written that does not resolve upstream | H | L | Phase 1 resolves every name to be cited against the live tree and the citation manifest before any document is edited. |
| A concurrent sibling edits one of the two target documents | M | L | Both files are re-read immediately before each edit; commits stage only this task's own files by explicit path. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint files
(`ADEQUACY.md` and `TRUST_PIPELINE.md` respectively) and are genuinely independent.

---

### Phase 1: Verify names and build the citation-site inventory [COMPLETED]

**Goal**: Establish, against live sources rather than the research report, that every declaration
name about to be written resolves, that the premise and conclusion counts the A1-Γ row asserts are
still true, and that the set of citation sites Phase 4 must convert is complete and correctly
bounded. This phase writes no document text; it produces the inventory the later phases consume.

**Tasks**:

- [x] Re-resolve every declaration name this task will cite against the live BimodalLogic tree:
      `exists_witnessFamily_of_not_validZTime`, `semanticConsequenceIn_nil_iff`,
      `compressionBound`, `cands`, `mem_cands_of_bounded`, `validZTime_iff_noCertifiedCandidate`,
      `Compression.decidableValidZTime`, `WitnessFamily.Refutes`, `refutes_of_certifies`,
      `WitnessFamily.joint_countermodel`, `exists_labelledLasso_of_history_realized`,
      `exists_labelledLasso_of_history`, `WitnessFamily.Target`, and the four `Decidable`
      instances in `WitnessFamily/Decide.lean`.
- [x] Cross-check each against `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json` and
      record the file each resolves to. Record any name that does not resolve as a blocker rather
      than writing it.
- [x] Confirm `f`'s closed form by locating `compressionBound`'s definition in the live tree and
      reading the definitional equation, so the row states what upstream actually checks by `rfl`.
- [x] Re-derive from the live `examples.py`, not from the report: whether every countermodel
      example still has a non-empty premise list, and whether `MD_CM_1` still has two conclusions.
      Read only; this file belongs to a sibling task's scope.
- [x] Build the citation-site inventory over both documents with two complementary greps: one for
      anchors carrying the `WitnessFamily` path prefix, and one for the bare module basenames
      (`Basic`, `Predicates`, `Agreement`, `Decide`, `Std`, `Examples`, `Types`, `Cycle`,
      `Fulfil`, `Extract`, `Family`, `Enumerate`, `Assembly`). Record every hit with its line
      number and the subtree it actually belongs to.
- [x] Mark the known traps in the inventory explicitly: the `Enumerate.lean` anchor in section 7.1
      belongs to `BiLasso/` and is out of scope; the section 4.1 Lemma 3 row mixes an in-scope
      `Std.lean` anchor with out-of-scope `ShiftSet.lean` and `TruthTransport.lean` anchors, so it
      converts per-anchor, not per-row.
- [x] Confirm no section renumbering is needed to insert section 7.1a, by checking that no
      cross-reference in either document points into section 7.2 or 7.3 by an offset rather than
      by number.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The research report enumerates sixteen conversion sites; an independent
grep of the live documents found eighteen lines carrying a path-prefixed anchor plus two
bare-basename lines, and one bare-basename line that is an out-of-scope decoy. Treat neither
count as settled. Confirm the true site count at implementation time by running both greps above
and reconciling the union against the report's table; if the union exceeds the report's list,
the additional sites are in scope, and if it falls short, establish why before proceeding.

**Files to modify**:

- None. This phase is read-only and produces an inventory consumed by Phases 2 through 4.

**Verification**:

- Every declaration name in the task list above resolves to a file in the live tree, and the file
  matches the manifest entry for that name.
- The premise and conclusion counts are restated from a fresh read of `examples.py`.
- The inventory lists, for every hit, whether it is in scope, out of scope, or mixed, with the
  reason.
- `git status --short` shows no modification in this repository.

---

### Phase 2: ADEQUACY.md — component rows, section 7.1 status, section 7.1a [COMPLETED]

**Goal**: Bring `ADEQUACY.md`'s record of the (ADEQ) chain onto current status: A1 partially
discharged at a named instance, A1-Γ recorded as the open general form the chain consumes, A3 live
rather than vacuous, with section 7.1's heading and framing matching.

**Tasks**:

- [x] Re-read `ADEQUACY.md` immediately before editing, in case a sibling has changed it.
- [x] In section 7's component table, replace the A1 row. State that A1 is discharged only at the
      empty-premise, single-conclusion instance, via `exists_witnessFamily_of_not_validZTime`,
      sorry-free, with axiom closure `{propext, Classical.choice, Quot.sound}`, and that the
      general form is a separate open obligation. Leave A0 and A2 untouched.
- [x] Insert a new A1-Γ row immediately after A1. Record that every countermodel example in this
      repository's `examples.py` has a non-empty premise list and that `MD_CM_1` has two
      conclusions, using the counts re-derived in Phase 1, so the restriction reads as
      load-bearing here rather than cosmetic.
- [x] Replace the A3 row. State `f`'s closed form as confirmed in Phase 1 rather than a table of
      sampled bound values. State that the `mid` clause is satisfiable by magnitude and that the
      `back`/`fwd` clause remains open because the landed theorem bounds segment lengths and not
      minimal periods, so representability against a registry folding by exact modulus still needs
      a bounded sweep. Keep the `max_witnesses` precondition note.
- [x] Rewrite section 7.1's heading so it no longer asserts A1 is open outright.
- [x] Replace section 7.1's opening paragraph, which currently reports a status and an effort
      estimate read off the upstream repository's task tracker. That is both stale and exactly the
      kind of tracker metadata that goes out of date silently. State the route's mathematical
      content in present tense and drop the tracker status, the effort figure, and any reference
      to a tracker entry.
- [x] Replace the paragraph beginning "A1 is recorded as open" with a present-tense statement of
      what is and is not discharged, and of what follows for the meaning of "no certificate within
      bounds".
- [x] Rewrite the heading that frames `exists_annot_of_truth` as a candidate route "examined and
      rejected" into a standing statement of why that theorem does not supply A1's bound. Keep the
      three numbered reasons verbatim: they are durable technical facts, not history. Do not carry
      across any record of which route was tried when.
- [x] Rewrite the closing paragraph of that discussion so conditions (i) and (ii) are recorded as
      met by the landed theorem for the carrier, condition (i) as unmet for the premise context
      (which is A1-Γ's obligation), and condition (iii) as the remaining representability gap.
      Leave the measured-against-the-live-search sentence and the two-routes paragraph unchanged.
- [x] Leave residue items (iii-a) through (iii-e) unchanged; they are current facts about A3's
      representability gap and are independent of A1's status.
- [x] Add section 7.1a immediately after section 7.1, recording A1-Γ as its own obligation and
      naming the already-general declarations that bound the residue. Do not add an effort
      estimate or a completion forecast.
- [x] Confirm no anchor written in this phase carries a line number, and no sentence written in
      this phase uses transition, change-log, or dated framing.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: This phase assumes section 7.1a can be inserted without renumbering
sections 7.2 through 7.4. Phase 1 confirms this by checking that no cross-reference in either
document addresses those sections positionally. If any does, renumber or re-target those
references within this phase rather than deferring.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — section 7 component table (A1
  replaced, A1-Γ inserted, A3 replaced, A0 and A2 untouched); section 7.1 heading, opening
  paragraph, status paragraph, `exists_annot_of_truth` heading and closing paragraph; new section
  7.1a.

**Verification**:

- The section 7 table has five rows in order A0, A1, A1-Γ, A2, A3, with A0 and A2 byte-identical
  to their prior text.
- A grep for transition and recency constructions over the changed spans returns nothing: "moves
  from", "what changed", "recently", "as of", "supersedes", "previously", "used to", "now that",
  "no longer" used of a document's own prior claim rather than of a technical fact.
- No anchor added in this phase matches a `.lean:` followed by a digit.
- The three numbered reasons under the `exists_annot_of_truth` discussion are unchanged, verified
  by diff.
- `git diff` for this phase touches `ADEQUACY.md` only.

---

### Phase 3: TRUST_PIPELINE.md — A-component table and the Lean-development row [COMPLETED]

**Goal**: Remove the live contradiction between the two documents and restate the compression and
bounded-enumerator row as standing scope rather than as a live capability.

**Tasks**:

- [x] Re-read `TRUST_PIPELINE.md` immediately before editing.
- [x] In the A-component table, replace the A3 row with the representability form, matching
      `ADEQUACY.md` section 7's wording, and cross-reference that section. The magnitude form
      ("configured lengths ≥ `f(|C|)`") must not survive anywhere in this document.
- [x] Replace the A1 row so it states partial discharge at the empty-premise, single-conclusion
      instance, and insert an A1-Γ row for the general form, matching Phase 2's rows. This closes
      the same contradiction Item 2 names for A3, one row up.
- [x] Rewrite the compression and verified-bounded-enumerator row in the "In the Lean development"
      table. State the proved instance, state that the general form is the remaining open
      mathematics, and state the enumerator's standing scope: verified absence is a theorem at
      restricted scope, not a live capability and not a practical replacement for trusting Z3
      UNSAT. Give all three reasons the two sides differ: the Lean criterion quantifies over the
      whole segment-length grid while a Z3 UNSAT verdict is at one configured triple, there is no
      executable target that runs the enumerator, and the decision procedure is a `def` rather
      than a global `instance`. Write this as the row's standing scope, never as a correction of a
      previous claim.
- [x] In the "In this repository" table, correct the A3 bounds row, which states the work is
      blocked until the Lean side supplies `f`. That is now false: `f` exists in closed form. State
      what actually remains, which is the representability gap, not `f`'s existence.
- [x] Confirm the sequencing note following the Lean-development table is still accurate against
      the rewritten rows, and adjust only if it now asserts something false.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts that the magnitude form of A3 and the "blocked until the
Lean side supplies `f`" framing each occur exactly once in this document. Confirm at
implementation time by grepping for the magnitude phrasing and for "supplies `f`" across the whole
file before editing, and convert every occurrence found rather than the first.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — A-component table (A1
  replaced, A1-Γ inserted, A3 replaced); "In the Lean development" table, compression and
  enumerator row; "In this repository" table, A3 bounds row.

**Verification**:

- Grepping the whole document for the magnitude form of A3 returns nothing.
- The A-component table's A1, A1-Γ, and A3 rows agree with `ADEQUACY.md` section 7's rows on
  status, and neither document asserts a status the other contradicts.
- The enumerator row names all three reasons the two sides quantify differently.
- The same transition and recency grep from Phase 2 returns nothing over the changed spans.
- `git diff` for this phase touches `TRUST_PIPELINE.md` only.

---

### Phase 4: Citation convention migration across the WitnessFamily subtree [COMPLETED]

**Goal**: Convert every citation into `Metalogic/Decidability/WitnessFamily/` and its
`Compression/` subdirectory from a line anchor to a name plus file, and record the convention in
the document's own provenance note so a future reader knows the file is for orientation only.

**Tasks**:

- [x] Re-read both documents immediately before editing.
- [x] Work the Phase 1 inventory site by site. For each in-scope site, keep the declaration name
      and the file path, and drop the line number. Where a site cites a declaration only by line,
      supply the declaration's name.
- [x] Convert the two `joint_countermodel` occurrences in `ADEQUACY.md` and the one in
      `TRUST_PIPELINE.md` by name, not by renumbering them to the declaration's current line.
- [x] Handle the section 4.1 Lemma 3 row per-anchor: convert only the `WitnessFamily/Std.lean`
      anchor, leaving the `ShiftSet.lean` and `TruthTransport.lean` anchors in the same row
      untouched.
- [x] Leave the `Enumerate.lean` anchor in section 7.1 untouched. It resolves in the `BiLasso/`
      subtree, which is out of scope, despite sharing a basename with a `Compression/` module.
- [x] Convert the two bare-basename in-scope sites: the `lab` decoding-function citation in
      section 1, and the four decidability-instance anchors in section 5.2's closing paragraph.
- [x] Rename section 5.2's table column from the file-and-line form to the file form, and drop
      every line number in that table's cells. Every row in that table cites the in-scope subtree.
- [x] Broaden section 4.1's provenance note so it covers every `WitnessFamily` and `Compression`
      citation in the document rather than only that table. State that the file is orientation,
      not an anchor, and that the upstream generated and gated citation manifest resolves each
      cited name to its current location. The drift itself may be stated as the standing reason
      the convention exists; do not narrate when it was discovered or what the document said
      before.
- [x] Update the "Scope and status" sentence at the top of `ADEQUACY.md` that claims every cited
      name was checked to resolve at the cited file and line, so it records the split convention:
      this subtree by name, other subtrees by file and line.
- [x] Cite no task numbers from either repository anywhere in either document.

**Timing**: 1 hour

**Depends on**: 2, 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the conversion set is exactly the union Phase 1
establishes, and that it is confined to the two target documents. Confirm at implementation time
by re-running both Phase 1 greps after the conversion: the path-prefixed grep must return no hit
carrying a line number, and every bare-basename hit that remains must be independently confirmed
to resolve outside the in-scope subtree.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — sections 1, 2, 3, 4.1, 5.1, 5.2,
  the section 4.1 provenance note, and the "Scope and status" convention sentence.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — the Stage 6 component
  citation.

**Verification**:

- Grepping both documents for a `.lean:` followed by a digit on any line also mentioning the
  in-scope subtree returns nothing.
- Every remaining `.lean:` anchor in either document is confirmed, by name, to belong to a
  different subtree.
- Every declaration name written in this phase appears in the Phase 1 resolution list.
- No task number from either repository appears in either document.

---

### Phase 5: End-to-end read-through and style verification [COMPLETED]

**Goal**: Confirm the dispatch's VERIFICATION clause holds over the finished documents, read as
documents rather than as diffs.

**Tasks**:

- [x] Read `ADEQUACY.md` end to end. Confirm it states only current status, carries no transition
      narrative, no change-log prose, and no dated or recency language, and that scope restrictions
      are present as standing facts rather than as history.
- [x] Read `TRUST_PIPELINE.md` end to end, to the same standard.
- [x] Confirm the two documents agree on A0, A1, A1-Γ, A2, and A3, row by row.
- [x] Re-run the full anchor grep over both documents and confirm no line-number anchor into the
      in-scope subtree survives.
- [x] Confirm every fully-qualified declaration name cited in the edited spans resolves in the
      live BimodalLogic tree, by a final pass against the citation manifest.
- [x] Confirm no task number from either repository appears in either document, per this
      repository's no-task-references-in-deliverables rule. Provenance belongs in this task's own
      `specs/` artifacts.
- [x] Run the repository's documentation-affecting checks if any apply to these paths, and record
      the result either way.
- [x] Confirm `git status --short` shows only the two intended documents modified by this task,
      and stage them by explicit path. If a foreign modification or commit is present, stop and
      report rather than proceeding.

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: prose

**Files to modify**:

- None. Verification only; any defect found is fixed in the phase that owns it.

**Verification**:

- Both documents read cleanly as present-tense status documents.
- The anchor grep is clean over the in-scope subtree.
- Every cited name resolves.
- No task-number reference in either document.
- Only the two intended files are staged.

## Testing & Validation

- [x] Every declaration name cited in the edited spans resolves in the live BimodalLogic tree and
      matches its citation-manifest entry.
- [x] No `.lean:NNN` anchor into `Metalogic/Decidability/WitnessFamily/` or its `Compression/`
      subdirectory survives in either document.
- [x] Every remaining `.lean:NNN` anchor in either document is confirmed to belong to a different
      subtree and is unchanged from its pre-task text.
- [x] `ADEQUACY.md` section 7 and `TRUST_PIPELINE.md`'s A-component table agree, row by row, on
      A0, A1, A1-Γ, A2, and A3.
- [x] The magnitude form of A3 does not appear in either document.
- [x] Neither document contains transition narrative, change-log prose, or dated language.
- [x] Neither document contains a task-number reference from either repository.
- [x] `git status --short` shows exactly the two intended documents modified by this task.
- [x] `examples.py` is unmodified.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — edited.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — edited.
- `specs/216_apply_upstream_adequacy_chain_rows/summaries/01_apply-adequacy-chain-rows-summary.md`
  — implementation summary, recording provenance, including the upstream hand-off note and its
  cited report, which must not be cited from the deliverable documents themselves.

## Rollback/Contingency

Both edited files are tracked markdown with no build or runtime surface, so rollback is a matter
of restoring their prior committed content.

- **Within a phase, before commit**: the phase's own changes are the only uncommitted work in
  these two files. Restoring one file to its committed state discards only that phase's edits.
  Because sibling tasks are dispatched on this same working tree in this cycle, never use a
  whole-tree discard. Restore the single named file, and only after confirming with
  `git status --short` that no other change to it is in flight.
- **After a phase commit**: revert that specific commit rather than resetting, so no sibling's
  commit in the same window is disturbed.
- **If a genuine snapshot is wanted before Phase 4's document-wide sweep**, take a non-reverting
  checkpoint with `bash .claude/scripts/git-snapshot.sh 216 --no-revert`, which is durable and
  leaves the working tree alone. Do not use the default reverting mode as a precautionary
  checkpoint.
- **If Phase 1 finds a declaration name that does not resolve**: do not write that citation. Mark
  the affected row or sentence blocked, complete the remaining phases, and record the unresolved
  name in the summary. A citation that does not resolve is the exact defect this task exists to
  remove.
