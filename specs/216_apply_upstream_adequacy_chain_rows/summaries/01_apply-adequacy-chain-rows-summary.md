# Implementation Summary: Task #216

- **Task**: 216 - Apply upstream adequacy chain rows
- **Status**: [COMPLETED]
- **Started**: 2026-09-29T12:00:00Z
- **Completed**: 2026-09-29T13:55:00Z
- **Effort**: ~2 hours
- **Dependencies**: None blocking. Sibling task 219 declares `examples.py` as its file scope; this
  task read that file for the premise/conclusion inventory and edited nothing in it.
- **Artifacts**: plans/01_apply-adequacy-chain-rows.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  no-task-references-in-deliverables.md

## Overview

Applied the A1 / A1-Γ / A3 adequacy-chain component rows to `ADEQUACY.md` and
`TRUST_PIPELINE.md`, resolved the live cross-document contradiction over A3's stated form
(magnitude versus representability), and migrated every `WitnessFamily`/`Compression`-subtree
citation in both documents from `file.lean:NNN` line anchors to the name + manifest convention.
Every declaration cited was independently re-verified against the live BimodalLogic tree (not
merely taken from the upstream hand-off note or this task's own research report) before being
written.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — section 7's component table: A1
  row replaced (partially discharged at the empty-premise, single-conclusion instance), new A1-Γ
  row inserted (open, the general form (ADEQ) consumes), A3 row replaced (live and open, `f` in
  closed form, representability gap named); A0 and A2 left byte-identical. Section 7.1's heading,
  opening paragraph, "A1 is recorded as open" paragraph, and the `exists_annot_of_truth` heading
  and closing paragraph rewritten to present-tense status, dropping the upstream task-tracker
  status/effort language. New section 7.1a added recording A1-Γ as its own bounded, open
  obligation. Every `WitnessFamily`/`Compression`-subtree citation converted from `file:line` to
  name + file (fourteen sites: `LabelledLasso`/`lab`, `joint_countermodel` ×2, `WitnessFamily.std`
  ×2, the `Std.lean` row, the mixed Lemma-3 row's `sh_surj` anchor only, `shiftTruth_iff_mem`/
  `truth_iff_mem`, `untl_mem_of_witness`/`snce_mem_of_witness`, `not_consequence_ztime`/`_base`,
  `no_witnessFamily_of_MF`, `lab_sub_back_length`/`lab_add_fwd_length`, the section 5.2 window
  table's five rows and column header, and the four `Decidable` instances). The section 4.1
  provenance note broadened document-wide, and the top-of-document "Scope and status" sentence
  updated to record the split convention.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — A-component table: A1 row
  replaced, A1-Γ row inserted, A3 row replaced with the representability form (removing the
  magnitude form that contradicted `ADEQUACY.md`). "In the Lean development" table's
  compression/enumerator row rewritten to state the proved instance, the open general form, and
  the enumerator's standing (non-practical) scope with all three reasons the two sides quantify
  differently. "In this repository" table's A3 bounds row corrected: no longer "blocked until the
  Lean side supplies `f`" (false — `f` exists in closed form); now names the representability gap
  as what remains. Stage 6's `joint_countermodel` citation converted to name + file.

## Decisions

- Followed this task's own research report's copy-ready text (independently re-verified against
  the live tree during implementation) rather than the upstream hand-off note's text verbatim,
  since the report's wording was already written to this document's exact current structure and
  the dispatch's style constraint.
- Kept the `exists_annot_of_truth` rejection's three numbered reasons, the "measured against the
  live search" sentence, the two-routes paragraph, and residue items (iii-a) through (iii-e)
  unchanged, per the dispatch: they are durable technical facts, not history.
- Rewrote section 7.1's opening paragraph's route description rather than transcribing it
  unchanged, since it referenced `BiLasso/GoodCycle.lean` as the route's basis; the live tree
  shows the landed proof uses a presentation-free transcription in
  `WitnessFamily/Compression/Cycle.lean` instead. Dropped internal proof-mechanism claims that
  could not be independently re-verified without disproportionate effort, keeping only the
  verified pigeonhole-over-subformula-set-space description and the unchanged literature citation.
- Included the TRUST_PIPELINE.md A1/A1-Γ row update (research report finding 5e), beyond the
  dispatch's literal A3-only wording for Item 2, because leaving A1's row as "Open — route named,
  owned by the Lean development" would reproduce the same live cross-document contradiction Item 2
  exists to fix, one row up. The plan's Phase 3 folded this in explicitly.

## Plan Deviations

- None (implementation followed plan).

## Verification

- Build: N/A (markdown-only change).
- Tests: N/A.
- Every declaration name cited resolves in the live BimodalLogic tree and matches its
  `scripts/lean-citation-manifest.json` entry (spot-verified by direct `grep` against the live
  `.lean` sources and by `jq` cross-check against the manifest, in addition to the manifest's own
  gate `C35` reporting PASS over 86 seeded names).
- `compressionBound`'s closed form was confirmed directly in
  `WitnessFamily/Compression/{Cycle,Extract}.lean` rather than taken on trust.
- Every countermodel example in `examples.py` re-derived as having a non-empty premise list, and
  `MD_CM_1` confirmed to have two conclusions, by a fresh `grep` immediately before writing the
  A1-Γ row.
- `grep` for the banned transition/recency constructions ("moves from", "recently", "as of",
  "supersedes", "previously", "used to", "now that", "no longer") returns no hits inside any span
  this task edited (all hits found are in pre-existing, unedited prose elsewhere in the
  documents).
- `grep` for `.lean:` followed by a digit confirms zero remaining line-number anchors into the
  `WitnessFamily`/`Compression` subtree in either document; all remaining `.lean:` anchors resolve
  to a different subtree (`Semantics/`, `Metalogic/Soundness.lean`, `Metalogic/Independence/`,
  `BiLasso/`, `ProofSystem/Axioms.lean`) and are unchanged from their pre-task text.
- The two documents' A0/A1/A1-Γ/A2/A3 rows read side by side and agree on status.
- `grep` confirms no task-number reference from either repository in either document.
- `git status --short` shows only `ADEQUACY.md` and `TRUST_PIPELINE.md` modified by this task in
  the bimodal docs directory; `examples.py` is unmodified; the BimodalLogic repository was not
  written to (only read).

## Impacts

- Both documents now state only current, present-tense status for the (ADEQ) chain's A1/A1-Γ/A3
  components, with no contradiction between them.
- Citations into the `WitnessFamily`/`Compression` subtree can no longer silently drift the way
  `joint_countermodel`'s citation had (cited at line 232, actually at line 248, with no gate on
  either side catching it): they now resolve by name against BimodalLogic's own C35-gated
  manifest.
- A1-Γ is now recorded as its own named, open obligation in both documents, so future work on the
  general `Γ ⊨ Δ` form has a stable place to land rather than being silently folded into A1's row
  or overlooked because A1 now reads as partially discharged.

## Follow-ups

- None from this task. A1-Γ's residue, A3's representability gap (section 7.1(iii-a)'s bounded
  sweep), and the sentence-translation fixture consumption are all pre-existing open items,
  correctly recorded as such rather than newly introduced by this task.

## References

- `specs/216_apply_upstream_adequacy_chain_rows/plans/01_apply-adequacy-chain-rows.md`
- `specs/216_apply_upstream_adequacy_chain_rows/reports/01_apply-adequacy-chain-rows.md`
- Provenance (read-only, not cited from the edited documents themselves): the upstream
  BimodalLogic repository's hand-off note and its cited research report, both under that
  repository's own `specs/` tree, supplied copy-ready replacement text that this task
  independently re-verified against the live tree before applying.
