# Implementation Summary: Apply Upstream Citation Corrections

- **Task**: 214 - Apply upstream citation corrections
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T18:30:00Z
- **Completed**: 2026-09-28T19:15:00Z
- **Effort**: ~1 hour
- **Dependencies**: None
- **Artifacts**: plans/01_apply-citation-corrections.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Applied, by mechanical lookup against `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json`,
all four dispatched upstream citation corrections plus the second stale-citation cluster and
wrong-file citation the research phase found in the same table rows (Decision D1), plus the three
handed-off residue rows, to `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` and
`ARCHITECTURE.md`. All six plan phases completed; no source, test, or gate file was touched, and
`~/Projects/BimodalLogic` was read-only throughout.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`:
  - §4.1 table: refreshed 10 stale line citations (4 A0 `ZTimeSharpness` rows, 6 `ShiftSet`
    second-cluster rows) to current manifest `keyword_line` values; replaced the deleted
    `Std.lean:73-80`/`Int.abs_lt_one_iff` Limit-discharge citation with `ShiftSet.ofIntAction`/
    `ShiftSet.sep_of_succOrder` and strengthened the verdict to "kernel-checked... not
    hand-proved"; split the grouped, one-position-shifted `Std.lean:84, 91, 96` citation into
    each declaration's own `keyword_line` (81, 87, 92); tightened `sh_surj` to its own
    `keyword_line` (98); split the wrong-file `Truth.box_const`/`sh_surj` citation into their own
    (different) files; added a provenance note after the table recording that names are
    load-bearing and numbers are a re-resolvable derived view.
  - Prose sites: the "Why the design is deterministic" determinism bullet and the §7.2 "A0" gap
    discussion both repeated the stale/deleted citations from the table; both now cite by
    declaration name (the A0 discussion drops its line-number suffixes per Decision D2, matching
    the document's existing `:295` no-line-number precedent).
  - §4.2 table: added a `worldNonempty` residue row (`FrameOver.worldNonempty` field,
    `TaskFrame.worldNonempty` accessor) and a `PartialHistory`/`PartialHistory.IsTotal`/
    `WorldHistory` residue row (paper anchor `def:world-history`); added a reasoned-exclusion note
    for the `TruthCorr` residue row, preserving its hand-off conditional verbatim.
  - Lemma 1's Limit bullet: added a general-transcription note stating `TaskFrame.Limit`
    transcribes only the subset half of the paper's set equation, with the superset half derived
    choice-free via `TaskFrame.nullity_of_serial_limit` rather than postulated.
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`:
  - Condensed table Row "1 (Frame)": replaced the `Int.abs_lt_one_iff` attribution with the
    corrected `ShiftSet.sep_of_succOrder`/`ShiftSet.ofIntAction` wording, and refreshed the same
    six stale `ShiftSet` line citations as `ADEQUACY.md`.
  - Row "3 (Time-shift preservation)": refreshed `forward_repr`'s stale citation and tightened
    `sh_surj`'s citation to its own `keyword_line`.

## Decisions

- **D1 (surfaced to the user at plan time, non-blocking)**: the second stale-citation cluster
  (`shRel_comp`, `shRel_serial`, `shRel_saturation`, `fibre_isRegular`, `frame_isRegular`,
  `forward_repr`) and the `Truth.box_const` wrong-file citation, though not among the dispatch's
  four named rows, were fixed in this same pass — they sit in the exact table rows this task
  already edits and come from the same upstream corrections table.
- **D2**: line numbers were dropped from prose sites (§7.2 A0 discussion, the determinism bullet)
  but kept, refreshed, in the §4.1 citation table, plus a new provenance note explaining names are
  load-bearing and numbers are a derived, re-resolvable view.
- **D3**: `ADEQUACY.md:295`'s time-shift citation was left unchanged (instantiated lemma), so the
  `TruthCorr` residue row's triggering condition remains unmet.
- **D4**: citations omit the manifest's `FormalSystem/` path prefix, matching this repository's
  existing convention.

## Residue-Row Decisions (recorded per the dispatch's "decide, and record" instruction)

- **`worldNonempty`** (upstream row 3): **added** as a new §4.2 row — the paper's reading of `W`
  as nonempty is load-bearing (an empty carrier would vacuously satisfy all four constraints while
  validating falsehood), and this document's own Lemma 1 proof already relies on it.
- **`PartialHistory`/`WorldHistory`** (upstream row 20): **added** as a new §4.2 row against
  `def:world-history` — the Box case of `TruthAt` quantifies over the total histories, so the
  whole Box case rests on this transcription.
- **`TruthCorr`** (upstream row 24): **reasoned exclusion**, not added. The row is conditional on
  §4.2 citing the general `Truth.truthAt_of_truthCorr` lemma; this document cites the instantiated
  `TimeShift.timeShift_preserves_truth` at `:295` instead, so the triggering condition is unmet.
  The conditional is preserved verbatim (not paraphrased) in the new note, and the `:295` citation
  was left unchanged.

## Plan Deviations

- **Phase 3's literal verification grep** (`grep -n "ZTimeSharpness.lean:2" ADEQUACY.md` returns
  no hit) is over-broad by construction: the corrected §4.1 table values (263, 274, 289) also
  start with digit 2, and Decision D2 explicitly keeps numbers in the table. Verified the intended
  criterion instead — the exact retired strings (`Int.abs_lt_one_iff`, `Std.lean:73-80`) return
  zero hits anywhere in the file, and the §7.2 prose citations carry no line-number suffix at all.

## Verification

- Build: N/A (documentation-only task)
- Tests: N/A (no source or test file touched)
- Files verified: Yes — `git diff` read-through on every phase confirmed only enumerated rows/
  passages changed; every `*.lean:NNN` citation written matches the Phase 1 manifest lookup;
  `grep -rn "Int.abs_lt_one_iff\|Std.lean:73-80"` returns nothing anywhere in the docs directory;
  a fresh scope re-grep confirms `ADEQUACY.md` and `ARCHITECTURE.md` remain the only affected
  files; `~/Projects/BimodalLogic` received zero writes (pre-existing, unrelated uncommitted
  modifications in that tree predate and are untouched by this task).

## Impacts

- Readers of `ADEQUACY.md`/`ARCHITECTURE.md` now see citations that resolve to their actual
  current Lean declarations rather than to a different, unrelated theorem three lines away.
- The Limit obligation's discharge path is now stated consistently and correctly (kernel-checked
  via `ShiftSet.ofIntAction`/`sep_of_succOrder`) across all three sites that discuss it.
- The adequacy argument's transcription audit is measurably larger and more honest: two previously
  unaudited but load-bearing transcription decisions (`worldNonempty`, the totality of
  `WorldHistory`) now have recorded rows.

## Follow-ups

- The upstream page's own "deferred cross-repository proposal" (a consuming-side manifest
  checker, analogous to BimodalLogic's C35) remains unimplemented and out of this task's
  `file_scope`; it is recorded there, not here, as a named future task.
- A future pass authorized to touch every §4.1 row could rename the table's "File:line" column to
  "Lean location" and drop numbers entirely, per the plan's Decision D2 discussion — deliberately
  not done here since this task's edit set is scoped to the touched rows only.

## References

- `specs/214_apply_upstream_citation_corrections/plans/01_apply-citation-corrections.md`
- `specs/214_apply_upstream_citation_corrections/reports/01_citation-corrections-mapping.md`
- `~/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md` (read-only input)
- `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json` (read-only input)
