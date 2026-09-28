# Implementation Plan: Apply Upstream Citation Corrections

- **Task**: 214 - Apply upstream citation corrections
- **Status**: [NOT STARTED]
- **Effort**: 3.25 hours
- **Dependencies**: None
- **Research Inputs**: `specs/214_apply_upstream_citation_corrections/reports/01_citation-corrections-mapping.md`
- **Artifacts**: plans/01_apply-citation-corrections.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Apply, by mechanical lookup against `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json`,
the citation corrections the producing repository already derived and handed off. All edits are
confined to `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` and
`ARCHITECTURE.md` — the two files a fresh grep of the docs directory confirmed are the only ones
carrying line-numbered citations against the affected declarations. Nothing is re-derived by hand
and nothing in the producing repository is touched. Done means: every citation this task edits
resolves by declaration name in the manifest, the two documents agree with each other, and the
three handed-off residue rows each have a recorded decision.

### Research Integration

The research report resolved all four dispatched correction rows plus the three residue rows
against the manifest by name and tabulated exact before/after data. Four findings materially shape
this plan and are carried into the phases below:

1. **Rows 2 and 4 each have more sites than the dispatch named.** The stale
   `Std.lean:73-80` / `Int.abs_lt_one_iff` citation appears at `ADEQUACY.md:243` (§4.1 table) *and*
   `ADEQUACY.md:323` ("Why the design is deterministic") *and* `ARCHITECTURE.md:181` (condensed
   table). All three must move together or the two documents contradict each other.
2. **Row 4 needs no citation change, only a statement.** Neither `TaskFrame.Limit` nor
   `TaskFrame.nullity_of_serial_limit` is cited anywhere in either file today, and every passage
   that could read as over-claiming the full set equation is actually about the *concrete*
   certified construction, which `ADEQUACY.md:108-127` proves in both directions directly. The
   correction therefore lands as a short added note, not a repair.
3. **Row 24 (`TruthCorr`) does not currently apply.** `ADEQUACY.md:295` cites the *instantiated*
   time-shift lemma, not the general `Truth.truthAt_of_truthCorr` the row's hand-off is
   conditional on. The recorded outcome is a reasoned-exclusion note preserving the conditional
   exactly, not a new audit row and not silence.
4. **A second stale-citation cluster sits in the same table rows.** Six `ShiftSet` citations
   (`shRel_comp`, `shRel_serial`, `shRel_saturation`, `fibre_isRegular`, `frame_isRegular`,
   `forward_repr`) are stale the same way as Row 1, and `Truth.box_const` is cited against the
   wrong file entirely. See Decisions below for this plan's scope ruling.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context. `specs/ROADMAP.md` exists and was
checked: it carries no item this plan advances (its bimodal entries concern packaging, the
differential-oracle gate, and missing notebooks). No roadmap phases are included.

## Decisions

These are recorded here because the research report explicitly deferred them to the plan phase.

- **D1 — The second stale-citation cluster and the `box_const` wrong-file citation ARE in scope**,
  applied in Phase 2 alongside the named rows. Rationale: they occupy the exact same table rows
  (`ADEQUACY.md:241-248`, `ARCHITECTURE.md:181,183`) that Rows 2 and 3 already require editing;
  they come from the same upstream corrections table and resolve by the same mechanical lookup;
  and the dispatch's own SCOPE section instructs deriving the affected set fresh rather than
  trusting the enumerated list. Leaving them would produce a table half-corrected and half-stale
  within single rows. This is severable: Phase 2's checklist separates the named-row items from
  the cluster items, so the cluster can be dropped without disturbing anything else. Surfaced
  non-blocking via `user_decision` for the user's review.
- **D2 — Line numbers are dropped in prose, kept (and corrected) in the §4.1 citation table.** The
  dispatch's "prefer names over lines" instruction is qualified by "where the surrounding prose
  allows it". Prose sites (`ADEQUACY.md:323`, `:715`, `:719`, `:724-725`) allow it and have an
  existing in-document precedent at `:295` (`` `TimeShift.timeShift_preserves_truth`
  (`Semantics/TruthTransport.lean`) ``, no line number), so they lose their `:NNN` suffixes
  permanently. The §4.1 table's third column is literally headed `File:line` and eighteen of its
  rows are outside this task's correction set, so converting only the touched rows to name-only
  would make the table internally inconsistent, and converting all of them means editing rows no
  upstream row authorizes. The table therefore keeps numbers, refreshed from the manifest, plus a
  new standing provenance note (Phase 2) recording that the names are load-bearing and the numbers
  are a derived view re-resolvable against the manifest. The alternative — renaming the column to
  "Lean location" and dropping every number — is noted as the cleaner long-term end state for a
  future task that is authorized to touch every row.
- **D3 — `ADEQUACY.md:295`'s time-shift citation is NOT changed.** Switching it from the
  instantiated to the general lemma would trigger Row 24 and pull `TruthCorr`'s five fields into
  the audit as an unrequested side effect.
- **D4 — Path convention follows this repository, not the manifest.** The manifest's `file` field
  carries a `FormalSystem/` prefix; every existing citation in both target files omits it.
  Corrections omit it too.

## Goals & Non-Goals

**Goals**:
- Repair the four stale `ZTimeSharpness` citations at both `ADEQUACY.md` sites (§4.1 table and the
  §7.2 A0 discussion).
- Replace the deleted `Std.lean:73-80` / `Int.abs_lt_one_iff` Limit-discharge citation with
  `ShiftSet.ofIntAction` / `ShiftSet.sep_of_succOrder` at all three sites, and strengthen the
  verdict to record that the obligation is now kernel-checked rather than hand-proved.
- Tighten the loose `WitnessFamily` range citations to each declaration's own manifest
  `keyword_line`, repairing the one-position shift in the grouped `:84, 91, 96` citation.
- State the `TaskFrame.Limit` correction (subset half transcribed; superset half derived
  choice-free via `TaskFrame.nullity_of_serial_limit`, not postulated), consistent with the
  existing state-sharing argument.
- Add the two applicable residue rows (`worldNonempty`; `PartialHistory`/`WorldHistory`) to
  §4.2 and record the `TruthCorr` row's conditional non-application.
- Leave every touched citation resolvable by name against the manifest.

**Non-Goals**:
- No edit of any kind under `~/Projects/BimodalLogic` (read-only input).
- No source, test, gate, or configuration change in this repository; documentation only.
- No full-theory gate run (the dispatch states none is required).
- No re-derivation of any line number by hand; the manifest is the sole source.
- No change to `ADEQUACY.md:295`, to `ADEQUACY.md:108-127`'s Lemma 1 hand proof, or to the
  `total_eq_orbit` / `ShiftSet#sep` citations upstream marks "no correction needed".
- No consuming-side citation-drift checker (flagged by research as a future task, explicitly
  deferred upstream).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The producing tree moves again between research and implementation, staling the report's `keyword_line` values | M | M | Phase 1 re-resolves every name against a fresh manifest read before any edit; the report's numbers are treated as provisional, names as load-bearing |
| A site is fixed in one document but not the other, leaving `ADEQUACY.md` and `ARCHITECTURE.md` contradicting each other on how the Limit obligation is discharged | H | M | Every site is enumerated per-phase; Phase 6 greps both files for the retired strings (`Int.abs_lt_one_iff`, `Std.lean:73-80`) and fails if any survive |
| Row 2's citation is swapped but the weaker "discharged trivially" verdict is left standing — explicitly forbidden by the dispatch | M | M | Phase 2 and Phase 3 each carry the verdict-language change as its own checklist item, separate from the citation swap; Phase 6 re-reads both hunks |
| Scope creep from D1's second cluster obscures the four dispatched rows in review | L | M | Phase 2's checklist separates named-row items from cluster items; the phase commit message names both; D1 is surfaced non-blocking for the user |
| Sibling task 213 is dispatched into the same working tree this cycle with no declared file scope | M | L | Re-read each file immediately before editing; stage only this task's own files by explicit path (never `git add -A`, a directory, or a glob); if a foreign commit or foreign uncommitted modification appears in these two files, stop and report after checking `git log` |
| The `worldNonempty` / `PartialHistory` additions drift from the upstream hand-off's phrasing | L | M | Phase 5 transcribes the hand-off's wording from `~/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md` rather than paraphrasing; Row 24's conditional is preserved verbatim per the dispatch |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel. Phases 3 and 5 both touch `ADEQUACY.md` but
disjoint regions; they are serialized (5 depends on 3) rather than run in parallel so that
same-file edits never race.

---

### Phase 1: Re-resolve every citation against a fresh manifest read [NOT STARTED]

**Goal**: Produce an authoritative, current name -> (file, keyword_line, span) lookup covering
every declaration this task will cite, so no later phase reads a line number from the research
report.

**Tasks**:
- [ ] Read `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json` (read-only; never write
      anything under `~/Projects/BimodalLogic`).
- [ ] Extract the current `file`, `keyword_line`, and span for every name in the set:
      `not_validIn_base_prior_UZ`, `not_validIn_base_z1`, `prior_UZ_minFrameClass_sharp`,
      `z1_minFrameClass_sharp`, `ShiftSet.ofIntAction`, `ShiftSet.sep_of_succOrder`,
      `WitnessFamily.std`, `WitnessFamily.std_isZTime`, `WitnessFamily.std_sat_ztime`,
      `WitnessFamily.std_sat_base`, `WitnessFamily.sh_surj`, `ProofSystem.FrameClass.Sat`,
      `TaskFrame.Limit`, `TaskFrame.nullity_of_serial_limit`, `FrameOver` (`worldNonempty`
      field), `TaskFrame.worldNonempty`, `PartialHistory`, `PartialHistory.IsTotal`,
      `WorldHistory`, `ShiftSet.shRel_comp`, `ShiftSet.shRel_serial`,
      `ShiftSet.shRel_saturation`, `ShiftSet.fibre_isRegular`, `ShiftSet.frame_isRegular`,
      `ShiftSet.forward_repr`, `Truth.box_const`, `Semantics.TruthCorr`.
- [ ] Confirm each entry's `status` is `resolved`; record any name that is missing or unresolved
      rather than substituting a guess.
- [ ] Diff the extracted values against the research report's tables and record every divergence
      explicitly — the manifest wins on every disagreement.
- [ ] Re-read
      `~/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md`'s "Corrections the
      consuming table owes" table and its "Hand-off" subsection, capturing rows 3, 20 and 24's
      wording verbatim for Phase 5.
- [ ] Write the resulting lookup to the scratchpad (not into the repository).

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: 27 declaration names are expected to resolve, all with
`"status": "resolved"`, against a 63-entry manifest. Confirm by counting resolved lookups against
the name list above; if any name fails to resolve, stop and record it rather than falling back to
the report's numbers.

**Files to modify**:
- None (read-only phase; scratchpad output only).

**Verification**:
- Every name in the list resolves to a manifest entry with `status: resolved`.
- Any divergence from the research report's tables is written down, with the manifest value taken
  as authoritative.

---

### Phase 2: Correct the ADEQUACY.md §4.1 citation table [NOT STARTED]

**Goal**: Every citation in the §4.1 "Every step, mapped to a landed, sorry-free Lean
counterpart" table (currently `ADEQUACY.md:240-257`) points at the declaration the manifest says
it does, and the Limit row's verdict records the improvement.

**Tasks**:

*Dispatched rows:*
- [ ] Row 1 — update the three A0 rows (currently `:225`, `:236`, `:251, :262`) to the manifest's
      current `keyword_line` values for `not_validIn_base_prior_UZ`, `not_validIn_base_z1`,
      `prior_UZ_minFrameClass_sharp`, `z1_minFrameClass_sharp`.
- [ ] Row 2 — in the "Lemma 1, Limit" row, remove the `Std.lean:73-80` range and the
      `Int.abs_lt_one_iff` attribution entirely (the proof is deleted; this is not a re-point) and
      cite `ShiftSet.ofIntAction` and `ShiftSet.sep_of_succOrder` instead.
- [ ] Row 2 (verdict, separate item) — rewrite the row's framing so it states the obligation is
      now **kernel-checked** (discharged from discreteness through the shift action) rather than
      hand-proved. Do not swap the citation and leave the old weaker wording.
- [ ] Row 3 — replace the grouped `Std.lean:84, 91, 96` citation with each of
      `std_isZTime`, `std_sat_ztime`, `std_sat_base` against its own manifest `keyword_line`
      (this repairs the one-position shift where `:91` and `:96` currently land inside the *next*
      declaration's span).
- [ ] Row 3 — tighten `sh_surj`'s citation from its `span_end` to its own `keyword_line`.

*Second cluster and wrong-file citation (per Decision D1; severable):*
- [ ] Update the six stale `ShiftSet` citations in this table — `shRel_comp`, `shRel_serial`,
      `shRel_saturation`, `fibre_isRegular`, `frame_isRegular`, `forward_repr` — to their current
      manifest `keyword_line` values.
- [ ] Split the "Lemma 3 / Corollary 3.1" row's second citation in two: `Truth.box_const` cites
      `Semantics/TruthTransport.lean` (it is not declared in `Std.lean` at all) and `sh_surj`
      keeps its own `Std.lean` location.

*Provenance note (per Decision D2):*
- [ ] Add a short note immediately after the table recording that the declaration names are the
      load-bearing citation and the line numbers are a derived view taken from BimodalLogic's
      generated, C35-gated `lean-citation-manifest.json`, re-resolvable by name. Note for the
      record that every gate in both repositories was green while the stale citations stood —
      which is why the manifest and its check exist.
- [ ] Leave `total_eq_orbit` (`:252`), `ShiftSet#sep`, and every row outside the correction set
      untouched.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: 8 of the table's ~18 rows are expected to change (4 dispatched-row edits
across 5 rows, plus 3 rows carrying only second-cluster edits), with no row outside the
correction set touched. Confirm at implementation time with `git diff` on `ADEQUACY.md` restricted
to the table block: the changed-line count must match the enumerated checklist, and any
additional changed row is an overreach to be reverted.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — §4.1 table (~lines 240-257) and
  a new provenance note immediately after it.

**Verification**:
- Diff read-through confirms every changed hunk lies inside the §4.1 table block or the new note.
- `grep -n "Int.abs_lt_one_iff\|Std.lean:73-80" ADEQUACY.md` returns no hit inside the table.
- Every number written into the table matches the Phase 1 lookup exactly.
- No row outside the enumerated checklist appears in the diff.

---

### Phase 3: Correct the ADEQUACY.md prose sites [NOT STARTED]

**Goal**: The two prose passages outside §4.1 that repeat the corrected citations agree with the
table, and shed their line numbers per Decision D2.

**Tasks**:
- [ ] "Why the design is deterministic" — the **Limit is genuinely non-free** bullet (~line 323)
      currently reads "Over `ℤ` it is discharged trivially
      (`Metalogic/Decidability/WitnessFamily/Std.lean:73-80`, via `Int.abs_lt_one_iff`)". Replace
      the deleted citation with `ShiftSet.ofIntAction` / `ShiftSet.sep_of_succOrder`, cited by
      file and name without a line number.
- [ ] Same bullet, separate item — replace "discharged trivially" with wording that records the
      kernel-checked provenance, matching Phase 2's table verdict. The bullet's own point (that
      `sep` is a structure field rather than a derived fact, proved non-derivable by
      `SepNotDerivable.sep_not_derivable`) is correct and stays.
- [ ] §7.2 "A0 — the frame-class gap" (~lines 713-726) — drop the `:225`, `:236` and `:251, :262`
      suffixes from the three citations there, citing
      `Metalogic/Independence/ZTimeSharpness.lean` by file and declaration name only (the
      existing precedent is `ADEQUACY.md:295`).
- [ ] Confirm the state-sharing passage (~lines 328-342) still reads correctly alongside the
      edits — it already says, correctly, that the real obstruction is Lemma 2 and the Box case,
      not Limit or Saturation. Change nothing there unless the Phase 2/3 edits create an actual
      inconsistency; record that the check was made.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: 2 passages and 4 citation sites are expected to change (1 bullet in "Why the
design is deterministic", 3 citations in §7.2), with the state-sharing passage unchanged. Confirm
by `git diff` hunk count on `ADEQUACY.md` outside the §4.1 block.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — ~line 323 and ~lines 713-726.

**Verification**:
- `grep -n "ZTimeSharpness.lean:2" ADEQUACY.md` returns no hit.
- `grep -n "Int.abs_lt_one_iff\|Std.lean:73-80" ADEQUACY.md` returns no hit anywhere in the file.
- The §4.1 table's Limit verdict and the "Limit is genuinely non-free" bullet make the same claim
  about how the obligation is discharged.

---

### Phase 4: Correct the ARCHITECTURE.md condensed table [NOT STARTED]

**Goal**: `ARCHITECTURE.md`'s condensed mirror of the §4.1 table agrees with the corrected
`ADEQUACY.md`.

**Tasks**:
- [ ] Re-read `ARCHITECTURE.md` immediately before editing (sibling-task territory discipline).
- [ ] Row "1 (Frame)" (~line 181) — replace "with Limit from `Int.abs_lt_one_iff`" with the
      corrected attribution (`ShiftSet.sep_of_succOrder`, through `ShiftSet.ofIntAction`),
      consistent with Phase 2's verdict wording.
- [ ] Same row — update the stale `Semantics/ShiftSet.lean:148,163,171,200,225` citation list to
      the manifest's current `keyword_line` values for `shRel_comp`, `shRel_serial`,
      `shRel_saturation`, `fibre_isRegular`, `frame_isRegular` (Decision D1).
- [ ] Row "3 (Time-shift preservation)" (~line 183) — update `forward_repr`'s stale `:284` and
      tighten `sh_surj`'s `Std.lean:101` to its own `keyword_line`.
- [ ] Assess the row's "all hold **by construction**" phrasing against Row 4's correction: it is
      a claim about the *specific* certified construction (which `ADEQUACY.md:108-127` proves in
      both directions directly), not about `TaskFrame.Limit`'s general transcription, so it needs
      no softening. Record the assessment; soften only if the re-read shows otherwise.
- [ ] Leave `total_eq_orbit` (~lines 182, 191) untouched — upstream marks it "no correction
      needed".

**Timing**: 0.25 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: exactly 2 table rows (~181 and ~183) are expected to change, and no other
line in `ARCHITECTURE.md`. Confirm with `git diff --stat` plus a hunk read-through.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` — ~lines 181 and 183.

**Verification**:
- `grep -n "Int.abs_lt_one_iff" ARCHITECTURE.md` returns no hit.
- Every number written matches the Phase 1 lookup.
- The Limit attribution in `ARCHITECTURE.md:181` and in `ADEQUACY.md`'s §4.1 Limit row name the
  same declarations.

---

### Phase 5: Residue rows and the Limit-transcription note in ADEQUACY.md §4.2 [NOT STARTED]

**Goal**: The three handed-off residue rows each have a recorded outcome in this repository's
adequacy argument, and the Row 4 correction is stated where a reader would otherwise assume
`TaskFrame.Limit` alone transcribes the paper's full set equation.

**Tasks**:
- [ ] Add a §4.2 audit-table row for `worldNonempty`: paper column `—` (the upstream hand-off
      states this row has no paper anchor of its own — the paper's reading of `W` as a **nonempty**
      set is exactly this field, transcribed rather than derived); Lean column naming both
      `FrameOver`'s `worldNonempty` field and the `TaskFrame.worldNonempty` accessor with their
      manifest locations; verdict column recording why it matters — an empty carrier satisfies all
      four constraints vacuously while validating falsehood. Note that this document's own Lemma 1
      proof already relies on `W` being nonempty (`ADEQUACY.md:113`, "`W` is nonempty since
      `k ≥ 0`"), so the transcription decision is load-bearing here too.
- [ ] Add a §4.2 audit-table row for `PartialHistory` / `PartialHistory.IsTotal` /
      `WorldHistory` against the paper anchor `def:world-history`, noting that `TruthAt`'s Box
      clause quantifies over the **total** histories — so the whole Box case rests on this
      transcription. Cross-reference the existing uses at `ADEQUACY.md:266`
      (`joint_countermodel`'s `(τ : WorldHistory F)`) and `:292` (the `box` clause).
- [ ] Add a short reasoned-exclusion note for the `TruthCorr` residue row (upstream row 24),
      preserving its conditional **exactly** as the producing side wrote it rather than
      paraphrasing: the row is reachable only if §4.2 cites the general
      `Truth.truthAt_of_truthCorr` (at `TimeShift.shiftCorr`) rather than the instantiated
      lemma. State that §4.2 cites the instantiated
      `TimeShift.timeShift_preserves_truth` (`ADEQUACY.md:295`), so the condition is unmet and the
      row does not currently apply. Do not change the `:295` citation (Decision D3).
- [ ] Add the Row 4 correction as a short note attached to Lemma 1's *Limit* bullet
      (~lines 121-124): `TaskFrame.Limit` transcribes only the **subset** half of the paper's set
      equation; the superset half — that `w` lies in each of its own positive cones — is
      `lem:nullity`, **derived** choice-free from Seriality together with the subset half via
      `TaskFrame.nullity_of_serial_limit`, not postulated (carrying it as an axiom would duplicate
      a theorem). Make clear the note is about the general Lean transcription, and that the
      concrete certified construction's own proof immediately above establishes both directions
      directly, so nothing in Lemma 1 weakens.
- [ ] Verify the new note does not contradict the "Why the design is deterministic" passage
      (~lines 328-342), which correctly locates the real state-sharing obstruction at Lemma 2 and
      the Box case rather than at Limit or Saturation. Record that the check was made.

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: prose

**Scope Hypothesis**: 2 new §4.2 table rows plus 2 short notes (`TruthCorr` exclusion, Limit
transcription) are expected — 4 additions, 0 deletions, and no change to any existing §4.2 row.
Confirm with `git diff` on `ADEQUACY.md`: every hunk in this phase must be an addition.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — §4.2 table (~lines 286-296),
  a note near `:295`, and Lemma 1's Limit bullet (~lines 121-124).

**Verification**:
- Both new rows carry manifest-resolved locations matching the Phase 1 lookup.
- Row 24's conditional appears in the upstream wording, not a paraphrase.
- No existing §4.2 row, and `ADEQUACY.md:295` in particular, is modified.
- The Limit note and the state-sharing passage are mutually consistent.

---

### Phase 6: Consistency sweep and manifest-resolution check [NOT STARTED]

**Goal**: Confirm the stated acceptance bar — every citation this task touched resolves by name in
the manifest, no retired string survives, and the two documents agree.

**Tasks**:
- [ ] Grep both files for the retired strings: `Int.abs_lt_one_iff`, `Std.lean:73-80`,
      `ZTimeSharpness.lean:225`, `:236`, `:251`, `:262` in the A0 context. Each must return no hit.
- [ ] For every `file.lean:NNN` citation in the changed hunks, confirm the number equals the
      Phase 1 lookup's `keyword_line` for the declaration named in the same row or sentence
      (name-first resolution; numbers are checked against names, never the reverse).
- [ ] Re-run the research report's fresh-scope grep over
      `code/src/model_checker/theory_lib/bimodal/docs/` for every affected declaration name and
      confirm no file other than `ADEQUACY.md` and `ARCHITECTURE.md` carries a line-numbered
      citation needing correction.
- [ ] Read `ADEQUACY.md`'s §4.1 Limit row, the "Limit is genuinely non-free" bullet, and
      `ARCHITECTURE.md:181` side by side: all three must make the same claim about how the Limit
      obligation is discharged.
- [ ] Confirm `~/Projects/BimodalLogic` is unmodified (`git status --porcelain` there is
      unchanged from the start of the task).
- [ ] Confirm no source, test, or gate file in this repository was touched:
      `git status --short` shows only the two documentation files (plus this task's own
      `specs/214_*` artifacts).
- [ ] Record the three residue-row decisions (worldNonempty: added; PartialHistory/WorldHistory:
      added; TruthCorr: reasoned exclusion, condition unmet) in the implementation summary.

**Timing**: 0.5 hours

**Depends on**: 4, 5

**Verification Tier**: prose

**Files to modify**:
- None (verification phase).

**Verification**:
- All retired-string greps return empty.
- Every touched citation resolves by name against the manifest.
- `git status --short` shows exactly the two documentation files plus this task's specs artifacts.
- `~/Projects/BimodalLogic` working tree is untouched.

---

## Testing & Validation

- [ ] `grep -rn "Int.abs_lt_one_iff\|Std.lean:73-80" code/src/model_checker/theory_lib/bimodal/docs/`
      returns nothing.
- [ ] Every `*.lean:NNN` citation in the changed hunks matches the Phase 1 manifest lookup for the
      declaration named alongside it.
- [ ] The freshly re-run scope grep confirms `ADEQUACY.md` and `ARCHITECTURE.md` are still the only
      affected files.
- [ ] `ADEQUACY.md` §4.1, `ADEQUACY.md`'s determinism section, and `ARCHITECTURE.md`'s condensed
      table agree on the Limit discharge.
- [ ] `git status --short` shows only the two documentation files and this task's `specs/214_*`
      artifacts — no source, test, or gate file, and nothing under `~/Projects/BimodalLogic`.
- [ ] No full-theory gate run is required (per the dispatch); none is performed.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — corrected §4.1 table with
  provenance note, corrected prose sites, two new §4.2 residue rows, `TruthCorr` exclusion note,
  Limit-transcription note.
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` — corrected condensed table
  rows.
- `specs/214_apply_upstream_citation_corrections/summaries/01_*-summary.md` — implementation
  summary recording the three residue-row decisions and the Decision D1 scope ruling.
- Per-phase commits, each scoped by explicit file path.

## Rollback/Contingency

Every change is documentation-only and confined to two files, so rollback is per-phase commit
revert: `git revert <phase-commit-sha>` for the offending phase, which leaves earlier phases
intact. Because the phases are ordered so that the §4.1 table (Phase 2) is the reference every
later phase is made consistent with, reverting Phase 2 requires also reverting Phases 3, 4 and 5.

If a rollback of *uncommitted* work is needed instead, take a snapshot first rather than
discarding directly — see `context/contracts/recovery.md`'s rollback rung for the exact
invocation shape, including its out-of-scope override flag. Do not emit a bare reverting
`git-snapshot.sh` call as a routine start-of-phase checkpoint; if a defensive checkpoint is
wanted before Phase 2, use the durable non-reverting `--no-revert` form.

Contingency if Phase 1 finds the manifest moved substantially or a name unresolved: stop before
editing, record which names failed to resolve, and report rather than falling back to the
research report's numbers or re-deriving line numbers by hand — the dispatch forbids hand
re-derivation, and a name that no longer resolves is upstream news, not a local problem.
