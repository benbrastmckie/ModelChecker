# Research Report: Apply Upstream Citation Corrections

- **Task**: 214 - Apply upstream citation corrections
- **Started**: 2026-09-28T18:20:00Z
- **Completed**: 2026-09-28T19:10:00Z
- **Effort**: ~1 hour (mechanical-lookup research, no re-derivation)
- **Dependencies**: None
- **Sources/Inputs**:
  - `~/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md` ("Corrections the
    consuming table owes" table, and the "Hand-off" subsection for the three residue rows)
  - `~/Projects/BimodalLogic/scripts/lean-citation-manifest.json` (generated, C35-gated; 63
    entries, all `"status": "resolved"`)
  - `~/Projects/BimodalLogic/FormalSystem/Semantics/ShiftSet.lean`,
    `.../Metalogic/Decidability/WitnessFamily/Std.lean`,
    `.../Metalogic/Independence/ZTimeSharpness.lean` (read directly to corroborate manifest
    entries and the docstrings explaining *why* each correction is what it is)
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`,
    `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` (this repository, grepped
    fresh for every declaration name named in the corrections table and in the four residue
    rows, per the dispatch's instruction not to trust the described file list)
  - `git log` in `~/Projects/BimodalLogic` to date the two correction clusters relative to task
    214's creation timestamp
- **Artifacts**: this report
- **Standards**: report-format.md, subagent-return.md

## Executive Summary

- All four named corrections resolve cleanly against the manifest by name; exact "before" line
  numbers and "after" manifest data are tabulated below for direct transcription in the plan/
  implement phases. No line number needs to be re-derived by hand.
- **The two Row-2/Row-4 citations each appear at *two* sites in `ADEQUACY.md`, not one.** The
  dispatch's line pointers (~243, ~318-342) name only the §4.1 table row; the same stale
  `Std.lean:73-80`/`Int.abs_lt_one_iff` citation and the same "Limit... by construction" framing
  also recur in the "Why the design is deterministic" section (line 323) and in
  `ARCHITECTURE.md`'s condensed table (line 181). All sites must move together or the two
  documents (and two places within `ADEQUACY.md`) will disagree.
- **Major additional finding, outside the dispatch's four named rows but inside the same upstream
  table and the same two files**: `ADEQUACY.md`'s §4.1 proof-mapping table (lines 241-248) and
  `ARCHITECTURE.md`'s mirrored table (lines 181-185) also carry the upstream table's *second*
  stale-citation cluster (`shRel_comp`, `shRel_serial`, `shRel_saturation`, `fibre_isRegular`,
  `frame_isRegular`, `forward_repr` — all landed one docstring-shift ago) and a *wrong-file*
  citation (`Truth.box_const` cited at `WitnessFamily/Std.lean:101`, but `box_const` is declared
  in `TruthTransport.lean` and does not exist in `Std.lean` at all). This second cluster was
  committed upstream (2026-09-27 19:58) before task 214 was created (2026-09-28 18:11), so it was
  available to whoever wrote the task description; it was not included in the "FOUR ROWS TO
  APPLY" list. Recommendation below.
- **Row 24 (TruthCorr) resolves to "does not currently apply."** `ADEQUACY.md`'s time-shift
  citation (line 295) already cites the *instantiated* lemma
  (`TimeShift.timeShift_preserves_truth`), not the *general* one
  (`Truth.truthAt_of_truthCorr` at `TimeShift.shiftCorr`) that Row 24's hand-off makes the row
  conditional on. No source change is proposed for this task, so the condition is unmet; the
  correct action is a one-line reasoned-exclusion note, not a new audit row.
- Rows 3 and 20 (worldNonempty, PartialHistory/WorldHistory) have no existing audit-table row
  anywhere in either target file today — confirmed by grep — so both are pure additions to
  `ADEQUACY.md` §4.2, exactly as the upstream hand-off frames them.
- Everything found is confined to `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
  and `ARCHITECTURE.md`. No other file in the docs directory (or elsewhere) cites any of the
  affected declaration names with a line number that needs correcting.

## Context & Scope

This is a mechanical-lookup task, not a fresh audit (see the task description's PROVENANCE
section). The producing repository (`~/Projects/BimodalLogic`) completed its own half of a
cross-repository citation-gating pass and recorded, read-only, a "Corrections the consuming table
owes" table plus a "Hand-off" subsection, both keyed by **declaration name** rather than line
number, resolving against its own generated, C35-gated `lean-citation-manifest.json`. Nothing was
written under `~/Projects/ModelChecker` by that pass; this task's job is to apply those
corrections here.

This research phase does not edit any file. Its job is to pin down, precisely and by name, what
is currently wrong at each site in `ADEQUACY.md`/`ARCHITECTURE.md`, what the manifest says the
correct name/location is today, and what decision each of the three residue rows requires — so
the plan/implement phases can apply the corrections directly without re-deriving anything.

Scope is documentation only, confined to `code/src/model_checker/theory_lib/bimodal/docs/`. Per
the dispatch's instruction, the affected file set was derived fresh by grepping the docs
directory for every declaration name in the upstream table (not trusted from the task
description). That grep confirms the affected files are exactly `ADEQUACY.md` and
`ARCHITECTURE.md` — see "Findings: Affected File Set" below for the full negative-result grep.

## Findings

### Affected File Set (derived fresh, not trusted)

```
grep -rln -E "not_validIn_base_prior_UZ|not_validIn_base_z1|prior_UZ_minFrameClass_sharp|
  z1_minFrameClass_sharp|WitnessFamily|ShiftSet|TaskFrame\.Limit|worldNonempty|FrameClass\.Sat|
  nullity_of_serial_limit|sh_surj|std_isZTime|std_sat_ztime|std_sat_base|TruthCorr|
  PartialHistory|WorldHistory|box_const|shiftCorr|timeShift_preserves_truth|
  truthAt_of_truthCorr" code/src/model_checker/theory_lib/bimodal/docs/
```

Hits: `API_REFERENCE.md`, `README.md`, `ADEQUACY.md`, `A2_GAP.md`, `ARCHITECTURE.md`,
`TRUST_PIPELINE.md`, `SETTINGS.md`. Inspecting each hit individually: `API_REFERENCE.md`,
`README.md`, `A2_GAP.md`, `TRUST_PIPELINE.md`, and `SETTINGS.md` mention `WitnessFamily`/
`ShiftSet` only in generic prose (no cited line numbers against any of the affected
declarations) — the one line-cited exception, `TRUST_PIPELINE.md:339`
(`` `ShiftSet.total_eq_orbit` ``), carries no line number at all and needs no change. Only
`ADEQUACY.md` and `ARCHITECTURE.md` contain line-numbered citations against the affected
declarations, confirming the task description's stated scope.

### Row (1): Four stale ZTimeSharpness line citations

Confirmed stale exactly as described. `ZTimeSharpness.lean`'s `not_validOn_z1_dense` theorem
spans roughly lines 211-254 (verified by reading the file); all four old numbers fall inside it.

| Declaration | `ADEQUACY.md` old citation | Manifest-current `keyword_line` (span) |
|---|---|---|
| `not_validIn_base_prior_UZ` | `:225` | `263` (257-268) |
| `not_validIn_base_z1` | `:236` | `274` (269-281) |
| `prior_UZ_minFrameClass_sharp` | `:251` | `289` (282-293) |
| `z1_minFrameClass_sharp` | `:262` | `300` (294-306) |

File for all four: `Metalogic/Independence/ZTimeSharpness.lean` (manifest path
`FormalSystem/Metalogic/Independence/ZTimeSharpness.lean`; `ADEQUACY.md`'s own citation
convention consistently drops the `FormalSystem/` prefix — verified across every existing
citation in the file, so the corrected citations should follow the same convention rather than
introducing the full path).

**Two sites in `ADEQUACY.md`, both wrong, both need the fix**:
- Lines 255-257 (§4.1 table, "A0" rows): `` `Metalogic/Independence/ZTimeSharpness.lean:225` ``,
  `:236`, `:251, :262`.
- Lines 714-725 (§7.2 "A0 — the frame-class gap" discussion): repeats `:225` (line 715), `:236`
  (line 719), and `:251, :262` (line 725).

**Recommended fix, per the dispatch's "prefer names over lines" instruction** (this row is
*exactly* the case that instruction targets — "four of these rows are stale purely because a
docstring edit shifted line numbers underneath them"): drop the explicit `:NNN` suffix and cite
`ZTimeSharpness.lean` by file + declaration name only (the table already names the declaration in
its own column; the prose discussion at lines 714-725 can name the file without a line number
the same way line 295's time-shift citation already does — `` `TimeShift.timeShift_preserves_truth`
(`Semantics/TruthTransport.lean`) `` with no line number at all is an existing precedent in this
same document). If the plan phase prefers to keep numbers for skimmability, the manifest's
`keyword_line` values above (263, 274, 289, 300) are the correct current numbers.

### Row (2): One cited range that no longer exists (WitnessFamily.std's Limit discharge)

The proof this pointed at is gone. Corroborated by reading `Std.lean`'s current docstring
directly (not just the manifest):

> "**Three axioms, not four.** Built through `ShiftSet.ofIntAction`, so the separation field —
> `def:frame#Limit` transcribed over the shift action — is discharged by
> `ShiftSet.sep_of_succOrder` from the zero-shift law rather than proved here by hand. Every
> field *value* is unchanged from the hand-built version this replaces; only the provenance of
> `sep` changed, **from a hand proof over `Int.abs_lt_one_iff` to a kernel-checked consequence of
> discreteness**."

This confirms the verdict genuinely improves, and confirms `Int.abs_lt_one_iff` should be
*removed* from the citation entirely (not merely re-pointed) — it is no longer part of the
discharge path at all, replaced by `ShiftSet.sep_of_succOrder`'s discreteness argument.

New manifest data:

| Declaration | File | `keyword_line` (span) |
|---|---|---|
| `ShiftSet.ofIntAction` | `Semantics/ShiftSet.lean` | `494` (477-506) |
| `ShiftSet.sep_of_succOrder` | `Semantics/ShiftSet.lean` | `472` (455-476) |

**Three sites need this fix, not one** (dispatch names only the first):
- `ADEQUACY.md` line 243, §4.1 table, "Lemma 1, Limit" row: `` "discharged for `std` at
  `Metalogic/Decidability/WitnessFamily/Std.lean:73-80` by `Int.abs_lt_one_iff`" `` -> cite
  `ShiftSet.ofIntAction` / `ShiftSet.sep_of_succOrder`, and change "discharged" framing to state
  the obligation is now kernel-checked (per the row's own instruction: "do not silently swap the
  citation and leave the old weaker verdict standing").
- `ADEQUACY.md` line 323, "Why the design is deterministic" section (the "Limit is genuinely
  non-free" bullet): `` "Over `ℤ` it is discharged trivially
  (`Metalogic/Decidability/WitnessFamily/Std.lean:73-80`, via `Int.abs_lt_one_iff`)." `` — same
  stale citation, same fix. This site was **not named in the dispatch** but cites the identical
  now-deleted range and must move together with line 243 or the document will contradict itself
  about how the Limit obligation is discharged.
- `ARCHITECTURE.md` line 181 (condensed table, "1 (Frame)" row): `` "...with Limit from
  `Int.abs_lt_one_iff`..." `` — also **not named in the dispatch** (the dispatch's SCOPE line
  only flags `ARCHITECTURE.md` for `WitnessFamily.std` and `sh_surj`, not for this Limit phrase),
  but it is the same claim in condensed form and should read "Limit from
  `ShiftSet.sep_of_succOrder`" (or similar) to stay consistent with the corrected `ADEQUACY.md`.

No contradiction was found with the nearby Lemma 1 hand-proof of the *concrete* construction
(`ADEQUACY.md` lines 121-124, proving both directions of the Limit set-equation directly for `W =
{0,…,k} × ℤ`) — that passage proves the equation for the specific certified carrier by direct
calculation and never cites `WitnessFamily.std`'s Lean discharge path, so it needs no change.

### Row (3): Two loose ranges

Manifest data for the five named declarations:

| Declaration | File | `keyword_line` | span |
|---|---|---|---|
| `WitnessFamily.std_isZTime` | `Metalogic/Decidability/WitnessFamily/Std.lean` | 81 | 79-85 |
| `WitnessFamily.std_sat_ztime` | same | 87 | 86-90 |
| `WitnessFamily.std_sat_base` | same | 92 | 91-95 |
| `WitnessFamily.sh_surj` | same | 98 | 96-101 |
| `ProofSystem.FrameClass.Sat` | `Semantics/FrameClassValidity.lean` | 151 | 100-217 |

**Current `ADEQUACY.md` citations and what they actually resolve to**:
- Line 246: `` `Metalogic/Decidability/WitnessFamily/Std.lean:84, 91, 96` `` for
  `std_isZTime`/`std_sat_ztime`/`std_sat_base` respectively. Checked against the spans above:
  `:84` is inside `std_isZTime`'s own span (loose-but-correct, as the upstream table says). `:91`
  and `:96`, however, each fall inside the **next** declaration's span (`:91` is inside
  `std_sat_base`'s span 91-95, not `std_sat_ztime`'s 86-90; `:96` is inside `sh_surj`'s span
  96-101, not `std_sat_base`'s 91-95) — i.e. positionally shifted by one. Whether the upstream
  table's framing ("two cited ranges are loose... correct under the span convention") is meant to
  cover this exact shift or just the FrameClass.Sat case is genuinely ambiguous from the text
  alone; either way, the manifest resolves it cleanly: use each name's own `keyword_line` (81,
  87, 92) or its own span, not the old `84, 91, 96` grouping.
- Line 248: `` `Metalogic/Decidability/WitnessFamily/Std.lean:101` `` for `sh_surj` — `:101` is
  `sh_surj`'s own `span_end`, so this one is loose-but-correct exactly as described.
- `ADEQUACY.md` line 291 / §4.2 table: `` `Semantics/FrameClassValidity.lean:152` `` for
  `FrameClass.Sat` — `152` is one line past `keyword_line` 151 (the very next match-arm line
  inside the `def`'s body), well within the 100-217 span. This is loose-but-correct and does not
  strictly need changing, though citing `151` (the keyword line itself) would be tighter.
- `ARCHITECTURE.md`: no citation of `FrameClass.Sat` was found (only `FrameClass.ZTime.Sat`/
  `FrameClass.Base.Sat` used as inline notation, never cited with a line number).

**Recommendation**: for the three-name grouped citation at `ADEQUACY.md:246`, switch to citing
each name against its own `keyword_line` (81, 87, 92) — this directly repairs the one-position
shift noted above, independent of how the upstream table's "loose" framing is read. Leave
`sh_surj` (line 248) and `FrameClass.Sat` (line 291) as-is, or tighten to `98` and `151`
respectively if the plan phase wants numeric consistency across the row.

### Row (4): The Limit verdict is too strong (substantive correction)

Confirmed: `TaskFrame.Limit` (`Semantics/TaskFrame.lean`, `keyword_line` 828, span 808-830)
transcribes only the `⊆` half; `TaskFrame.nullity_of_serial_limit` (same file, `keyword_line`
941, span 916-964) derives the `⊇` half — "`w` lies in each of its own positive cones" — choice-
free from Seriality together with the `⊆` half. Neither of these two declaration names is
currently cited anywhere in `ADEQUACY.md` or `ARCHITECTURE.md` (confirmed by grep: no hit for
`TaskFrame.Limit` or `nullity_of_serial_limit` in either file). This means the correction is not
"fix a wrong citation" but "state the correction" — i.e. wherever the surrounding prose currently
implies or asserts that the frame construction's Limit obligation transcribes the *full* set
equation, that claim needs softening, even though no line-numbered citation of `TaskFrame.Limit`
itself needs to move.

Candidate sites carrying language that could be read as claiming the full equation:
- `ADEQUACY.md` line 68 (§2 statement): `` "Compositionality, Seriality, Limit and Saturation
  (`:989-994`)" `` — this cites the paper's own definitions, not `TaskFrame.Limit`'s Lean
  transcription specifically; it is a statement about what the obligations *are*, not a claim
  about which half Lean proves. No change needed.
- `ADEQUACY.md` lines 121-124 (Lemma 1's hand proof): proves the full set-equation directly for
  the *concrete* certified construction (`W = {0,…,k} × ℤ`), not through `TaskFrame.Limit`/
  `nullity_of_serial_limit` at all — a self-contained calculation. No change needed (already
  discussed under Row 2 above).
- `ARCHITECTURE.md` line 181: `` "compositionality, seriality, Limit, and Saturation all hold
  **by construction**" `` — this is about the *specific* certified `WitnessFamily.std`
  construction (which does satisfy the full equation directly, per Lemma 1's proof), not a
  general claim about `TaskFrame.Limit`'s transcription — arguably does not need softening either,
  though the "Limit from `Int.abs_lt_one_iff`" clause immediately following it is already being
  corrected under Row 2 above.

**Conclusion**: this repository's `ADEQUACY.md`/`ARCHITECTURE.md` do not currently contain a
statement that specifically over-claims `TaskFrame.Limit`'s Lean-side transcription as the full
equation — the closest such statements are all about the concrete certified construction
(verified true for both directions by direct proof) rather than about `TaskFrame.Limit`'s general
definition. **No edit is strictly required for Row 4 as a standalone item**, but if the plan
phase wants to state the correction defensively (matching the upstream table's own phrasing, and
useful if a future reader assumes `TaskFrame.Limit` alone is Lean's transcription), a short note
naming `TaskFrame.Limit` (⊆ only) and `TaskFrame.nullity_of_serial_limit` (⊇, derived from
Seriality, not postulated) could be added near `ADEQUACY.md` lines 108-127 (Lemma 1's Limit
bullet) — this is exactly the kind of addition the upstream hand-off's §4.2 residue-row
convention would use, though it is not one of the three named residue rows.

**Consistency check with the state-sharing discussion** (dispatch explicitly asked for this):
`ADEQUACY.md` lines 308-342 ("Why the design is deterministic") already state, independently and
correctly, that "the real obstruction to state-sharing is not Limit or Saturation — it is Lemma 2
and the Box case" (line 328). This is fully consistent with Row 4's correction (Limit's `⊇` half
being derived rather than postulated does not change where the state-sharing obstruction lives);
no conflict found, no change needed to that passage beyond the citation fix already covered under
Row 2 (line 323 cites the same deleted range).

### Residue Row: `worldNonempty` (upstream row 3)

No existing row or citation anywhere in either file (confirmed by grep for `worldNonempty`).
Manifest data:

| Declaration | File | `keyword_line` | span | field |
|---|---|---|---|---|
| `FrameOver` (`worldNonempty` field) | `Semantics/TaskFrame.lean` | 1055 | 1003-1086 | `worldNonempty` |
| `TaskFrame.worldNonempty` (accessor) | `Semantics/TaskFrame.lean` | 2642 | 2641-2643 | — |

No paper anchor (upstream states this explicitly: "no paper anchor of its own — the row records
that the paper's reading of `W` as nonempty is exactly this field, transcribed rather than
derived"). This repository's own Lemma 1 proof (`ADEQUACY.md` line 113) already asserts "`W` is
nonempty since `k ≥ 0`" as a proof step, so the underlying fact is already load-bearing here too
— it is a genuine gap that this document's own §4.2 table does not audit the transcription
decision behind it. **Recommendation: add as a new §4.2 row**, following the upstream hand-off's
exact phrasing (paper column: "—"; Lean column naming both the field and the accessor; verdict
column noting the vacuous-satisfaction risk of an empty carrier).

### Residue Row: `PartialHistory`/`WorldHistory`/`IsTotal` (upstream row 20)

No existing audit row (confirmed by grep for `PartialHistory`), but `WorldHistory` itself is
**already used** in this document's own cited theorem statements — `ADEQUACY.md` line 266
(`joint_countermodel`'s signature: `` (τ : WorldHistory F) ``) and line 292 (`TruthAt`'s `box`
clause: `` ∀ σ : WorldHistory F, TruthAt M σ t φ ``) — so this residue row is directly relevant to
claims this document already relies on, not a hypothetical addition. Manifest data:

| Declaration | File | `keyword_line` | span |
|---|---|---|---|
| `PartialHistory` | `Semantics/PartialHistory.lean` | 136 | 125-168 |
| `PartialHistory.IsTotal` | same | 225 | 211-226 |
| `WorldHistory` | same | 423 | 409-429 |

Paper anchor: `def:world-history` (same anchor the upstream page's own row 20 cites).
**Recommendation: add as a new §4.2 row**, noting (per the upstream hand-off) that the Box clause
of `TruthAt` quantifies over the *total* histories, so the whole Box case rests on this
transcription — directly relevant to the "Box case" language this document's own "Why the design
is deterministic" section (lines 328-342) already discusses at length.

### Residue Row: `TruthCorr` (upstream row 24) — conditional, currently NOT triggered

Upstream's hand-off is explicit that this row is reachable **only if** `ADEQUACY.md`'s §4.2 cites
the *general* time-shift lemma (`Truth.truthAt_of_truthCorr` at `TimeShift.shiftCorr`) rather than
the *instantiated* one. Checked directly: `ADEQUACY.md` line 295 currently cites
`` `TimeShift.timeShift_preserves_truth` (`Semantics/TruthTransport.lean`), consumed by
`ShiftSet.reverse_repr` and `modal_future_valid` `` — this is the **instantiated** lemma, per the
upstream corrections table's own row distinguishing the two readings. No change to that citation
is in scope for this task (switching it is a separate, unrequested correction with its own
consequences — it would pull `TruthCorr`'s five fields into the audit).

**Decision, recorded per the task's explicit instruction to "decide, and record"**: Row 24 does
**not** currently apply to this repository's adequacy argument, because the condition it is
predicated on is unmet. The existing `app:auto_existence` position at `ADEQUACY.md` line 288
("not needed: Corollary 2.1 derives it") already stands and is not contradicted. **Recommendation:
add a short explanatory note (not a full audit row) near line 295 or in §4.2**, stating that
`TruthCorr` and its fields are out of scope for this document's residue because §4.2 cites the
instantiated lemma, not the general form — this preserves the conditional framing exactly, as the
task requires, rather than silently doing nothing (which would look like an oversight to a future
reader who knows about Row 24) or silently adding a row that does not apply.

Manifest data for `TruthCorr`, recorded here in case a future pass switches the citation:
`FormalSystem.Semantics.TruthCorr`, file `Semantics/TruthTransport.lean`, `keyword_line` 92, span
77-106.

### Additional finding: the upstream table's second stale-citation cluster also affects both files

Not named in the task description's "FOUR ROWS TO APPLY," but present in the same upstream
"Corrections the consuming table owes" table (committed 2026-09-27 19:58, before task 214 was
created at 2026-09-28 18:11) and directly verifiable in both `ADEQUACY.md` and `ARCHITECTURE.md`
by the same mechanical-lookup method used for the four named rows:

**Seven citations stale the same way as Row 1** (landed inside a neighbouring declaration after
one docstring-insertion shift):

| Declaration | Current citation (`ADEQUACY.md`/`ARCHITECTURE.md`) | Manifest `keyword_line` (span) |
|---|---|---|
| `ShiftSet.shRel_comp` | `:148` | `157` (156-170) |
| `ShiftSet.shRel_serial` | `:163` | `172` (171-177) |
| `ShiftSet.shRel_saturation` | `:171` | `180` (178-183) |
| `ShiftSet.fibre_isRegular` | `:200` | `209` (206-214) |
| `ShiftSet.frame_isRegular` | `:225` | `234` (231-235) |
| `ShiftSet.forward_repr` | `:284` | `293` (286-322) |

Cited at `ADEQUACY.md` lines 241-245, 248 (§4.1 table) and `ARCHITECTURE.md` lines 181, 183
(condensed table) — the same table rows already being touched for the `sep`/Limit fix (Row 2) and
the loose-range fix (Row 3), so these stale citations sit immediately adjacent to corrections this
task is already making.

**One wrong-file citation**: `Truth.box_const` is cited at `ADEQUACY.md:248` alongside `sh_surj`
at `` `Metalogic/Decidability/WitnessFamily/Std.lean:101` ``, but `box_const` is declared in
`Semantics/TruthTransport.lean` (`keyword_line` 310, span 292-319) and does not exist in
`Std.lean` at all. The upstream table's own instruction: "split the row's second citation in two
— `box_const` and `sh_surj` each get their own location from the manifest, resolved against their
own (different) files."

**Two further loose-but-correct citations, no action needed**: `ShiftSet#sep` (the field) and
`ShiftSet.total_eq_orbit` — upstream's own table marks these "no correction needed"; verified the
`total_eq_orbit` citations at `ADEQUACY.md:247, 330` and `ARCHITECTURE.md:182, 191` carry no stale
line-number problem.

**Why this matters for this task specifically**: leaving this second cluster unfixed while
correcting the four named rows means the same §4.1/condensed-table rows in both files will still
contain stale line numbers immediately next to the newly-corrected ones — a future reader (or the
next C35-style audit, if one is ever built on this side per the upstream page's "deferred
cross-repository proposal") would find half the table fixed and half still wrong, in the same
rows. This was not requested by the task description and is called out here as a recommendation,
not applied, and not treated as blocking (see Decisions below).

## Decisions

- **No file edits were made in this research phase** — this is a research-only dispatch; all
  findings above are recommendations and exact "before/after" data for the plan/implement phases.
- **Row 4 requires no line-citation change**, only an optional defensive note, because neither
  `TaskFrame.Limit` nor `nullity_of_serial_limit` is currently cited by name anywhere in either
  target file, and the passages that could be read as over-claiming are actually about the
  concrete certified construction (independently proved both directions), not about
  `TaskFrame.Limit`'s general transcription.
- **Row 24 (TruthCorr) is recorded as a reasoned exclusion, not an addition**, because
  `ADEQUACY.md` line 295 cites the instantiated time-shift lemma, not the general one the row's
  hand-off makes it conditional on. This is not escalated as a `user_decision` — the citation is
  unambiguous and the resolution follows directly from reading it, requiring no external
  preference or judgment call the artifacts cannot supply.
- **The second stale-citation cluster is flagged as a strong recommendation, not silently
  expanded into scope.** The task description explicitly enumerates "FOUR ROWS TO APPLY" and
  named residue rows; nothing in the dispatch or task description asks for the second cluster.
  Given the SCOPE section's own instruction to "derive the affected file set fresh... rather than
  trusting this list," and given the second cluster sits in the exact same table rows as fixes
  already required, the recommendation is to include it in the same implementation pass — but
  this is left for the plan phase to decide and scope explicitly (e.g. as an additional phase or
  an explicitly noted exclusion), not assumed here.

## Recommendations

1. Apply Rows 1-3 as tabulated above, at all sites identified (including the two sites the
   dispatch did not separately name: `ADEQUACY.md:323` for Row 2, and `ARCHITECTURE.md:181` for
   both Row 2's `Int.abs_lt_one_iff` phrase and the second-cluster staleness).
2. For Row 1 and the second cluster, prefer name-only citations (drop the `:NNN` suffix) per the
   dispatch's own "prefer names over lines" instruction — these are the rows where a future
   docstring edit will repeat the exact same drift if a hard-coded number is left behind.
3. Add the `worldNonempty` and `PartialHistory`/`WorldHistory` rows to `ADEQUACY.md` §4.2's audit
   table, using the paper anchors and phrasing the upstream hand-off already supplies verbatim.
4. Add a short reasoned-exclusion note for `TruthCorr` (Row 24) rather than an audit row, since
   the triggering condition is unmet.
5. Decide explicitly (plan phase) whether the second stale-citation cluster and the `box_const`
   wrong-file citation are in scope for this task's implementation pass or deferred to a
   follow-up task; either choice should be stated in the plan rather than left implicit, since
   the citations are already known-wrong and sit in rows this task is already editing.
6. Do not touch the `ADEQUACY.md:295` time-shift citation (instantiated vs. general lemma) — that
   choice is out of scope; changing it would trigger Row 24 and pull `TruthCorr`'s five fields
   into the audit as an unrequested side effect.

## Risks & Mitigations

- **Risk**: applying only the §4.1 table fix for Row 2 (line 243) while missing the duplicate at
  line 323 would leave `ADEQUACY.md` internally inconsistent about how `std`'s Limit obligation is
  discharged. **Mitigation**: both sites are listed explicitly above; the plan should name both.
- **Risk**: the manifest's line numbers are a generated, moving view ("Cite the `name` field; the
  line numbers here are a derived view and are expected to move" — the manifest's own `note`
  field). If the BimodalLogic tree moves again before implementation, the exact `keyword_line`
  values above could be stale by the time they are applied. **Mitigation**: the implement phase
  should re-resolve each name against a fresh read of the manifest immediately before editing,
  exactly as the dispatch instructs, rather than trusting this report's numbers as final —
  declaration names, not line numbers, are the load-bearing part of every recommendation above.
- **Risk**: partially fixing the §4.1 table (four named rows) while leaving the second cluster's
  stale citations in the same rows could look like an incomplete or careless edit to a future
  reviewer. **Mitigation**: Recommendation 5 above asks the plan phase to make an explicit,
  recorded choice either way.

## Context Extension Recommendations

- **Topic**: cross-repository citation-manifest consumption.
- **Gap**: nothing in this repository currently reads BimodalLogic's generated
  `lean-citation-manifest.json` to detect citation drift automatically; every correction here was
  found by manual grep + manifest lookup. The upstream page's own "deferred cross-repository
  proposal" section names this exact gap and sketches the fix (a consuming-side check resolving
  `BIMODAL_LOGIC_PATH` or `~/Projects/BimodalLogic`, analogous to its own C35).
- **Recommendation**: not for this task (out of `file_scope`, and the upstream page explicitly
  defers it), but worth a future `general` or `meta` task if citation drift recurs — a script
  under `code/scripts/` that resolves the BimodalLogic checkout and cross-checks
  `ADEQUACY.md`/`ARCHITECTURE.md`'s `file.lean:NNN` citations by name against the manifest,
  skipping cleanly when no checkout is present (mirroring `_lean_check.py`'s existing skip
  discipline).

## Appendix

### Manifest paths vs. this repository's citation convention

The manifest's `file` field is repo-relative to `~/Projects/BimodalLogic` and includes the
`FormalSystem/` prefix (e.g. `FormalSystem/Semantics/ShiftSet.lean`). `ADEQUACY.md`/
`ARCHITECTURE.md` consistently omit that prefix in every existing citation (e.g.
`Semantics/ShiftSet.lean:520`, `Metalogic/Independence/ZTimeSharpness.lean:225`). Corrections
should follow the existing convention (drop `FormalSystem/`), not the manifest's raw path.

### Full manifest entries consulted (name, file, keyword_line, span)

```
FormalSystem.Metalogic.Decidability.WitnessFamily.std                         Std.lean            72  (59-78)
FormalSystem.Metalogic.Decidability.WitnessFamily.std_isZTime                 Std.lean            81  (79-85)
FormalSystem.Metalogic.Decidability.WitnessFamily.std_sat_ztime               Std.lean            87  (86-90)
FormalSystem.Metalogic.Decidability.WitnessFamily.std_sat_base                Std.lean            92  (91-95)
FormalSystem.Metalogic.Decidability.WitnessFamily.sh_surj                     Std.lean            98  (96-101)
FormalSystem.ProofSystem.FrameClass.Sat                                       FrameClassValidity.lean 151 (100-217)
FormalSystem.Metalogic.Independence.not_validIn_base_prior_UZ                 ZTimeSharpness.lean 263 (257-268)
FormalSystem.Metalogic.Independence.not_validIn_base_z1                       ZTimeSharpness.lean 274 (269-281)
FormalSystem.Metalogic.Independence.prior_UZ_minFrameClass_sharp              ZTimeSharpness.lean 289 (282-293)
FormalSystem.Metalogic.Independence.z1_minFrameClass_sharp                    ZTimeSharpness.lean 300 (294-306)
FormalSystem.Semantics.FrameOver (worldNonempty field)                        TaskFrame.lean      1055 (1003-1086)
FormalSystem.Semantics.TaskFrame.worldNonempty                                TaskFrame.lean      2642 (2641-2643)
FormalSystem.Semantics.TaskFrame.Limit                                        TaskFrame.lean      828  (808-830)
FormalSystem.Semantics.TaskFrame.nullity_of_serial_limit                      TaskFrame.lean      941  (916-964)
FormalSystem.Semantics.ShiftSet.sep_of_succOrder                              ShiftSet.lean       472  (455-476)
FormalSystem.Semantics.ShiftSet.ofIntAction                                   ShiftSet.lean       494  (477-506)
FormalSystem.Semantics.ShiftSet.shRel_comp                                    ShiftSet.lean       157  (156-170)
FormalSystem.Semantics.ShiftSet.shRel_serial                                  ShiftSet.lean       172  (171-177)
FormalSystem.Semantics.ShiftSet.shRel_saturation                              ShiftSet.lean       180  (178-183)
FormalSystem.Semantics.ShiftSet.fibre_isRegular                               ShiftSet.lean       209  (206-214)
FormalSystem.Semantics.ShiftSet.frame_isRegular                               ShiftSet.lean       234  (231-235)
FormalSystem.Semantics.ShiftSet.forward_repr                                  ShiftSet.lean       293  (286-322)
FormalSystem.Semantics.Truth.box_const                                       TruthTransport.lean  310  (292-319)
FormalSystem.Semantics.TimeShift.timeShift_preserves_truth                    TruthTransport.lean  254  (238-263)
FormalSystem.Semantics.Truth.truthAt_of_truthCorr                             TruthTransport.lean  122  (107-187)
FormalSystem.Semantics.TimeShift.shiftCorr                                    TruthTransport.lean  228  (218-237)
FormalSystem.Semantics.TruthCorr                                              TruthTransport.lean  92   (77-106)
FormalSystem.Semantics.PartialHistory                                        PartialHistory.lean  136  (125-168)
FormalSystem.Semantics.PartialHistory.IsTotal                                 PartialHistory.lean  225  (211-226)
FormalSystem.Semantics.WorldHistory                                          PartialHistory.lean  423  (409-429)
```

### `ADEQUACY.md` / `ARCHITECTURE.md` line references gathered during this research

- `ADEQUACY.md`: 42, 68, 77, 106, 108-127, 233-234, 240-257, 260-282, 282-300 (§4.2 table), 291,
  292, 295, 308-342 ("Why the design is deterministic"), 349-359, 366-370, 714-726.
- `ARCHITECTURE.md`: 7, 40, 67, 96, 141, 163, 175-192, 279, 289, 338.
