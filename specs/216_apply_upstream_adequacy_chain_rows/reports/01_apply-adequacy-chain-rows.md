# Research Report: Apply Upstream A1 / A1-Γ / A3 Adequacy-Chain Rows

- **Task**: 216 - Apply upstream adequacy chain rows
- **Started**: 2026-09-29
- **Completed**: 2026-09-29
- **Effort**: research only, ~2 hours
- **Dependencies**: None blocking. Sibling task (research phase, this same cycle) declares
  `code/src/model_checker/theory_lib/bimodal/examples.py` as its file scope; this research read
  that file (for the premise/conclusion inventory) but recommends no edit to it.
- **Sources/Inputs**:
  - Provenance note (read-only, not edited): `~/Projects/BimodalLogic/specs/693_a1_compression_conformance_adequacy_chain/handoff-a1-adequacy-rows.md`
  - Cited report (read-only): `~/Projects/BimodalLogic/specs/693_.../reports/01_a1-compression-conformance.md`
  - This repository's live documents: `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`,
    `.../docs/TRUST_PIPELINE.md`, `.../bimodal/examples.py`
  - Live BimodalLogic tree (read-only verification, not edited): `FormalSystem/Metalogic/Decidability/WitnessFamily/{Basic,Predicates,Agreement,Decide,Std,Examples}.lean`,
    `WitnessFamily/Compression/{Types,Cycle,Fulfil,Extract,Family,Enumerate,Assembly}.lean`,
    `scripts/lean-citation-manifest.json`, `scripts/lean-citation-seeds.txt`,
    `scripts/check-module-invariants.sh`, `lakefile.toml`
- **Artifacts**: this report
- **Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The upstream hand-off is current, not stale.** BimodalLogic's own task that produced the
  hand-off note has since completed all its planned phases: the 23-name citation-manifest seed
  block is landed and gate-green (`C35 PASS — 86 seeded declaration(s) resolve`), and the two
  "needs a deduction theorem" docstrings the note flagged as over-stated have already been
  corrected in that repository. Every declaration this task needs to cite was independently
  re-resolved against the live tree during this research (not merely taken from the note) and
  every one resolves, at the file recorded in `scripts/lean-citation-manifest.json`.
- **Every existing `WitnessFamily/`-anchored citation in both documents has already drifted from
  its cited line** — not just the one `joint_countermodel` occurrence the dispatch names. This
  research measured the drift directly (see Findings 2) and confirms the case for dropping line
  numbers document-wide for this subtree, not only at the two named occurrences.
- **The three component rows, the two TRUST_PIPELINE.md corrections, and the citation-convention
  migration are all independently actionable now.** This report supplies copy-ready replacement
  text for every edit site, written to the dispatch's STYLE CONSTRAINT (current status only, no
  transition narrative, no dated language).
- **One consistency gap beyond the dispatch's literal item list**: `TRUST_PIPELINE.md`'s A-component
  table still labels A1 "Open — route named, owned by the Lean development," which contradicts
  ADEQUACY.md's corrected A1 row exactly as Item 2 describes for A3. Recommended (not mandatory
  per the dispatch's literal text) as an additional row update, flagged explicitly below.
- **Scope check on Item 3 confirms the migration is document-wide, not confined to section 7.**
  The dispatch's own VERIFICATION clause ("no line-number anchor to the WitnessFamily/Compression
  subtree survives") and its worked example (`joint_countermodel` cited "in two places," neither
  of which is in section 7) both point to a document-wide sweep. This report enumerates every
  site in both documents.

## Context & Scope

This is a research pass ahead of the plan/implement phases that will actually edit
`ADEQUACY.md` and `TRUST_PIPELINE.md`. Nothing in this repository or in BimodalLogic was
modified. The goal is to (a) independently verify every claim and every declaration name the
upstream hand-off note relies on against the live BimodalLogic tree, (b) locate every citation
site in both target documents that the dispatch's three items touch, and (c) produce exact,
copy-ready replacement text — table rows, prose paragraphs, and a full citation-conversion table —
so the plan/implement phases can apply the edits without re-deriving any of this.

## Findings

### 1. Verification: every cited declaration resolves in the live BimodalLogic tree

All declarations below were independently re-resolved by `grep`-locating each `def`/`theorem`
signature in the live tree and cross-checked against `scripts/lean-citation-manifest.json`
(regenerated, gate `C35` green: "all 86 seeded declaration(s) resolve at the recorded file,
keyword line and span").

| Declaration | Current file (per manifest) |
|---|---|
| `LabelledLasso` | `Metalogic/Decidability/WitnessFamily/Basic.lean` |
| `LabelledLasso.lab` | `Metalogic/Decidability/WitnessFamily/Basic.lean` |
| `WitnessFamily.LocalCoherentLab` | `Metalogic/Decidability/WitnessFamily/Predicates.lean` |
| `WitnessFamily.FulfillingLab` | `Metalogic/Decidability/WitnessFamily/Predicates.lean` |
| `WitnessFamily.BoxFaithful` | `Metalogic/Decidability/WitnessFamily/Predicates.lean` |
| `WitnessFamily.Target` | `Metalogic/Decidability/WitnessFamily/Predicates.lean` |
| `WitnessFamily.Certifies` | `Metalogic/Decidability/WitnessFamily/Predicates.lean` |
| `WitnessFamily.joint_countermodel` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| `WitnessFamily.refutes_of_certifies` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| `WitnessFamily.Refutes` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| `cycleBoundC`, `midBoundC`, `compressionBound` | `WitnessFamily/Compression/{Cycle,Extract,Extract}.lean` |
| `exists_labelledLasso_of_history_realized`, `exists_labelledLasso_of_history` | `WitnessFamily/Compression/Extract.lean` |
| `boxedPart`, `exists_witnessFamily_of_not_validZTime`, `semanticConsequenceIn_nil_iff` | `WitnessFamily/Compression/Family.lean` |
| `cands`, `mem_cands_of_bounded` | `WitnessFamily/Compression/Enumerate.lean` |
| `validZTime_iff_noCertifiedCandidate`, `Compression.decidableValidZTime`, `decidableSemanticConsequenceNil` | `WitnessFamily/Compression/Assembly.lean` |

Also independently confirmed, not part of the seeded 23 but cited today in `ADEQUACY.md`/
`TRUST_PIPELINE.md`: `WitnessFamily.std`, `std_isZTime`, `std_sat_ztime`, `std_sat_base`,
`sh_surj` (`WitnessFamily/Std.lean`); `untl_mem_of_witness`, `snce_mem_of_witness`,
`shiftTruth_iff_mem`, `truth_iff_mem`, `not_consequence_ztime`, `not_consequence_base`
(`WitnessFamily/Agreement.lean`); `no_witnessFamily_of_MF` (`WitnessFamily/Examples.lean`);
`coherent_iff_window`, `fulfil_iff_window`, `mem_all_iff_window`, `scan_forward`,
`scan_backward`, `decidableLocalCoherentLab`, `decidableFulfillingLab`, `decidableBoxFaithful`,
`decidableTarget` (`WitnessFamily/Decide.lean`); `nb`, `nm`, `nf`, `lab_sub_back_length`,
`lab_add_fwd_length` (`WitnessFamily/Basic.lean`). Every one resolves.

`lakefile.toml` declares fourteen `[[lean_exe]]` targets; the only one touching certificate
checking is `BimodalTools.CheckCertificateMain` (`root = "BimodalTools.CheckCertificateMain"`),
which checks a *supplied* certificate — confirming there is no executable target for the
enumerator, as the hand-off note states.

### 2. The drift is not confined to the one cited occurrence — it is the norm, not the exception

The dispatch names one measured drift (`joint_countermodel`, cited at `Agreement.lean:232`,
now at line 248). This research checked every other WitnessFamily-subtree citation currently in
the two documents and found the same pattern throughout:

| Declaration | Document's cited line | Live line | Drift |
|---|---|---|---|
| `WitnessFamily.std` | 65 | 72 | +7 |
| `WitnessFamily.joint_countermodel` | 232 (×2 in ADEQUACY.md, ×1 in TRUST_PIPELINE.md) | 248 | +16 |
| `not_consequence_ztime` / `not_consequence_base` | 203, 219 | 219, 235 | +16 |
| `coherent_iff_window` | 335 | 336 | +1 |
| `fulfil_iff_window` | 743 | 744 | +1 |
| `mem_all_iff_window` (lasso / family) | 809, 883 | 810, 884 | +1 |
| `decidableLocalCoherentLab` / `FulfillingLab` / `BoxFaithful` / `Target` | 865, 878, 923, 927 | 866, 879, 924, 928 | +1 |

`std_isZTime`, `std_sat_ztime`, `std_sat_base`, `sh_surj`, `scan_forward`, `scan_backward` are the
only currently-cited lines still exactly correct. This is exactly the failure mode the dispatch
describes: every gate in both repositories stayed green throughout this drift, because no gate
reads these particular line numbers. It confirms the scope of Item 3 is document-wide (see
Finding 4), not limited to the two `joint_countermodel` occurrences named as the motivating
example.

### 3. The BimodalLogic-side work behind the hand-off note is complete, not proposed

`git log` in BimodalLogic shows the producing task ran to completion (phases 1–4, then a final
"complete implementation" commit) after the hand-off note was written:

- The 23-name seed block (Recommendation 3 of the cited report) is landed in
  `scripts/lean-citation-seeds.txt` (63 → 86 names) and the manifest regenerated;
  `check-module-invariants.sh`'s `C35` reports **PASS**, byte-current.
- The two "needs a deduction theorem" docstrings (Recommendation 6) were corrected in
  `Compression/Assembly.lean` and `Compression/README.md` — the summary records three passages
  found and corrected, not two, and confirms each now scopes the deduction-theorem obstruction to
  the *reduction* route only, matching Finding 2c of the cited report.

This matters for this task: the "name + manifest convention" is not aspirational for the
declarations this task cites — every one of them is already a resolving, gate-checked manifest
entry today.

### 4. Scope of Item 3: which citations are in scope, which are not

"WitnessFamily/ and Compression/ citations" scopes to file paths under
`Metalogic/Decidability/WitnessFamily/` (including its `Compression/` subdirectory). Citations to
`Metalogic/Decidability/BiLasso/*.lean` (e.g. `exists_annot_of_truth`, `Enumerate.lean`,
`TruthLemma.lean`, `Annotation.lean` in §7.1), `Semantics/*.lean`, `Metalogic/Independence/*.lean`,
`Metalogic/Soundness.lean`, and `ProofSystem/Axioms.lean` are a **different subtree** and are
**out of scope** — the dispatch's Item 3 and the cited report's Recommendation 2 both name only
`WitnessFamily/`-and-`Compression/`. This keeps the migration bounded: every anchor listed in
Finding 2's table converts; nothing else in either document does.

### 5. Copy-ready replacement text

All text below is written to the STYLE CONSTRAINT: current status only, present tense, no
"moves from X to Y," no "recently," no dated language, no task-number citations. Scope
restrictions (non-empty premises, `MD_CM_1`'s two conclusions, the `back`/`fwd` vs. `mid`
asymmetry) are kept as standing facts, not history.

#### 5a. `ADEQUACY.md` §7 component table (replaces the current A1 row, inserts A1-Γ, replaces A3; A0 and A2 untouched)

```markdown
| **A1** | Compression: a ℤ-time countermodel yields a certificate with lengths bounded by `f(\|C\|)` | **Partially discharged, at the empty-premise, single-conclusion instance.** `exists_witnessFamily_of_not_validZTime` (`Metalogic/Decidability/WitnessFamily/Compression/Family.lean`) takes `¬ ValidZTime φ` to a `WitnessFamily [] [φ]` and a target time satisfying exactly (C1)–(C4), with every lasso's three segment lengths and the target time bounded by `compressionBound [] [φ]`, at most `\|C\| + 1` lassos, and a canonically enumerable box guess `fun χ => decide (χ ∈ S)` for an explicit `S ⊆ C`. `compressionBound Γ Del = max ((2k+1)·2^k) (2·2^k)` at `k = \|closureOf (Γ ++ Δ)\|` — a bound in the closure size alone, checked by `rfl` — via a pigeonhole over subformula-set space (`TypeState C`, cardinality `2^\|C\|`), not over presentation states. Sorry-free; axiom closure `{propext, Classical.choice, Quot.sound}`. **The general `Γ ⊨ σ` form this chain consumes is a separate, open obligation — see A1-Γ.** §7.1. |
| **A1-Γ** | Compression at non-empty premises and multiple conclusions: `¬ SemanticConsequenceIn FrameClass.ZTime Γ σ` for arbitrary finite `Γ`, target `Δ` a finite list | **Open, and this is the form (ADEQ) consumes.** The landed instance is at `Γ = []`, `Δ = [φ]`; every countermodel example in `examples.py` has a non-empty premise list, and `MD_CM_1` has `\|Δ\| = 2`. A1's "equivalently `¬ SemanticConsequenceIn FrameClass.ZTime Γ σ`" phrasing needs a context-conjunction deduction theorem; the only landed bridge, `semanticConsequenceIn_nil_iff`, covers `Γ = []` only. The residue is bounded: `WitnessFamily.Refutes`, `refutes_of_certifies`, `joint_countermodel`, `exists_labelledLasso_of_history_realized`, `compressionBound`, and all four `Decidable` instances are already stated at arbitrary `Γ Del`. §7.1a. |
| **A3** | Bound realization: configured `back`/`fwd` are common multiples of the compressed family's periods (each bounded by `f(\|C\|)`), and `mid` is at least its mid length — a representability, not a magnitude, condition (precondition: `max_witnesses` is `None` or at least the boxed-subformula count) | **Live and open, at A1's scope.** `f` exists in closed form: `f(k) = max((2k+1)·2^k, 2·2^k)`. The `mid` clause is a magnitude condition, satisfiable at `mid ≥ f(\|C\|)`, since `mid` carries no periodicity. The `back`/`fwd` clause is open: the landed theorem bounds segment lengths, not minimal periods, so representability against a registry that folds by exact modulus needs §7.1(iii-a)'s bounded sweep. The `max_witnesses` precondition is exactly matched: the compressed family is `main :: (one witness lasso per boxed closure member its guess sets false)`, so `1 + \|{Box members}\|` uncapped lassos is precisely what it needs. §7.1, §7.3. |
```

#### 5b. `ADEQUACY.md` §7.1 — replacement prose (the two paragraphs the dispatch's STYLE CONSTRAINT names)

Replace the current "**A1 is recorded as open. It is not asserted…**" paragraph with:

> **A1 is discharged only at the empty-premise, single-conclusion instance; the general form
> (ADEQ) consumes is A1-Γ, and neither is asserted — (SOUND) does not depend on either.** Their
> only consequence is whether "no certificate within bounds" carries information beyond "no
> certificate was found within these bounds" — and, for any inference outside A1's proved
> instance, it must not, until A1-Γ lands.

Replace the "**The one candidate for reducing A1 to an already-landed Lean theorem, examined and
rejected**" heading and its lead-in with a heading and lead-in stating the durable technical fact,
keeping the three numbered reasons unchanged (they remain correct and are not history — they are
a standing fact about what `exists_annot_of_truth` does and does not supply):

> **Why `exists_annot_of_truth` does not supply A1's bound.**
> `Metalogic/Decidability/BiLasso/Extraction.lean:354`:
>
> ```lean
> theorem exists_annot_of_truth (hbx : BoxOracleSound P bx)
>     (τ : WorldHistory P.toTaskFrame) (t : ℤ) (hφ : TruthAt P.toModel τ t φ) :
>     ∃ A ∈ boundedAnnots P φ bx (bound P φ),
>       ∃ i ∈ Finset.Ico (cohWindowLo A) (cohWindowHi A),
>         A.lasso.unroll i = τ.state t ∧ φ ∈ A.label i
> ```
>
> is proved and sorry-free, with enumeration completeness (`Enumerate.lean:153, 309`) and a truth
> lemma (`TruthLemma.lean:149`) beside it, and it looks superficially like a bound for exactly
> this setting. It does not supply A1's bound, for three reasons: [keep the existing three
> numbered reasons verbatim — they are unchanged, durable facts].

Then replace the closing "So `exists_annot_of_truth` is the **template**… What would have to be
true for a genuine reduction: (i)…(ii)…(iii)…" paragraph with:

> So `exists_annot_of_truth` is a template, not a source, for A1's bound.
> `exists_witnessFamily_of_not_validZTime` meets (i) and (ii) directly: its hypothesis is
> `¬ ValidZTime φ`, an arbitrary ℤ-time model, not a presented one; and its bound,
> `compressionBound [] [φ]`, factors through `|closureOf ([] ++ [φ])|` alone, via a pigeonhole
> over subformula-set space (`TypeState C`, cardinality `2^|C|`) rather than presentation states.
> Condition (i) is met for the carrier — the hypothesis is presentation-free — but not for the
> premise context: extending it to arbitrary `Γ` is exactly A1-Γ's obligation. What A1's proved
> instance does not meet is condition (iii): a demonstration that this repository's search
> *represents* the compressed family at the configured `back`/`fwd`/`mid` — not merely that
> `back, mid, fwd` are "at least" the bound, since `WitnessRegistry.wrap()` folds `back`/`fwd`
> positions by exact period … [continue unchanged with the existing "measured against the live
> search" sentence and the two-routes paragraph — both are current, durable facts about the
> search, unaffected by A1's status].

The residue work items (iii-a) through (iii-e) that follow are current facts about A3's
representability gap, independent of A1's status, and need no change.

Add a new subsection immediately after §7.1, numbered §7.1a (no renumbering of §7.2/§7.3 needed):

> ### 7.1a A1-Γ — compression at general premises and conclusions, open
>
> (ADEQ) is stated for arbitrary `Γ` and `Δ`, and `examples.py`'s own countermodel inventory
> instantiates it there: every `_CM_` example has a non-empty premise list, and `MD_CM_1` has two
> conclusions. `exists_witnessFamily_of_not_validZTime` is proved at `Γ = []`, `Δ = [φ]` only, so
> it does not by itself instantiate A1 at the form this chain consumes; that general form is
> recorded here as its own obligation.
>
> The residue is bounded, not open-ended. `WitnessFamily.Refutes`, `refutes_of_certifies`,
> `joint_countermodel`, `exists_labelledLasso_of_history_realized`,
> `exists_labelledLasso_of_history`, `compressionBound`, and the four `Decidable` instances in
> `WitnessFamily/Decide.lean` are already stated at arbitrary `Γ Del`. What is scoped to `Γ = []`
> is the entry point's carrier normalization (the consequence-form analogue of
> `validZTime_iff_validInt`, built from `truthAt_map` at a fixed aligned triple),
> `WitnessFamily.Target`'s premise clause, and `Compression/Enumerate.lean`'s φ-specialized
> `closureSubsetsOf` / `rawLabelledLassos` / `IsLabelledLasso` / `boundedLassos` / `cands`
> (`ListEnumC.ofLen`/`upTo` are already generic).

#### 5c. `TRUST_PIPELINE.md` A-component table — A3 row (adopt the representability form)

Replace:

```markdown
| **A3** | Bound realization: configured lengths ≥ `f(|C|)` | **Vacuous** until A1 supplies `f` |
```

with:

```markdown
| **A3** | Bound realization: configured `back`/`fwd` are common multiples of the compressed family's periods (each bounded by `f(\|C\|)`), and `mid` is at least its mid length — a representability, not a magnitude, condition | **Live and open, at A1's scope** (`ADEQUACY.md` §7, §7.1, §7.3) |
```

#### 5d. `TRUST_PIPELINE.md` "In the Lean development" table — the compression/enumerator row

Replace:

```markdown
| **Compression (A1)** and the verified bounded enumerator | A1 is the only genuinely open *mathematics* in the (ADEQ) chain. The enumerator matters independently: because the candidate space at the bound is finite and enumeration completeness is already proved there, **absence can be decided by verified code rather than by trusting Z3's UNSAT** — which dominates proving this repository's encoder correct. |
```

with:

```markdown
| **Compression (A1-Γ)**, and the scope of the verified bounded enumerator | The empty-premise, single-conclusion instance of compression is proved (`exists_witnessFamily_of_not_validZTime`); the general `Γ ⊨ Δ` form the chain consumes (A1-Γ) is the remaining open mathematics. The enumerator (`cands`, `mem_cands_of_bounded`, `validZTime_iff_noCertifiedCandidate`, `Compression.decidableValidZTime`) makes "no certificate at the bound" a **theorem** at that same restricted scope — not a practical replacement for trusting Z3's UNSAT: the Lean criterion quantifies over the whole segment-length grid, a Z3 UNSAT verdict is at one configured `(back, mid, fwd)` triple, no `lean_exe` target runs the enumerator, and `Compression.decidableValidZTime` is a `def`, not a global `instance`. |
```

#### 5e. Consistency gap beyond the dispatch's literal item list (recommended, not mandatory)

`TRUST_PIPELINE.md`'s A-component table A1 row currently reads "**Open** — route named, owned by
the Lean development," which will contradict the corrected `ADEQUACY.md` A1 row (5a) the same way
Item 2 describes for A3. Recommended replacement, for internal consistency:

```markdown
| **A1** | Compression: a ℤ-time countermodel yields a certificate with lengths bounded by `f(|C|)` | **Partially discharged**, at the empty-premise, single-conclusion instance (`ADEQUACY.md` §7, §7.1) |
| **A1-Γ** | Compression at non-empty premises and multiple conclusions — the form (ADEQ) consumes | **Open** — the residual general form (`ADEQUACY.md` §7.1a) |
```

This is flagged separately from Items 1–3 because it is not literally named in the dispatch;
the plan/implement phase should treat it as recommended for the same self-consistency reason
Item 2 states, not as a scope expansion the dispatch already mandates.

#### 5f. Full citation-conversion table (Item 3, document-wide)

Convert every cell below from `file:line` to `file` (name-only citation, file path kept for
orientation, no line number). Nothing else in either document changes — see Finding 4 for the
subtree boundary.

| Document, location | Current text | Replacement |
|---|---|---|
| ADEQUACY.md §1 (certificate) | `LabelledLasso` (`...Basic.lean:76`) and `lab` (`Basic.lean:104`) | `LabelledLasso` (`Metalogic/Decidability/WitnessFamily/Basic.lean`) and `LabelledLasso.lab` (same file) |
| ADEQUACY.md §2 (S1 row) | `joint_countermodel` (`...Agreement.lean:232`) | `joint_countermodel` (`Metalogic/Decidability/WitnessFamily/Agreement.lean`) |
| ADEQUACY.md §3 (std construction) | `WitnessFamily.std` (`...Std.lean:65`) | `WitnessFamily.std` (`Metalogic/Decidability/WitnessFamily/Std.lean`) |
| ADEQUACY.md §4.1 table, "the construction" row | `...Std.lean:65` | `Metalogic/Decidability/WitnessFamily/Std.lean` |
| ADEQUACY.md §4.1 table, "the frame is ℤ-time" row | `...Std.lean:81, 87, 92` | `Metalogic/Decidability/WitnessFamily/Std.lean` |
| ADEQUACY.md §4.1 table, "Lemma 3 / Corollary 3.1" row | `...Std.lean:98` (leave the `ShiftSet.lean:293` and `TruthTransport.lean:310` anchors in the same row unchanged — different subtree) | `Metalogic/Decidability/WitnessFamily/Std.lean` for the `sh_surj` citation only |
| ADEQUACY.md §4.1 table, "Lemma 4" row | `...Agreement.lean:109, 193` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| ADEQUACY.md §4.1 table, "Lemma 4, U/S helper" row | `...Agreement.lean:65, 85` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| ADEQUACY.md §4.1 table, "The Theorem" row | `...Agreement.lean:232` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| ADEQUACY.md §4.1 table, "Theorem, single-conclusion" row | `...Agreement.lean:203, 219` | `Metalogic/Decidability/WitnessFamily/Agreement.lean` |
| ADEQUACY.md §4.1 table, "No certificate refutes MF" row | `...Examples.lean:275` | `Metalogic/Decidability/WitnessFamily/Examples.lean` |
| ADEQUACY.md §4.1 provenance note | scoped to "this table" | broaden to cover every `WitnessFamily`/`Compression` citation in the document (see 5g) |
| ADEQUACY.md §5.1 (periodicities) | `...Basic.lean:117, 123` | `Metalogic/Decidability/WitnessFamily/Basic.lean` |
| ADEQUACY.md §5.2 table header + rows | column header "File:line"; rows citing `Decide.lean:335`, `:743`, `:809`/`:883`, `:192`, `:212` | rename column "File"; every row's file becomes `Metalogic/Decidability/WitnessFamily/Decide.lean` with no line |
| ADEQUACY.md §5.2 (decidability instances sentence) | `Decide.lean:865, 878, 923, 927` | `Metalogic/Decidability/WitnessFamily/Decide.lean` |
| TRUST_PIPELINE.md Stage 6 ("The agreement theorem") | `joint_countermodel` (`...Agreement.lean:232`) | `joint_countermodel` (`Metalogic/Decidability/WitnessFamily/Agreement.lean`) |

New citations this task adds (§7/§7.1/§7.1a/§7.3, TRUST_PIPELINE.md's two tables) should be
written directly in this same name-only form from the start — see 5a–5d above, none of which
carry a line number.

#### 5g. `ADEQUACY.md`'s provenance note and top-of-document convention line

Broaden the existing §4.1 provenance note (currently scoped to "this table") so it covers the
whole document, since after 5f every `WitnessFamily`/`Compression` citation in the document is
name-only:

> **Provenance note.** Every `WitnessFamily`/`Compression` declaration cited in this document is a
> load-bearing citation by name; where a file is given alongside it, the file is for orientation
> only, not an anchor. BimodalLogic's generated, C35-gated `scripts/lean-citation-manifest.json`
> resolves each cited name to its current file, keyword line and span. A citation to
> `WitnessFamily.joint_countermodel` drifted from its actual line under an unchanged name while
> every gate in both repositories stayed green — a docstring edit upstream shifted it without
> breaking any check on either side — which is exactly why the manifest and its C35 gate exist,
> and why this subtree carries no line numbers in this document.

Also update the top-of-document sentence (§"Scope and status," currently "Every cited name was
checked to resolve at the cited file and line at the time of writing") to note the split
convention, e.g.: "...at the cited location at the time of writing; `WitnessFamily`/`Compression`
declarations are cited by name only and resolved via BimodalLogic's citation manifest (§4.1's
provenance note), while other citations retain file:line anchors."

## Decisions

- **A1-Γ is recorded as a new named obligation, not folded into A1's row**, per the dispatch's
  explicit instruction and matching the upstream hand-off's own structure.
- **The citation-convention migration (Item 3) is read as document-wide**, scoped to the
  `WitnessFamily/`-and-`Compression/` file-path subtree only, based on the dispatch's own
  VERIFICATION clause and its two-occurrence example (neither occurrence is in section 7). This
  report enumerates every site in Finding 5f rather than converting only the sites the new rows
  touch.
- **`BiLasso/`, `Semantics/`, `Metalogic/Independence/`, `Metalogic/Soundness.lean`, and
  `ProofSystem/Axioms.lean` citations are left untouched** — a different subtree, outside both the
  dispatch's Item 3 and the upstream report's Recommendation 2.
- **TRUST_PIPELINE.md's A1 row inconsistency (5e) is reported as a recommendation, not folded
  silently into the mandatory edit set**, since the dispatch's Item 2 names only A3 and the
  Lean-development row explicitly. The plan phase should decide whether to include it; this report
  states why leaving it out would reproduce Item 2's own problem in miniature.
- **No sampled-bound table is proposed for A1's row**, per the dispatch's explicit preference for
  `f`'s closed form over a table of measured values that can drift.

## Risks & Mitigations

- **Risk: the §7.1 prose rewrite in 5b is described as edit instructions rather than a full
  drop-in replacement of the whole section.** The two paragraphs and the heading named in the
  dispatch's STYLE CONSTRAINT are given as exact copy-ready text; the "keep unchanged" spans
  (the three numbered reasons, the two-routes paragraph, items (iii-a)-(iii-e)) are named by
  content rather than re-transcribed, to avoid this report drifting from the live file the way the
  citations already have. **Mitigation**: the implementer should diff against the live document
  text quoted in this report's own research (available in the read history of this session) rather
  than against the upstream hand-off note, which was written without the ModelChecker document's
  exact current wording in hand.
- **Risk: converting the §5.2 table's "File:line" column header to "File" changes a documented
  column contract.** **Mitigation**: this is the correct fix — every row in that table is a
  `WitnessFamily/Decide.lean` citation, so the whole column is in scope for Item 3.
- **Risk: A1-Γ's residue estimate ("bounded, not open-ended") could be wrong if the
  consequence-form carrier normalization does not go through as cleanly as
  `validZTime_iff_validInt`'s existing proof.** This is inherited from the upstream report's own
  stated risk, not resolved by this research (no Lean proof was attempted or is in scope for this
  repository). **Mitigation**: the row text in 5a and the subsection in 5b state only that the
  residue is bounded by naming the already-general declarations, and promise no effort estimate,
  matching the upstream caveat.
- **Risk: sibling task's file scope.** The sibling task (this cycle) has `examples.py` in its
  declared scope; this research read that file but recommends no edit to it. If the sibling task's
  implementation changes the premise/conclusion counts cited in the A1-Γ row (5a) or §7.1a (5b),
  the counts ("every example has a non-empty premise list," "`MD_CM_1` has `|Δ| = 2`") should be
  re-verified before the plan/implement phase applies this text.

## Appendix: verification commands run

- `grep -rn "^\(theorem\|def\|lemma\|noncomputable def\|instance\) <name>"` against every
  `Compression/*.lean` and `WitnessFamily/*.lean` file, for all 23 seeded names plus the
  pre-existing citations (Finding 1).
- `jq -r '.entries[] | select(.name | test(...))'` against `scripts/lean-citation-manifest.json`
  to cross-check current file:line for every seeded name (Finding 1, Finding 2).
- `bash scripts/check-module-invariants.sh --no-build 2>&1 | grep -i "C35\|manifest"` — confirmed
  `PASS C35 ... all 86 seeded declaration(s) resolve`.
- `git log --oneline -5 -- scripts/lean-citation-seeds.txt` and
  `git log --oneline --all | grep -i "task 693"` in BimodalLogic, to confirm the producing task
  ran to completion after the hand-off note was written (Finding 3).
- `grep -n "\.lean:" ADEQUACY.md TRUST_PIPELINE.md` in this repository, to enumerate every
  currently-cited file:line anchor (Finding 2, Finding 5f).
- `grep -n "_premises\s*=\|_conclusions\s*=" examples.py | grep -i "CM_"` — confirmed all 13
  countermodel examples have non-empty premise lists and `MD_CM_1` has two conclusions.
