# Research Report: Task #211

**Task**: 211 - Correct kernel-checked-proof overclaim
**Started**: 2026-09-28T07:01:21Z
**Completed**: 2026-09-28T07:30:00Z
**Effort**: ~1 hour
**Dependencies**: None
**Sources/Inputs**: Codebase (`code/src/model_checker/theory_lib/bimodal/`), companion Lean
repository (`~/Projects/BimodalLogic`), task 197/205/209 artifacts and state.json
**Artifacts**: - This report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Item 1 confirmed as a live, in-tree self-contradiction.** `ADEQUACY.md` lines 458 and 490
  still assert "a kernel-checked proof [for this particular certificate]"; `TRUST_PIPELINE.md:162`,
  `A2_GAP.md:519`, and `SETTINGS.md:103-113` all correctly deny that phrasing and reserve it for a
  third `Acceptance` value nothing here produces. `semantic/model.py`'s module docstring
  (`_verification_label`'s "Wording discipline (F2)") already names this exact ADEQUACY.md
  overclaim as a known, unfixed finding from task 197 ("the certificate-wire hardening task").
  The correct replacement wording is already established in three places in-tree
  (`SETTINGS.md:108-109`, `semantic/checker.py` `resolve_checker`, `semantic/model.py:337-340`):
  *"Lean constructed a `WitnessFamily.Refutes` term for this certificate by applying a
  compile-time kernel-checked implication to four run-time decisions."*
- **Item 2: the pin should be retired, not auto-tracked.** `BIMODAL_LOGIC_COMMIT` in
  `tests/_lean_check.py:99` has zero consumers anywhere in the tree (grep-verified), and
  `semantic/checker.py`'s own module docstring already documents why: it "is a pin that is
  consumed by nothing and had already drifted (from `d55e2760` to `d1a24b30`, observed same-day)
  before this module existed." The real enforcement mechanism — the capability handshake in
  `resolve_checker`, backed by `CheckerHandle.provenance` recorded dynamically per resolution
  from the checkout's actual git HEAD — was built specifically because a static pin cannot detect
  a checkout rebuilt at a different, incompatible commit. Auto-tracking the constant would
  re-introduce exactly the drift problem the handshake replaced it to solve.
- **Item 3: the deferral is stale, not verify-and-restate.** `TRUST_PIPELINE.md:287-292` claims
  the Lean-side half of S4 (a truth-preservation theorem for the `Sentence → Formula`
  translation) is "deferred, not attempted... confirmed absent from the local `BimodalLogic`
  checkout." That is no longer true: BimodalLogic task 679 ("Lean Sentence-to-Formula
  translation, proved truth-preserving," completed 2026-09-27T13:10:00Z, commit range ending
  `d815cf3e9`) landed `FormalSystem/SourceLanguage/SentenceTruth.lean`'s `sat_iff` theorem
  (sorry-free, no new axiom), plus the `translate_sentence` executable/JSON codec and a
  26-row fixture file, exactly the infrastructure the dispatch flagged. `TRUST_PIPELINE.md`'s
  "What remains" row for this item needs to change from "deferred / absent" to "landed upstream;
  what remains here is consuming it" — which is the scope of the already-open, currently
  in-progress task 209 (`bimodal_sentence_translation_contract`, status `researching` as of this
  writing), not new work for this task.

## Context & Scope

Three independent documentation-consistency items in
`code/src/model_checker/theory_lib/bimodal/`, verified against the current tree rather than
inherited from any prior report:

1. A wording contradiction between `ADEQUACY.md` and three other documents about what an
   `"acceptance":"entailment"` verdict licenses.
2. Whether to auto-track or retire a dead constant (`BIMODAL_LOGIC_COMMIT`) in
   `tests/_lean_check.py`.
3. Whether `TRUST_PIPELINE.md`'s claim that the Lean-side half of obligation S4 is "deferred, not
   attempted" is still accurate, given that the companion `BimodalLogic` repository's
   `lakefile.toml` now declares a `translate_sentence` executable.

Task 209 (`bimodal_sentence_translation_contract`) is a concurrent sibling dispatched in this
same `/orchestrate` cycle, with a declared `file_scope` of
`syntactic/sentence.py`, `tests/unit/test_formula.py`,
`tests/integration/test_sentence_translation_agreement.py`, `tests/_lean_check.py`, and
`tests/README.md`. None of those overlap the files this task's findings point at
(`docs/ADEQUACY.md`, `docs/TRUST_PIPELINE.md`, `docs/A2_GAP.md`, `docs/SETTINGS.md`), **except**
`tests/_lean_check.py`, which both tasks touch: task 209 is wiring the conformance-channel test
there, this task is (per the recommendation below) deleting the unused `BIMODAL_LOGIC_COMMIT`
constant there. A future plan/implementation phase for task 211 should re-read
`tests/_lean_check.py` immediately before editing it, per the territory contract, since task 209
may have already landed changes to that file by the time task 211 implements.

## Findings

### Item 1 — The ADEQUACY.md overclaim

**The two wrong sites** (verified against current line numbers, both within `docs/ADEQUACY.md`):

- Line 456-459 (§6.1, describing the `"acceptance"` wire field):
  > `"entailment"` means the binary constructed the paper-countermodel existence term for this
  > particular certificate (a kernel-checked proof); an absent field reads as `"decided"`...

- Line 487-491 (§6.2, describing the four-step dual verification):
  > ...`check_certificate`'s accepting branch applies `WitnessFamily.joint_countermodel` to the
  > decided hypothesis, *constructing* the paper-countermodel existence term rather than printing
  > a verdict — a kernel-checked proof for that particular certificate, not merely four
  > `Decidable` instances agreeing.

**The three correct sites**, all using the same denial:

- `TRUST_PIPELINE.md:161-163`: "A `countermodel` verdict says the four `Decidable` instances
  returned `true` on the family rebuilt from the wire input. It is **not a kernel-checked proof
  for that particular certificate**. `ADEQUACY.md` §6.2 says so explicitly..." — this citation
  is itself now stale in the sense that ADEQUACY.md §6.2 says the *opposite* for the entailment
  case; see Decisions below.
- `A2_GAP.md:518-520`: same denial, same citation pattern back to ADEQUACY.md §6.2.
- `SETTINGS.md:103-113`: the fullest, most accurate statement — it gives the exact narrower
  wording ("Lean constructed a `WitnessFamily.Refutes` term for this certificate by applying a
  compile-time kernel-checked implication to four run-time decisions") and explicitly says the
  stronger phrase "a kernel-checked proof for this particular certificate" is reserved for a
  third `Acceptance` value "that nothing this checker produces today," citing
  `BimodalTools/CertificateImport.lean`'s `Acceptance` docstring.

**Production code already uses the correct, narrower wording.** `semantic/model.py`'s
`_verification_label` (lines 320-340) renders exactly SETTINGS.md's phrasing:
`"independently checked -- Lean constructed a WitnessFamily.Refutes term for this certificate by
applying a compile-time kernel-checked implication to four run-time decisions..."`. The module
docstring's "Wording discipline (F2)" section (lines 60-66) states in so many words that this
wording is deliberately narrower than "a kernel-checked proof for this particular certificate,"
names that exact phrase as the one `docs/ADEQUACY.md` §6.2 and `docs/TRUST_PIPELINE.md`
"currently use," and calls it out as "reported as a finding for the certificate-wire hardening
task to fix, not edited here."

**"The certificate-wire hardening task" is task 197**, `[COMPLETED]`
(`specs/197_harden_certificate_wire_proof_carrying/`). Its summary confirms it touched
`ADEQUACY.md` §6.1/§6.2 (e.g., adding `"echo"` to `rejected` verdicts) but its own description
and summary do not mention correcting the "kernel-checked proof" phrase — the finding
`semantic/model.py` names was left unfixed, exactly matching the two remaining bad sites found
here. `TRUST_PIPELINE.md` was **not** wrong; it and `A2_GAP.md` already used the correct denial
at the time task 197 landed, and were not touched.

**Confirmed exhaustive** via `grep -rn "kernel-checked proof" docs/`: exactly six occurrences —
`TRUST_PIPELINE.md:162`, `SETTINGS.md:108`, `ADEQUACY.md:458`, `ADEQUACY.md:482` (this one is
already correct — same denial pattern as TRUST_PIPELINE/A2_GAP), `ADEQUACY.md:490` (wrong), and
`A2_GAP.md:519`. Only `ADEQUACY.md:458` and `:490` need rewriting; nothing else in the docs
directory contains the phrase.

### Item 2 — `BIMODAL_LOGIC_COMMIT`

- Declared at `tests/_lean_check.py:99`: `BIMODAL_LOGIC_COMMIT = "d55e2760e6731a2240f3db5d761658947bf69125"`,
  exported in `__all__` (line 77).
- Grep across `code/` for `BIMODAL_LOGIC_COMMIT` outside its own declaration and export: **zero
  consumers.** No test asserts against it, no other module imports it.
- `semantic/checker.py`'s module docstring ("The capability handshake (not the commit pin)",
  lines 33-47) already narrates why: `BIMODAL_LOGIC_COMMIT` "is a pin that is consumed by nothing
  and had already drifted (from `d55e2760` to `d1a24b30`, observed same-day) before this module
  existed. Pinning a commit cannot prevent a checkout from being rebuilt at a different,
  incompatible commit; checking the binary's actual behaviour can." The replacement mechanism —
  a `CheckerHandle.provenance` field populated per-resolution from `_git_head(checkout_root)`
  (lines 137, 241, 328-329) — records the checkout's actual HEAD as informational provenance on
  every resolution, not as a gate, and is what backs the "checkout" suffix in
  `SETTINGS.md`'s state-1 wording.
- This is not a fresh judgment call this task needs to make from scratch: the enforcement
  rationale for retiring the pin, rather than tracking it, is already fully written and landed in
  `semantic/checker.py`'s docstring by task 205 (`certifying_countermodel_architecture`,
  `[COMPLETED]`). What is still open is the mechanical cleanup: `tests/_lean_check.py` still
  carries the dead constant and its `__all__` export, and `semantic/checker.py:43`'s prose still
  refers to it in present tense ("`BIMODAL_LOGIC_COMMIT` (recorded in `tests/_lean_check.py`) is
  a pin...") as though it still serves a purpose, which will read oddly once the constant is
  deleted.

### Item 3 — The S4 deferral claim

- `TRUST_PIPELINE.md:287-292` ("What remains" section, opening paragraph): "Discharge S4 on the
  ModelChecker side is done... The remaining half — a Lean-side translation with its own
  truth-preservation theorem — is listed under the Lean development below, explicitly deferred
  (its counterpart is confirmed absent from the local `BimodalLogic` checkout)."
- `TRUST_PIPELINE.md:313` (table row under "In the Lean development"): "**Lean-side translation
  with a truth-preservation theorem** | The other half of S4 -- deferred, not attempted from this
  repository; the ModelChecker-side half is discharged..."
- **This is now false.** `~/Projects/BimodalLogic/lakefile.toml:172-176` declares
  `[[lean_exe]] name = "translate_sentence" root = "BimodalTools.TranslateSentenceMain"`, and the
  binary is built (`.lake/build/bin/translate_sentence` exists). More importantly, the
  truth-preservation theorem itself exists:
  `FormalSystem/SourceLanguage/SentenceTruth.lean:231-232`:
  ```
  theorem sat_iff (M : TaskModel F) (φ : Sentence) :
      ∀ (τ : WorldHistory F) (t : F.Duration), Sat M τ t φ ↔ TruthAt M τ t (tr φ)
  ```
  `grep -n sorry` over that file returns nothing — the theorem is sorry-free, proved by structural
  induction over all 18 `Sentence` constructors.
- **Provenance**: `git log --oneline -- FormalSystem/SourceLanguage/SentenceTruth.lean` in
  `~/Projects/BimodalLogic` shows `fb6a90537 task 679 phase 2: the truth evaluation and the
  agreement theorem`. BimodalLogic's own task tracker
  (`specs/679_lean_sentence_formula_translation_truth/summaries/01_..._summary.md`) records this
  task `[COMPLETED]`, `2026-09-27T13:10:00Z`, "No `sorry`, no new axiom, no deferral," and lists
  exactly the deliverables `TRUST_PIPELINE.md` says are absent: the native truth evaluation
  `Sat`, the agreement theorem `sat_iff`, the `translate_sentence` executable, its JSON codec, and
  a committed 26-line fixture (`Tests/fixtures/sentence-translation-fixtures.jsonl`) meant for a
  **consuming repository** (i.e. this one) to diff its own translation against.
- **This task's own scope is documentation correction only** — the dispatch explicitly frames
  item 3 as "verify a deferral before restating it," not "wire the conformance channel." The
  wiring itself — consuming BimodalLogic's fixture from this repository's own
  `Sentence.update_types` / `formula.translate` / `to_json` pipeline — is squarely the scope of
  task 209 (`bimodal_sentence_translation_contract`), which is a concurrent sibling in this same
  orchestrate cycle, status `researching`, dependencies on tasks 205/206 (both completed), and
  whose description (item 5, "AN UNWIRED CONFORMANCE CHANNEL") already names
  `Tests/fixtures/sentence-translation-fixtures.jsonl` as the fixture to consume. Task 209's
  description does **not** mention the Lean-side `sat_iff` theorem or `SentenceTruth.lean` by
  name — its own upstream research (authored before BimodalLogic task 679 landed, or independent
  of it) is scoped to the Python-side `sentence.py` defect and the fixture-diffing test, not to
  restating the theorem's existence in `TRUST_PIPELINE.md`. There is no finding from task 209 to
  "prefer... over a fresh probe" (per the dispatch's conditional instruction) — task 209 has not
  landed, and its scope does not include this specific documentation correction, so the fresh
  probe performed here is authoritative for item 3.
- **A related, adjacent staleness this task was NOT asked to fix, flagged for the plan phase to
  weigh**: `ADEQUACY.md:80` (obligation table) and `ADEQUACY.md:300` both say the S4 translation
  is "not covered by any Lean theorem cited here" / "not covered by any theorem cited here." This
  is the same species of staleness as the TRUST_PIPELINE.md claim — both predate BimodalLogic
  task 679 — but the dispatch names only `TRUST_PIPELINE.md` for item 3. Recorded here as an
  observation, not a mandate; the plan phase should decide whether to fold it in (same underlying
  fact, same fix shape: "not yet proved" → "proved upstream, not yet consumed here") or leave it
  for a follow-up task.

## Decisions

- **Item 1**: Rewrite `ADEQUACY.md:456-459` and `:487-491` to replace "a kernel-checked proof
  [for this particular certificate]" with the SETTINGS.md/model.py wording — "Lean constructed a
  `WitnessFamily.Refutes` term for this certificate by applying a compile-time kernel-checked
  implication to four run-time decisions" (adapted grammatically to each site's sentence). Do
  **not** touch `TRUST_PIPELINE.md:162`, `A2_GAP.md:519`, or any part of `SETTINGS.md` — all
  three already deny the overclaim and are correct as written. After the rewrite, re-grep
  `docs/` for "kernel-checked proof" and confirm every surviving hit either denies the claim
  (`TRUST_PIPELINE.md`, `A2_GAP.md`) or explains the reservation (`SETTINGS.md`).
- **Item 2**: Retire `BIMODAL_LOGIC_COMMIT`, do not auto-track it. Recommended concrete steps for
  the plan phase: remove the constant's declaration (`tests/_lean_check.py:99`) and its `__all__`
  entry (line 77); update `semantic/checker.py:43`'s docstring sentence, which currently narrates
  the pin in present tense as something that "is... recorded in `tests/_lean_check.py`," to past
  tense or to drop the specific-location claim now that the pin no longer exists there. No test
  changes are needed beyond this, since nothing consumes the constant. Territory note: this edit
  and task 209's edits both land in `tests/_lean_check.py`; re-read the file immediately before
  editing per the concurrency protocol.
- **Item 3**: Rewrite `TRUST_PIPELINE.md:287-292`'s "confirmed absent from the local `BimodalLogic`
  checkout" claim and `:313`'s "deferred, not attempted from this repository" table row to reflect
  that the Lean-side truth-preservation theorem (`sat_iff`, `FormalSystem/SourceLanguage/SentenceTruth.lean`)
  and its consumption infrastructure (`translate_sentence` executable, JSON codec, fixture file)
  have landed upstream (BimodalLogic task 679, completed 2026-09-27). The corrected framing:
  the Lean-side theorem is no longer the open half of S4; what remains is this repository
  *consuming* the fixture to verify its own translation agrees — which is task 209's scope, not
  this task's. Cite BimodalLogic task 679 and the fixture path
  (`Tests/fixtures/sentence-translation-fixtures.jsonl`) so the row points a future reader at
  where the real remaining work (the wiring) is tracked, rather than re-describing something
  already proved as merely aspired-to.

## Risks & Mitigations

- **Risk**: Item 1's rewrite could accidentally weaken the trust-base honesty the surrounding
  prose is careful about (e.g., accidentally re-introducing "proof" language elsewhere in the
  same paragraph). **Mitigation**: use the exact, already-reviewed wording from
  `SETTINGS.md:108-109` / `semantic/model.py:337-339` verbatim rather than paraphrasing; both are
  landed, reviewed production text.
- **Risk**: Item 2's docstring cleanup in `semantic/checker.py` and item 2's constant removal in
  `tests/_lean_check.py` collide with task 209's concurrent edits to the same file. **Mitigation**:
  re-read `tests/_lean_check.py` immediately before editing (per dispatch's Territory section);
  stage only this task's own hunks.
- **Risk**: Item 3's correction could be read as claiming this repository's own translation is now
  verified, which it is not — the Lean theorem verifies BimodalLogic's own reference translation,
  not this repository's implementation (`SentenceTruth.lean`'s own docstring is explicit: "It does
  not certify that repository's implementation... it does not relieve that repository of its own
  verification obligation for its translation"). **Mitigation**: when rewriting, preserve that
  distinction explicitly — landed theorem = a verified reference to diff against, not a proof
  that this repository's translation is correct; the diffing itself is task 209's unwired
  conformance channel.

## Context Extension Recommendations

None. This is a narrowly-scoped, bimodal-theory-specific documentation-consistency correction;
no gap in `.claude/context/` documentation was identified as a byproduct of this research.

## Appendix

### Search queries / commands used

- `grep -rn "kernel-checked proof" code/src/model_checker/theory_lib/bimodal/docs/`
- `grep -rn "BIMODAL_LOGIC_COMMIT" code/src/model_checker/theory_lib/bimodal/ code/`
- `find ~/Projects/BimodalLogic -iname "*TranslateSentence*" -o -iname "*translate_sentence*"`
- `git log --oneline -- FormalSystem/SourceLanguage/SentenceTruth.lean` (in `~/Projects/BimodalLogic`)
- `git log --oneline -- BimodalTools/TranslateSentenceMain.lean` (in `~/Projects/BimodalLogic`)
- `grep -n sorry ~/Projects/BimodalLogic/FormalSystem/SourceLanguage/SentenceTruth.lean`
- `jq -r '.active_projects[] | select(.project_number==209)' specs/state.json`
- `jq -r '.active_projects[] | select(.description | contains("certificate-wire hardening"))' specs/state.json`

### Key files read

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (§6.1, §6.2, plus lines 80, 300 for
  the adjacent staleness note)
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` (Stage 5 section, "What
  remains" section)
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` (§9/§10 area, the honesty point)
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` (Certificate Verification section)
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` (module docstring, `_verification_label`)
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` (module docstring, `resolve_checker`)
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`
- `~/Projects/BimodalLogic/lakefile.toml`
- `~/Projects/BimodalLogic/BimodalTools/TranslateSentenceMain.lean`
- `~/Projects/BimodalLogic/FormalSystem/SourceLanguage/SentenceTruth.lean`
- `~/Projects/BimodalLogic/specs/679_lean_sentence_formula_translation_truth/summaries/01_sentence-formula-translation-truth-summary.md`
- `specs/197_harden_certificate_wire_proof_carrying/summaries/01_harden-certificate-wire-proof-carrying-summary.md`
- `specs/state.json` (tasks 197, 205, 209, 211)
