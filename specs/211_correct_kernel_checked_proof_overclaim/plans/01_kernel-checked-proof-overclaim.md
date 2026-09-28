# Implementation Plan: Task #211

- **Task**: 211 - Correct kernel-checked-proof overclaim
- **Status**: [COMPLETED]
- **Effort**: 2.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/211_correct_kernel_checked_proof_overclaim/reports/01_kernel-checked-proof-overclaim.md
- **Artifacts**: plans/01_kernel-checked-proof-overclaim.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Three independent documentation-consistency corrections in
`code/src/model_checker/theory_lib/bimodal/`, plus one small dead-code retirement. Item 1
rewrites the two `ADEQUACY.md` sites that assert an `"acceptance":"entailment"` verdict is "a
kernel-checked proof" for a particular certificate — a claim three other documents in the same
directory correctly deny. Item 2 retires the dead `BIMODAL_LOGIC_COMMIT` pin. Item 3 corrects
`TRUST_PIPELINE.md`'s now-false claim that the Lean-side half of obligation S4 is absent
upstream. Definition of done: every surviving `"kernel-checked proof"` occurrence under
`docs/` either denies the claim or explains why the phrase is reserved; `BIMODAL_LOGIC_COMMIT`
exists nowhere in the tree; no document still describes `sat_iff` as unattempted; the bimodal
test suite is green.

### Research Integration

The research report verified all three items against the current tree and against the companion
`~/Projects/BimodalLogic` checkout. Its three findings drive the three work items directly:

- Item 1: exactly two wrong sites (`ADEQUACY.md:458`, `ADEQUACY.md:490`); `TRUST_PIPELINE.md:162`,
  `A2_GAP.md:519`, `ADEQUACY.md:482` and `SETTINGS.md:108` are already correct and MUST NOT be
  "fixed". The correct replacement wording is already landed, reviewed production text in
  `SETTINGS.md:107-109` and `semantic/model.py`'s `_verification_label` — it is copied, not
  paraphrased.
- Item 2: the report's recommendation is **retire, not auto-track**. The enforcement rationale is
  already written and landed in `semantic/checker.py`'s "The capability handshake (not the commit
  pin)" docstring section; auto-tracking would re-introduce the drift the handshake replaced.
- Item 3: the deferral claim is stale, not merely in need of restatement. BimodalLogic's
  `FormalSystem/SourceLanguage/SentenceTruth.lean:231` carries a sorry-free `sat_iff`, and the
  `translate_sentence` executable and `Tests/fixtures/sentence-translation-fixtures.jsonl`
  fixture both exist (re-confirmed at plan time). The dispatch's conditional "prefer the
  sentence-translation conformance task's findings over a fresh probe" does **not** fire: task
  209 has not landed and its scope excludes this documentation correction, so the fresh probe is
  authoritative.

The report additionally flagged, as an observation rather than a mandate, an adjacent staleness
of the same species at `ADEQUACY.md:80` and `ADEQUACY.md:300`. **Decision: fold it in** (Phase 4)
— same underlying fact, same fix shape, and leaving two documents disagreeing about `sat_iff`
would simply recreate item 1's defect class in a new place.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch; no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:
- Remove the `"a kernel-checked proof [for this particular certificate]"` overclaim from the two
  `ADEQUACY.md` sites, using the already-landed narrower wording verbatim.
- Delete the `BIMODAL_LOGIC_COMMIT` constant and its `__all__` export, and correct the one
  docstring sentence in `semantic/checker.py` that narrates it in the present tense.
- Correct `TRUST_PIPELINE.md`'s "deferred / confirmed absent" framing of the Lean-side S4
  truth-preservation theorem, and align `ADEQUACY.md`'s two matching S4 statements.
- Leave the documentation set internally consistent: one claim about what `entailment` licenses,
  one claim about where the S4 Lean theorem stands.

**Non-Goals**:
- Editing `TRUST_PIPELINE.md:162`, `A2_GAP.md:519`, `ADEQUACY.md:482`, or `SETTINGS.md`'s
  Certificate Verification section. All four already state the accurate position.
- Wiring the sentence-translation conformance channel (consuming BimodalLogic's fixture). That is
  task 209's declared scope and is being dispatched concurrently.
- Changing `semantic/model.py`'s `_verification_label`, or any user-facing string. The overclaim
  never reached users; `_verification_label` was written from the Lean docstring directly.
- Adding any new test. Nothing consumes `BIMODAL_LOGIC_COMMIT`, so its removal needs no test
  change; the rest is prose.
- Re-introducing commit pinning in any auto-tracked form.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rewriting item 1 accidentally weakens the surrounding trust-base honesty, or re-introduces "proof" language elsewhere in the same paragraph | H | M | Copy `SETTINGS.md:107-109` / `semantic/model.py`'s `_verification_label` wording verbatim rather than paraphrasing; both are landed, reviewed text. Re-read the whole of §6.1 and §6.2 after editing, not just the changed lines. |
| "Fixing" one of the four already-correct sites, inverting the defect | H | L | Phase 1's file scope is `ADEQUACY.md` only; its verification re-greps and asserts `TRUST_PIPELINE.md:162`, `A2_GAP.md:519`, `SETTINGS.md:108` are byte-identical to their pre-edit state. |
| Item 2's edit to `tests/_lean_check.py` collides with concurrent task 209, which declares that same file in its `file_scope` | M | H | Re-read `tests/_lean_check.py` immediately before editing (dispatch Territory section); stage only this task's own hunks by explicit path list, never a directory or glob `git add`; if a foreign modification or commit to that file is observed, STOP and report per the concurrency protocol. |
| Removing an `__all__`-exported public symbol breaks an unseen dynamic import | M | L | Grep for `BIMODAL_LOGIC_COMMIT` across the whole repository (not just `code/`) immediately before deleting, including string-literal / `getattr` forms; run the full bimodal test suite in Phase 5. |
| Item 3's correction is read as claiming *this* repository's translation is now verified | H | M | Preserve the distinction explicitly in the new prose: the upstream theorem verifies BimodalLogic's own reference translation and supplies a fixture to diff against; it does not discharge this repository's own obligation. `SentenceTruth.lean`'s own docstring says exactly this — mirror it. |
| Stale cross-references (`TRUST_PIPELINE.md:162` and `A2_GAP.md:519` both cite "ADEQUACY.md §6.2 says so explicitly") silently become wrong after the §6.2 rewrite | M | L | Phase 1 verification re-reads both citing sentences against the rewritten §6.2 and confirms the citation still resolves to a denial. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 3 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phase 4 is serialized after Phase 1 because
both edit `ADEQUACY.md`, and after Phase 3 because it must use the same corrected S4 framing.

---

### Phase 1: Rewrite the two ADEQUACY.md kernel-checked-proof sites [COMPLETED]

**Goal**: `ADEQUACY.md` §6.1 and §6.2 state what an `"acceptance":"entailment"` verdict actually
licenses, matching `SETTINGS.md` and `semantic/model.py`, and no longer contradict
`TRUST_PIPELINE.md` or `A2_GAP.md`.

**Tasks**:
- [x] Re-read `docs/ADEQUACY.md` lines 450-500 to confirm current line numbers before editing
      (they are a hypothesis — see Scope Hypothesis below). *(completed)*
- [x] Re-read `docs/SETTINGS.md` lines 104-113 and `semantic/model.py`'s `_verification_label`
      (~lines 320-340) to copy the canonical wording exactly. *(completed)*
- [x] Rewrite §6.1's `**"acceptance"**` paragraph (currently ~line 456-459): replace
      "constructed the paper-countermodel existence term for this particular certificate (a
      kernel-checked proof)" with the narrower landed wording — Lean constructed a
      `WitnessFamily.Refutes` term for this certificate by applying a compile-time kernel-checked
      implication to four run-time decisions — and state that "a kernel-checked proof for this
      particular certificate" is reserved for a third `Acceptance` value nothing this checker
      produces today, citing `SETTINGS.md` and `BimodalTools/CertificateImport.lean`'s
      `Acceptance` docstring. *(completed)*
- [x] Rewrite §6.2's entailment paragraph (currently ~line 487-491): keep the accurate mechanical
      description (`check_certificate`'s accepting branch applies `WitnessFamily.joint_countermodel`
      to the decided hypothesis, constructing a term rather than printing a verdict) and replace
      the trailing "— a kernel-checked proof for that particular certificate" clause with the same
      narrower wording plus an explicit denial of the reserved phrase. *(completed)*
- [x] Leave `ADEQUACY.md:482`'s existing denial untouched. *(completed: verified byte-identical)*
- [x] Commit (`task 211 phase 1: ...`), staging `docs/ADEQUACY.md` by explicit path only. *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly two sites in `ADEQUACY.md` need rewriting (currently lines 458 and
490 of six total `"kernel-checked proof"` occurrences under `docs/`). Confirm at implementation
time with `grep -rn "kernel-checked proof" docs/` before editing; if the count or the set of
files differs from {`TRUST_PIPELINE.md`:1, `SETTINGS.md`:1, `ADEQUACY.md`:3, `A2_GAP.md`:1},
re-classify each occurrence as asserting or denying before proceeding.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §6.1 `"acceptance"` paragraph and
  §6.2 entailment paragraph rewritten to the narrower, accurate claim.

**Verification**:
- `grep -rn "kernel-checked proof" code/src/model_checker/theory_lib/bimodal/docs/` — every
  surviving occurrence either denies the claim (`TRUST_PIPELINE.md`, `A2_GAP.md`,
  `ADEQUACY.md`:482 and the two rewritten sites) or is `SETTINGS.md`'s explanation of why the
  phrase is reserved. No occurrence asserts it.
- `git diff --stat` shows `ADEQUACY.md` as the only changed file; `TRUST_PIPELINE.md`, `A2_GAP.md`
  and `SETTINGS.md` are byte-identical to HEAD.
- Re-read `TRUST_PIPELINE.md:160-164` and `A2_GAP.md:517-521`: both cite "ADEQUACY.md §6.2 says so
  explicitly", and §6.2 as rewritten still says so.
- Diff read-through confirms every changed hunk is markdown prose (tier `prose`).

---

### Phase 2: Retire the dead BIMODAL_LOGIC_COMMIT pin [COMPLETED]

**Goal**: The unconsumed, repeatedly-drifted commit pin is gone from the tree, and the one
docstring that narrates it in the present tense reads correctly without it.

**Tasks**:
- [x] `grep -rn "BIMODAL_LOGIC_COMMIT" /home/benjamin/Projects/ModelChecker` (whole repo, not just
      `code/`) to re-confirm zero consumers immediately before editing. *(completed: confirmed
      zero code consumers; task 209's plan/report files reference it in prose only)*
- [x] **Re-read `tests/_lean_check.py` in full immediately before editing** — task 209 declares
      this same file in its `file_scope` and is dispatched in this same cycle. If a foreign
      uncommitted modification or an unexpected commit to this file is present, check `git log`
      to confirm it is not this task's own work, then STOP and report rather than proceeding.
      *(completed: no foreign modification present; git log confirmed no recent commits to this
      file from task 209)*
- [x] Delete the `BIMODAL_LOGIC_COMMIT` assignment (currently ~line 99) and its `__all__` entry
      (currently ~line 77). *(completed)*
- [x] Update `semantic/checker.py`'s "The capability handshake (not the commit pin)" docstring
      (currently ~line 43): the sentence narrating `BIMODAL_LOGIC_COMMIT` as something that "is
      (recorded in `tests/_lean_check.py`) a pin that is consumed by nothing" must move to the
      past tense / drop the location claim, so the rationale for the handshake survives without
      pointing at a constant that no longer exists. Preserve the drift evidence
      (`d55e2760` → `d1a24b30`, observed same-day) — it is the argument, not decoration.
      *(completed)*
- [x] Commit (`task 211 phase 2: ...`), staging the two files by explicit path list only. *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly three in-tree occurrences of `BIMODAL_LOGIC_COMMIT` exist
(`tests/_lean_check.py`:77 and :99, `semantic/checker.py`:43), and none is a consumer. Confirm at
implementation time with the whole-repo grep above; if any occurrence outside those three exists,
or any is a read rather than a declaration/export/prose mention, stop and re-plan rather than
deleting.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - remove the constant and its
  `__all__` export.
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` - docstring sentence re-tensed to
  not reference a live constant.

**Verification**:
- `grep -rn "BIMODAL_LOGIC_COMMIT" /home/benjamin/Projects/ModelChecker` returns nothing.
- Enumerated direct dependents build/import cleanly (tier `interface`):
  `PYTHONPATH=code/src python -c "import model_checker.theory_lib.bimodal.tests._lean_check as m; print(m.__all__)"`
  succeeds and `__all__` no longer lists the constant; `PYTHONPATH=code/src python -c "import
  model_checker.theory_lib.bimodal.semantic.checker"` succeeds.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` collects
  without import error.
- `git status --short` shows only this task's two files modified.

---

### Phase 3: Correct TRUST_PIPELINE.md's stale S4 deferral [COMPLETED]

**Goal**: `TRUST_PIPELINE.md` stops claiming the Lean-side truth-preservation theorem is absent
and unattempted, and points a reader at the real remaining work (this repository consuming the
upstream fixture) instead.

**Tasks**:
- [x] Re-verify upstream before restating: in `~/Projects/BimodalLogic`, confirm
      `FormalSystem/SourceLanguage/SentenceTruth.lean` contains `theorem sat_iff`, that
      `grep -n sorry` over that file is empty, that `Tests/fixtures/sentence-translation-fixtures.jsonl`
      exists, and that `lakefile.toml` declares the `translate_sentence` executable. (All four
      confirmed at plan time; re-confirm rather than inherit.) *(completed: all four re-confirmed)*
- [x] Rewrite the "What remains" opening paragraph (currently ~lines 286-292): drop "explicitly
      deferred (its counterpart is confirmed absent from the local `BimodalLogic` checkout)" and
      state that the Lean-side half landed upstream, citing `SentenceTruth.lean`'s `sat_iff`.
      *(completed)*
- [x] Rewrite the "Lean-side translation with a truth-preservation theorem" table row under "In the
      Lean development" (currently ~line 313): change "deferred, not attempted from this
      repository" to a landed-upstream statement naming the fixture path
      (`Tests/fixtures/sentence-translation-fixtures.jsonl`) as the consumption channel, and say
      that what remains **here** is diffing this repository's own translation against it.
      *(completed)*
- [x] Preserve the distinction explicitly: the upstream theorem certifies BimodalLogic's own
      reference translation, not this repository's implementation, and does not relieve this
      repository of its own verification obligation (mirroring `SentenceTruth.lean`'s docstring).
      *(completed)*
- [x] Consider whether the row still belongs under "In the Lean development" at all now that the
      Lean work is done; if it is moved or re-homed under "In this repository", say plainly that
      the remaining work is wiring, and reference the open sentence-translation conformance work
      rather than describing it as unattempted. *(completed: kept the landed-theorem row under
      "In the Lean development", marked (done), and added a new "Consume the upstream
      sentence-translation fixture (open)" row under "In this repository" naming the remaining
      wiring work)*
- [x] Commit (`task 211 phase 3: ...`), staging `docs/TRUST_PIPELINE.md` by explicit path only.
      *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly two sites in `TRUST_PIPELINE.md` carry the stale claim (the "What
remains" opening paragraph, currently ~lines 286-292, and the Lean-development table row,
currently ~line 313). Confirm at implementation time with
`grep -n "deferred\|not attempted\|confirmed absent" docs/TRUST_PIPELINE.md`; if other sites
repeat the claim, fold them into this phase rather than leaving them.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - "What remains" paragraph and
  the Lean-side-translation table row.

**Verification**:
- `grep -n "confirmed absent from the local" docs/TRUST_PIPELINE.md` returns nothing.
- `grep -n "deferred, not attempted" docs/TRUST_PIPELINE.md` returns nothing.
- The rewritten prose names `sat_iff`, `SentenceTruth.lean`, and the fixture path, and contains an
  explicit statement that the upstream theorem does not verify this repository's own translation.
- Diff read-through confirms every changed hunk is markdown prose (tier `prose`).
- `git diff --stat` shows `TRUST_PIPELINE.md` as the only changed file in this phase.

---

### Phase 4: Align ADEQUACY.md's two matching S4 statements [COMPLETED]

**Goal**: `ADEQUACY.md`'s obligation table and transcription-audit residual no longer say the S4
translation is "not covered by any theorem cited here" in a way that contradicts the corrected
`TRUST_PIPELINE.md`.

**Tasks**:
- [x] Re-read `ADEQUACY.md` lines 76-84 and 296-304 after Phase 1's edits have landed. *(completed)*
- [x] Update the **S4** row of the obligation table (currently ~line 80): keep "Discharged for both
      the tense and box halves by a differential property test — §6.3", and replace "still not
      covered by any Lean theorem cited here" with the accurate position — an upstream Lean
      theorem (`sat_iff`) now exists for BimodalLogic's own reference translation, and this
      repository's own translation is not yet diffed against it. *(completed)*
- [x] Update the **Residual** paragraph (currently ~line 300) the same way, keeping the distinction
      that the upstream theorem is about the reference translation, not this one. *(completed)*
- [x] Use wording consistent with Phase 3's, so the two documents agree verbatim on the fact.
      *(completed)*
- [x] Commit (`task 211 phase 4: ...`), staging `docs/ADEQUACY.md` by explicit path only. *(completed)*

**Timing**: 0.25 hours

**Depends on**: 1, 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly two sites in `ADEQUACY.md` carry this adjacent staleness (currently
lines 80 and 300). Confirm at implementation time with
`grep -n "not covered by any" docs/ADEQUACY.md`; treat any additional hit as in scope for this
phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - S4 obligation-table row and the
  transcription-audit Residual paragraph.

**Verification**:
- `grep -n "not covered by any" docs/ADEQUACY.md` returns nothing, or only hits whose surrounding
  sentence has been corrected to the landed-upstream framing.
- `ADEQUACY.md` and `TRUST_PIPELINE.md` state the same fact about `sat_iff` — read both side by
  side and confirm no reader could derive opposite conclusions.
- Diff read-through confirms every changed hunk is markdown prose (tier `prose`).

---

### Phase 5: Consistency sweep and full gate [COMPLETED]

**Goal**: The documentation set is internally consistent on both claims, nothing else regressed,
and the task closes against the full gate rather than only per-phase tiers.

**Tasks**:
- [x] Re-run the item-1 sweep: `grep -rn "kernel-checked proof" code/src/model_checker/theory_lib/bimodal/docs/`
      and classify every hit as denying or explaining. Zero assertions.
      *(completed: 6 hits, all denials or SETTINGS.md's reservation explanation)*
- [x] Re-run the item-2 sweep: `grep -rn "BIMODAL_LOGIC_COMMIT" /home/benjamin/Projects/ModelChecker`.
      Zero hits. *(completed: zero hits under code/; reworded checker.py's docstring to avoid the
      literal token entirely — see deviation note below)*
- [x] Re-run the item-3 sweep: grep the whole `docs/` directory for remaining "deferred",
      "not attempted", "confirmed absent", "not covered by any theorem" language about S4 across
      all four documents, including `A2_GAP.md` and `SETTINGS.md`, and confirm none contradicts the
      corrected position. *(completed: found and fixed a third stale S4 site at ADEQUACY.md:567
      that Phase 4's scope hypothesis had not enumerated — see deviation note below)*
- [x] Run the full bimodal suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`.
      *(completed: 640 passed)*
- [x] Run the broader suite as the final gate:
      `PYTHONPATH=code/src pytest code/tests/ -q`. *(completed: 645 passed, 5 skipped, 0 failed;
      one Z3-internal segfault in `test_concurrent_model_building` reproduced on the first
      full-suite run but not on 3/3 isolated re-runs nor on a second full-suite run — pre-existing
      thread-contention flake in unrelated logos/solver code, not a regression from this task's
      docs-only + dead-constant changes)*
- [x] Review `git log --oneline` for this task's commits and confirm no file outside this task's
      scope was staged; confirm no foreign work was swept in (concurrent task 209 shares
      `tests/_lean_check.py`). *(completed: git log and git status confirm no foreign commits or
      out-of-scope staged files)*
- [x] Commit any final sweep corrections (`task 211: complete implementation`). *(completed)*

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None expected. Any edit this phase produces is a sweep correction in one of the four documents
  already in scope.

**Verification**:
- All three greps return the expected empty / denial-only results.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (Lean
  checker tests may clean-skip when `BIMODAL_LOGIC_PATH` is unset — a skip is acceptable, a
  failure or collection error is not).
- `PYTHONPATH=code/src pytest code/tests/ -q` shows no new failures relative to the pre-task
  baseline.
- `git status --short` is clean of unintended modifications.

---

## Testing & Validation

- [ ] `grep -rn "kernel-checked proof" code/src/model_checker/theory_lib/bimodal/docs/` — every hit
      denies the claim or explains the reservation; none asserts it.
- [ ] `grep -rn "BIMODAL_LOGIC_COMMIT" /home/benjamin/Projects/ModelChecker` — no hits.
- [ ] `PYTHONPATH=code/src python -c "import model_checker.theory_lib.bimodal.tests._lean_check"` —
      imports cleanly with the constant removed.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` — green
      (skips permitted where the Lean checkout is absent).
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` — no new failures.
- [ ] Manual cross-read: `ADEQUACY.md` §6.1/§6.2, `TRUST_PIPELINE.md` Stage 5 and "What remains",
      `A2_GAP.md` §9/§10, `SETTINGS.md` "Certificate Verification" — all four agree on what
      `entailment` licenses and on where the Lean-side S4 theorem stands.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (modified — Phases 1 and 4)
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` (modified — Phase 3)
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (modified — Phase 2)
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` (modified — Phase 2)
- `specs/211_correct_kernel_checked_proof_overclaim/summaries/01_kernel-checked-proof-overclaim-summary.md`
  (created at implementation completion)

## Rollback/Contingency

Every phase commits independently and touches at most two files, so reverting is a per-phase
`git revert <sha>` of that phase's commit — no working-tree discard is needed and none should be
attempted. Because concurrent task 209 shares `tests/_lean_check.py`, a whole-tree rollback would
risk destroying a sibling's in-flight work: do **not** run `git reset --hard`, `git checkout --`,
or `git clean -fd` on this tree. If a defensive checkpoint is wanted before Phase 2's edit, use
`bash .claude/scripts/git-snapshot.sh 211 --no-revert` (durable, non-reverting). A genuine
rollback, if one ever becomes necessary, follows `context/contracts/recovery.md`'s rollback rung
— including its out-of-scope override flag — and only after confirming no sibling task has
uncommitted work in the tree.
