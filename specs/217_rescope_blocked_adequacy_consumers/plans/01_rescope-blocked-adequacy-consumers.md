# Implementation Plan: Task #217

- **Task**: 217 - rescope_blocked_adequacy_consumers
- **Status**: [NOT STARTED]
- **Effort**: 3.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/217_rescope_blocked_adequacy_consumers/reports/01_rescope-blocked-adequacy-consumers.md
- **Artifacts**: plans/01_rescope-blocked-adequacy-consumers.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Two blocked ModelChecker tasks carry recorded blockers that no longer match the live
BimodalLogic tree: project 198 (`a3_compute_bounds_from_closure`) and project 200
(`extend_bimodal_to_stability_modal`). This plan rewrites both descriptions in place through
`state-write.sh`, regenerates `TODO.md` in the same pass, and commits. Nothing under `code/`
is touched and the BimodalLogic repository is never written to. Definition of done: both
descriptions are self-contained, cite upstream results by fully-qualified declaration name,
name the blockers that are actually outstanding, both entries remain `status: blocked`, and
`TODO.md` renders the new text.

### Research Integration

The research report verified every dispatch claim against the live upstream tree and found
the dispatch's own Entry 2 replacement stale. Three findings drive this plan:

1. **Entry 1**: `f` exists in closed form as
   `f(k) = max((2k+1)·2^k, 2·2^k)`, supplied by
   `FormalSystem.Metalogic.Decidability.exists_witnessFamily_of_not_validZTime`. But the
   discharge holds only at A1's restricted scope (`Γ = []`, single conclusion), a scope no
   countermodel example in `code/src/model_checker/theory_lib/bimodal/examples.py` occupies.
   Both the back/fwd periodicity result and the general-consequence form (upstream's new
   **A1-Γ** adequacy row) are open and unowned by any upstream task. Research recommends
   keeping `blocked`; this plan adopts that recommendation and records the reasoning in the
   entry itself, as the dispatch requires.
2. **Entry 2**: the dispatch's proposed three-task replacement blocker is stale. Upstream 694
   is abandoned and folded into 696; 695 is completed. The blocker must name **696**
   (`stability_modal_substrate_design`, `researched`) and **703**
   (`lplus_compression_and_completeness`, `not_started`, deps `[695, 696]`), the latter created
   by upstream's own survey task 700, which names this ModelChecker task by number.
3. **Root cause**: stated in shape/reflexivity form, never the temporal form. Verified at
   `snce_share_congr`'s two-reading proof, at `share_refl`/`share_symm`/`share_trans`, and at
   `SharingSkeleton.Thread`'s `step` field being *defined* via `share`. The until-side gate
   family is machine-checked in an archived upstream probe, not landed in the library.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context, and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:
- Rewrite project 198's description so its blocker names the back/fwd periodicity result and
  the A1-Γ general-consequence obligation, records that `f` exists and cites it by
  fully-qualified name, splits mid from back/fwd, and states the deliberate status choice and
  its reason.
- Rewrite project 200's description so its blocker names upstream 696 and 703 with their
  actual current statuses, states the root cause in shape/reflexivity form, and describes the
  until-side gate family as probe-only.
- Keep both entries at `status: blocked`.
- Route every `specs/state.json` write through `state-write.sh` and regenerate `TODO.md` in
  the same pass.
- Keep both descriptions self-contained: actionable without re-deriving anything upstream.

**Non-Goals**:
- Editing any file under `code/`, including `bimodal/examples.py` (sibling task 219 owns it).
- Writing to `/home/benjamin/Projects/BimodalLogic` in any form, including its `specs/`.
- Fixing project 200's `dependencies: [193, 194, 197]` array, which names ModelChecker tasks
  unrelated to the upstream tasks its prose discusses. This pre-existing mismatch is flagged
  in the rewritten description text only; the array itself stays untouched.
- Changing either entry's `status`, `task_type`, `dependencies`, or `topic` fields.
- Creating, abandoning, or re-scoping any other task.
- Hand-editing `specs/state.json` or `specs/TODO.md` with an editor tool.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Upstream 696/703 change status between research and implement (both repos under same-day development) | H | M | Phase 1 re-reads `/home/benjamin/Projects/BimodalLogic/specs/state.json` immediately before drafting and records live statuses; drafts use the observed values, not the report's. |
| The until-side gate family lands in the library, making "probe-only" wording wrong | M | L | Phase 1 re-greps `FormalSystem/` for `untl_shift_share_congr`; Phase 3 picks wording from the observed result. |
| Sibling task 219 edits `bimodal/examples.py` concurrently, changing the premise/conclusion counts Entry 1 cites | M | M | Phase 1 re-derives the counts from the live file and Phase 2 uses the observed numbers; Entry 1 phrases the claim as a dated observation, not a standing invariant. |
| `specs/state.json` is written concurrently by sibling tasks 216 and 219 via their own orchestrate postflight | H | H | All writes go through `state-write.sh`, whose fail-closed `specs/.scope-lock` mutex serializes them. Never hand-edit the file. Re-read immediately before writing. |
| The commit stages sibling rows that rode along inside `state.json` | M | H | `state.json` is one file, so sibling rows cannot be split out. Stage the two files by explicit path only, review `git diff --staged` first, and note any foreign rows in the commit body rather than reverting them. |
| Rewriting wholesale discards still-valid scope prose from either entry | M | M | Preserve each entry's substantive scope paragraphs verbatim; replace only the trailing blocker clause and append a dated provenance block. |
| A future reader transcribes the stale blocker because it was left in the text | M | M | The false blocker sentence is replaced, not merely annotated. Phase 5 greps the rendered `TODO.md` to confirm the superseded phrases are gone. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Re-verify upstream and local facts against the live trees [NOT STARTED]

**Goal**: Replace every fact the drafts will assert with a freshly observed value, so no
stale claim from the report or the dispatch is transcribed.

**Tasks**:
- [ ] Read `/home/benjamin/Projects/BimodalLogic/specs/state.json` and record the current
      `status` and `dependencies` of upstream projects 682, 683, 684, 685, 693, 694, 695,
      696, 700, 703. Note any that differ from the research report.
- [ ] Confirm `FormalSystem.Metalogic.Decidability.exists_witnessFamily_of_not_validZTime`
      resolves in `WitnessFamily/Compression/Family.lean` and record its file and line.
- [ ] Confirm the four `PlusWitnessFamily/Incompleteness.lean` declarations resolve:
      `snce_share_congr`, `not_plusCertifies_stabSnce`,
      `not_plusCertifies_stabSnce_premise`, `not_plusValidZTime_stabSnce`.
- [ ] Confirm `share_refl`/`share_symm`/`share_trans` in `WitnessFamily/Sharing/Basic.lean`
      and the `step` field of `SharingSkeleton.Thread` in `WitnessFamily/Sharing/Skeleton.lean`.
- [ ] Confirm `plusSnce_thread_step` and `plusThread_share_pred` in `PlusWitnessFamily/Fulfil.lean`.
- [ ] Grep `FormalSystem/` for `untl_shift_share_congr`, `not_plusCertifies_stabUntl`,
      `not_plusValidZTime_stabUntl`. Record whether they are still probe-only.
- [ ] Re-derive from `code/src/model_checker/theory_lib/bimodal/examples.py`, read-only:
      the number of countermodel examples, how many have empty premise lists, and
      `MD_CM_1`'s conclusion count.
- [ ] Re-read projects 198 and 200 in `/home/benjamin/Projects/ModelChecker/specs/state.json`
      and save each current description verbatim to the scratchpad.
- [ ] Write the observed values to a scratchpad notes file for Phases 2 and 3 to consume.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The report asserts 13 countermodel examples, zero with empty premise
lists, `MD_CM_1` at two conclusions, and upstream statuses 694 abandoned / 695 completed /
696 researched / 703 not_started. Each is a hypothesis. Confirm by direct `jq` over the
upstream `state.json` and `grep` over `examples.py`; if any value differs, the observed value
wins and Phases 2 and 3 use it.

**Files to modify**:
- None. This phase is read-only. Scratchpad notes only.

**Verification**:
- Every declaration name listed above either resolves with a recorded file and line, or is
  recorded as absent with the search command that established it.
- Both current descriptions are saved verbatim to the scratchpad.
- `git status --porcelain` shows no new or modified tracked file from this phase.

---

### Phase 2: Draft the replacement description for project 198 [NOT STARTED]

**Goal**: Produce the full replacement text for `a3_compute_bounds_from_closure`, ready to
write, with no edits to `state.json` yet.

**Tasks**:
- [ ] Preserve verbatim the existing scope prose: the compute-`f(|C|)`-from-the-closure
      deliverable, the honest-reporting deliverable, and the frame-class caveat.
- [ ] Replace the trailing `BLOCKED on BimodalLogic's compression task ...` sentence.
- [ ] Add: `f` now exists in closed form,
      `f(k) = max((2k+1)·2^k, 2·2^k)` at `k = |closureOf (Γ ++ Δ)|`, supplied by
      `FormalSystem.Metalogic.Decidability.exists_witnessFamily_of_not_validZTime`, and
      upstream's A3 adequacy row is reclassified from vacuous to live and open.
- [ ] Record the scope split: the `mid` clause is a magnitude condition, satisfiable at
      `mid >= f(|C|)`, and is actionable; the `back`/`fwd` clause is not, because the landed
      theorem bounds segment lengths and not minimal periods, so representability against a
      registry folding by exact modulus still needs a bounded sweep.
- [ ] Record the restricted-scope qualifier: the landed instance holds only at `Γ = []` with a
      single conclusion, while the countermodel examples in this repository's bimodal
      `examples.py` carry non-empty premise lists (with `MD_CM_1` at two conclusions), using
      the counts observed in Phase 1 and dating the observation.
- [ ] Record the general consequence form as a separate open upstream obligation, naming
      upstream's **A1-Γ** adequacy row, and note it has no owning upstream task.
- [ ] Record the back/fwd periodicity obligation as upstream ADEQUACY.md section 7.1(iii-a)'s
      bounded sweep, and note it likewise has no owning upstream task.
- [ ] State that the honest-reporting half grows in importance rather than shrinking: a bare
      reading of "f now exists" overclaims relative to what landed, and the
      never-report-validity discipline is what prevents that overclaim reaching users.
- [ ] State the deliberate status choice explicitly: **remains blocked**, because the
      actionable mid half is scoped to an A1 instance no real example occupies, and the
      justification that would extend it is unproved and unowned. Give this reasoning in the
      entry text, per the dispatch's instruction to say which was chosen and why.
- [ ] Append a dated provenance line naming the upstream tasks consulted, so a future reader
      can re-check without re-deriving.
- [ ] Save the draft to the scratchpad as a single plain-text file.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- None yet. Scratchpad draft only; the write happens in Phase 4.

**Verification**:
- The draft names `exists_witnessFamily_of_not_validZTime` by fully-qualified name.
- The draft contains no sentence asserting there is no `f` to read.
- The draft states the chosen status and its reason in one identifiable sentence.
- The draft reads as self-contained: no claim requires opening the upstream repository to
  act on.

---

### Phase 3: Draft the replacement description for project 200 [NOT STARTED]

**Goal**: Produce the full replacement text for `extend_bimodal_to_stability_modal`, with the
blocker restated against the tasks that are actually outstanding and the root cause stated in
shape form.

**Tasks**:
- [ ] Preserve verbatim the existing scope prose: the operator and truth conditions, the
      certificate datatype replacement, the Z3 re-encoding and box faithfulness, the wire
      contract and re-checker, the search bounds, and the iteration-machinery revisit.
- [ ] Replace the trailing `BLOCKED on the four verified-side tasks ...` sentence.
- [ ] Record that the four originally-named upstream tasks (682, 683, 684, 685) are all
      completed, so a status-only check reads as discharged, and that this reading is wrong.
- [ ] Record what actually landed: a refutation, not a construction. The six-condition L-plus
      substrate is proved to certify no instance of the stability modal, in either target
      placement, at any time or size, and the corresponding integer-time non-validity is
      proved. Cite `PlusSharingWitnessFamily.snce_share_congr`,
      `...not_plusCertifies_stabSnce`, `...not_plusCertifies_stabSnce_premise`, and
      `...not_plusValidZTime_stabSnce`. State that the empty certificate class is a
      completeness failure, not a vacuity.
- [ ] State the root cause in **shape form only**. Any truth clause of the form "for all j
      accessible from i, phi holds at i if and only if `<condition mentioning only j>`" is an
      invariance axiom for phi across the accessibility class, derivable from reflexivity
      alone by instantiating the clause twice and chaining the two biconditionals. Cite
      `snce_share_congr`, whose proof is exactly that chaining via `share_refl`. Note the
      sharing relation is an equality of representatives, hence an equivalence
      (`share_refl`/`share_symm`/`share_trans`), so the invariance runs across the whole class.
- [ ] State the deeper conflation: one relation carries two algebraically incompatible jobs.
      The stability modal needs an equivalence (same state, different history), while one-step
      succession must be neither symmetric nor transitive, yet `SharingSkeleton.Thread`'s
      `step` field is *defined* as `K.share (u+1) (idx u) (idx (u+1))`, so succession inherits
      symmetry and transitivity and past truth becomes a function of the present state.
- [ ] **Do not** write the temporal explanation. Explicitly record that the "snce quantifies
      at the label's own time while untl escapes at the successor time" account is refuted,
      and cite `plusSnce_thread_step` showing the snce clause is the exact mirror of the untl
      clause relative to `Thread.step`, with both clauses collapsing.
- [ ] Describe the until-side gate family (`untl_shift_share_congr`,
      `not_plusCertifies_stabUntl`, `not_plusValidZTime_stabUntl`) using the Phase 1 grep
      result: as machine-checked in an archived upstream probe and not yet landed in the
      library, unless Phase 1 observed otherwise.
- [ ] Restate the blocker as upstream **696** `stability_modal_substrate_design` (design
      authority for the state-sharing structure, the histories characterization, and the box
      condition) and **703** `lplus_compression_and_completeness` (supplies the compression
      bound; gated on 696). Give each one's status as observed in Phase 1, not as
      "not started".
- [ ] Record that upstream 694 `sharing_substrate_trans_redesign` was evaluated and abandoned,
      its `trans` candidate folded into 696's own design authority, and that upstream 695
      `plus_carrier_normalization_int_transfer` is completed and now sits upstream of 703
      rather than blocking this task directly.
- [ ] Record that there is no L-plus compression subtree yet, and that upstream states it is
      worth building only against a corrected condition set, since that subtree is precisely
      what this task would consume. Cite this to upstream 703 rather than as a free-standing
      fact.
- [ ] Add a one-line flag that this entry's own `dependencies: [193, 194, 197]` array names
      ModelChecker tasks unrelated to the upstream tasks this prose discusses, left uncorrected
      here deliberately and available for whoever next maintains the entry.
- [ ] State that the status stays **blocked**: the original reasoning is superseded while its
      conclusion stands.
- [ ] Append a dated provenance line naming the upstream tasks consulted.
- [ ] Save the draft to the scratchpad as a single plain-text file.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- None yet. Scratchpad draft only; the write happens in Phase 4.

**Verification**:
- The draft names 696 and 703 and does not present either as "not started" unless Phase 1
  observed that value.
- The draft contains no temporal-asymmetry explanation of the collapse, and does contain the
  reflexivity/invariance mechanism.
- The draft cites at least `snce_share_congr`, `share_refl`, `Thread.step`, and
  `plusSnce_thread_step` by name.
- The draft does not describe the until-side gate family as a landed library theorem, unless
  Phase 1 observed it landed.
- The draft states the status stays blocked.

---

### Phase 4: Apply both descriptions and regenerate TODO.md [NOT STARTED]

**Goal**: Write both replacement descriptions into `specs/state.json` through the mutex-guarded
writer and regenerate `TODO.md` in the same pass.

**Tasks**:
- [ ] Re-read projects 198 and 200 from `specs/state.json` immediately before writing and
      confirm each description still matches the copy Phase 1 saved. If a sibling changed
      either, stop and re-reconcile before proceeding.
- [ ] Apply the Entry 1 draft:
      ```bash
      bash .claude/scripts/state-write.sh \
        '.active_projects |= map(
           if .project_number == ($num | tonumber)
           then .description = $desc
              | .last_updated = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))
           else . end)' \
        --session-id "$session_id" \
        --arg num 198 \
        --arg desc "$(cat "$SCRATCH/198-description.txt")"
      ```
- [ ] Apply the Entry 2 draft with the same filter, `--arg num 200`,
      `--arg desc "$(cat "$SCRATCH/200-description.txt")"`, and `--regen-todo` on this second
      call so `TODO.md` regenerates once, after both writes land.
- [ ] Confirm both calls exited 0. On exit 2 (mutex held by a sibling), wait and retry rather
      than bypassing the writer.
- [ ] Run `bash .claude/scripts/validate-state.sh` and confirm it passes.
- [ ] Confirm `jq -e '.active_projects[] | select(.project_number==198 or .project_number==200)
      | select(.status=="blocked")'` returns both entries, i.e. neither status changed.

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts it modifies exactly two files, `specs/state.json` and
`specs/TODO.md`, and exactly two `active_projects` entries. Confirm with
`git status --short` limited to those two paths, and with a `jq` diff of the project-number
set whose `description` or `last_updated` changed. Sibling rows changed concurrently by tasks
216 or 219 may also appear in `state.json`; those are expected and must not be reverted.

**Files to modify**:
- `specs/state.json` - replace the `description` of projects 198 and 200, refresh their
  `last_updated`. No other field on either entry changes.
- `specs/TODO.md` - regenerated, never hand-edited.

**Verification**:
- `validate-state.sh` exits 0.
- Both entries still read `"status": "blocked"`.
- `dependencies`, `task_type`, `topic`, `project_name`, and `created` are byte-identical to
  their pre-write values on both entries.
- `git status --short` shows `specs/state.json` and `specs/TODO.md` modified and no new file.

---

### Phase 5: Verify the rendering and commit [NOT STARTED]

**Goal**: Confirm the rendered task list carries the new text and no superseded claim, then
commit the two files.

**Tasks**:
- [ ] Read the rendered entries for 198 and 200 in `specs/TODO.md` end to end and confirm each
      matches its draft.
- [ ] Grep `specs/TODO.md` to confirm the superseded phrases are gone: "there is no f to read
      until it lands" from Entry 1, and "BLOCKED on the four verified-side tasks" plus "until
      the agreement lemma lands" from Entry 2.
- [ ] Grep both entries to confirm no temporal-asymmetry phrasing of the collapse survives.
- [ ] Confirm no file under `code/` is modified by this task:
      `git status --short -- code/` must be empty of this task's changes. Any modification
      there belongs to sibling task 219 and must be left alone, not staged.
- [ ] Confirm `/home/benjamin/Projects/BimodalLogic` has no modification attributable to this
      task.
- [ ] Review `git diff --staged` after staging, before committing.
- [ ] Stage by explicit path only: `git add -- specs/state.json specs/TODO.md`. Never
      `git add -A`, never a directory or glob pathspec.
- [ ] Commit with `task 217: create implementation plan`-style convention adapted to the
      operation, including the session ID in the body, and noting in the body if sibling rows
      rode along inside `state.json`.

**Timing**: 0.25 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the commit contains exactly two paths. Confirm with
`git show --stat --name-only HEAD` after committing; if a third path appears, the staging was
wrong and must be corrected before the task closes.

**Files to modify**:
- None beyond Phase 4's two files. This phase stages and commits them.

**Verification**:
- `git show --name-only HEAD` lists exactly `specs/state.json` and `specs/TODO.md`.
- The superseded-phrase greps return no match inside either entry.
- No path under `code/` appears in the commit.

---

## Testing & Validation

- [ ] `bash .claude/scripts/validate-state.sh` exits 0 after the writes.
- [ ] `jq -e '.'` parses `specs/state.json` cleanly.
- [ ] Both projects 198 and 200 read `"status": "blocked"` after the writes.
- [ ] `dependencies`, `task_type`, `project_name`, `topic`, and `created` are unchanged on
      both entries.
- [ ] `specs/TODO.md` renders both new descriptions in full, with no truncation at the first
      newline.
- [ ] The superseded blocker phrases are absent from both rendered entries.
- [ ] Every declaration name cited in either entry resolved during Phase 1, with file and line
      recorded.
- [ ] `git status --short -- code/` shows no change attributable to this task.
- [ ] No file under `/home/benjamin/Projects/BimodalLogic` was written.
- [ ] The commit contains exactly two paths.

## Artifacts & Outputs

- `specs/state.json` - projects 198 and 200 with rewritten `description` and refreshed
  `last_updated`; all other fields unchanged.
- `specs/TODO.md` - regenerated from state.json by `generate-todo.sh`.
- `specs/217_rescope_blocked_adequacy_consumers/summaries/01_rescope-blocked-adequacy-consumers-summary.md`
  - written by the implement phase's postflight.
- Scratchpad drafts and verification notes (not committed).

## Rollback/Contingency

`specs/state.json` is concurrently written by sibling tasks this same cycle, so a working-tree
rollback is not an appropriate recovery here and must not be attempted: it would discard
sibling rows along with this task's own.

- **Before Phase 4**, nothing is written, so there is nothing to roll back. Phase 1 saves both
  original descriptions verbatim to the scratchpad specifically so a revert is a forward
  re-write rather than a tree operation.
- **If Phase 4 writes the wrong text**, recover by re-running the same `state-write.sh`
  invocation with the saved original description as `--arg desc`, then regenerate `TODO.md`.
  This is a normal forward write through the mutex and is safe under concurrency.
- **If a write partially lands** (one entry written, the other not), re-run only the failing
  entry's call. The filter is idempotent: applying it twice with the same `--arg desc` is a
  no-op beyond `last_updated`.
- **If `validate-state.sh` fails after a write**, do not hand-edit the file. Restore the saved
  original for the affected entry through `state-write.sh`, re-validate, then re-diagnose the
  draft.
- **Do not** run `git-snapshot.sh` in its default reverting mode, `git reset --hard`,
  `git checkout -- specs/state.json`, or `git restore specs/state.json` at any point in this
  task. If a durable checkpoint is genuinely wanted before Phase 4, use
  `bash .claude/scripts/git-snapshot.sh 217 --no-revert`, which is durable and does not revert
  the working tree.
- **If a foreign commit or foreign uncommitted modification is observed**, stop and report it
  after checking `git log` to confirm the work is not this task's own, per the territory
  contract.
