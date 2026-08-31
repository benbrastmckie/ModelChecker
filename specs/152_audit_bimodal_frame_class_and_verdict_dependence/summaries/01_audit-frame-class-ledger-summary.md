# Implementation Summary: Audit Bimodal Frame Class and Verdict Dependence

- **Task**: 152 - Audit bimodal frame class and verdict dependence
- **Plan**: `specs/152_audit_bimodal_frame_class_and_verdict_dependence/plans/01_audit-frame-class-ledger.md`
- **Status**: All 6 phases completed

## What this audit settled

**Phase 1 — reference re-verification.** All 21 code/Lean citation rows in the research report's
Section 4 table were re-opened against the current tree. Result: zero drift. One documentation
annotation was recorded (a retired `lem:fibers` anchor now appears in `Extension.lean`'s printed
proof-chain diagram, without changing the chain's substance). The re-run `grep -rn "serial"
semantic/` still returns nothing, confirming *Seriality* remains unasserted.

**Phase 2 — asserted vs. free (the audit's central finding).** The report's original headline
("four missing axioms") conflated two different questions: which axioms `thm:extension`'s proof
chain *consumes* (four: Seriality, Interpolation, Limit, Spherical) versus which axioms
ModelChecker must *newly assert* (only two: Seriality, Interpolation). *Limit* and *Spherical* are
already **free** — this audit checked, not merely cited, each discharging lemma's hypotheses
against ModelChecker's actual encoding:
- *Spherical* is discharged by `TaskFrame.spherical_of_finite`, whose sole hypothesis is
  `[Finite W]`; ModelChecker's `WorldStateSort = BitVecSort(N)` satisfies it directly, and the
  lemma is proved independent of any duration-type structure.
- *Limit* is discharged by `TaskFrame.limit_of_succOrder`, whose hypotheses are
  `[SuccOrder D] [NoMaxOrder D]` (satisfied because the duration sort is Z3 `Int` = ℤ) plus an
  unconditional nullity biconditional — exactly ModelChecker's existing, unguarded
  `build_nullity_identity_constraint`. The proof only ever needs the hypothesis at duration 0/1,
  so the `is_valid_duration` bound (a value-level guard, not a sort restriction) does not block it.
- BimodalLogic's own `IntPresentation.toTaskFrame` is a precedent for the identical `(D, W)`
  configuration and states the same conclusion in its own docstring: seriality is the sole
  obligation a finite-carrier ℤ-duration presentation pays by hand.
- The duration-domain gap (`\D` must be a nontrivial ordered abelian group; `is_valid_duration`
  bounds to `(-M, M)`) does not block the Limit/Spherical discharge, but **is** genuinely
  load-bearing for the follow-on frame-axiom task: if Seriality/Interpolation are asserted
  duration-guarded (the natural performance-motivated choice), the result is not literally the
  unbounded `TaskFrame ℤ` `thm:extension`'s Lean statement needs without a stated embedding
  argument. Recorded as an open gap for that task, not resolved here.

**Phase 3 — the undecided baseline cells.** `BM_TH_1`/`BM_TH_2`'s baseline (with-abundance) side
was re-run at a capped 90s (3x the original 30s) on a host with elevated but not extreme load
(6.79→6.35, vs. the original run's 4.62; this session's concurrent sibling-agent dispatches did
not clear within a bounded 2-minute wait). **Both remained inconclusive at 90s** — recorded as
`inconclusive-at-90s`, per the plan's own pre-written contingency, rather than left as a bare
`inconclusive` or retried further. `BM_TH_3`/`BM_TH_4` — the two cells the whole regression net's
credibility rests on — both reproduced their clean flips exactly. `core.py`/`operators.py`/
`examples.py` remained untouched throughout (`git status --short` clean).

**Phase 4 — the baseline as a re-runnable regression net.** `baselines/README.md` documents what
the baseline measures, exact invocation commands (verified: the Phase 3 script is byte-identical
to the already-executed, successfully-run scratchpad copy; both scripts pass `py_compile`), the
comparison procedure ("explain every flip, never absorb one silently — a flip is not automatically
a regression"), and all four known caveats (the pervasive `truth_value_at()` interpretation error
present on every run and unrelated to verdicts; `BM_CM_1`'s documented `unstable` timing flake;
`TN_CM_2`'s separately-documented timeout; `MF_MODAL_FUTURE_TH`/`BM_TH_5` as pre-existing
non-theorems).

**Phase 5 — the standalone `task_restriction` verdict.** Promoted to
`reports/02_task-restriction-verdict.md`: `task_restriction` remains an independent gap because it
couples `task_rel` to the solver's `is_world`/`world_function` enumeration, while every `def:frame`
axiom (all four, not just the two newly asserted) is stated purely over the abstract relation —
confirmed by inspection of both the Z3-encoding analogues and the Lean predicates. The existing
soundness-analysis comment's claim that operators never read `task_rel` was re-checked and found
*stronger* than stated: `grep -n "task_rel" operators.py` returns zero matches file-wide, not just
"none of the cited methods." The SAT/UNSAT-asymmetry conclusion stands unchanged.

**Phase 6 — propagation and closure.** Task 153's opening premise ("two of the paper's four frame
axioms are missing... precisely the two the extension proof consumes") was corrected in both
`specs/state.json` and the regenerated `specs/TODO.md` to state the Phase 2 finding; its existing
Deliverable 3 (which already argued Limit/Spherical are free) was left intact since Phase 2
confirms rather than contradicts it. Task 154 did not carry the superseded phrasing and needed no
premise correction; both entries gained pointers to `baselines/README.md` and
`reports/02_task-restriction-verdict.md`.

## What this audit deliberately left open

- **The duration-domain embedding question** (Section 1.2a): whether Seriality/Interpolation, once
  asserted, will constitute a genuine unbounded `TaskFrame ℤ` or only a duration-bounded
  approximation requiring a stated embedding argument. This is squarely the follow-on frame-axiom
  task's Deliverable 4, not resettled here.
- **The pervasive interpretation error** (`BimodalProposition.truth_value_at() missing 1 required
  positional argument: 'eval_time'`, present on every baseline run, both sessions): documented as
  a caveat per the task's explicit non-goal; not fixed.
- **`BM_CM_1`'s `unstable` timing flake**: two more data points recorded (7.66s and 7.67s across
  the two sessions), neither meeting the documented 20-run/20-seed exit criteria; not
  re-adjudicated.
- **`BM_TH_1`/`BM_TH_2`'s baseline side**: still undecided at the capped 90s ceiling. The
  abundance-dependence conclusion for both continues to rest on the no-abundance side's fast,
  unambiguous SAT result plus pre-existing code-comment/example-file corroboration — unchanged
  from the original report's basis, now reinforced by a second, longer timeout rather than
  resolved by one.

## Non-goals respected

No change was made to `core.py`, `operators.py`, or `examples.py` (confirmed via `git status
--short` on the theory directory throughout). `task_restriction` was not enabled. No
`ARCHITECTURE.md` frame-class table was written (that remains the follow-on frame-axiom task's
Deliverable 3, per the plan's explicit non-goal). All monkeypatching for the baseline re-runs
stayed process-local to throwaway scripts under `baselines/`.

## What the follow-on tasks must do with the baseline

Both `specs/TODO.md` entries (153, 154) now point to `baselines/README.md` for the concrete
re-run/diff procedure and to `reports/02_task-restriction-verdict.md` for the `task_restriction`
question. The regression surface to explain on any frame-class change is exactly `BM_TH_1`–
`BM_TH_4`; every other example's verdict is uninformative for the abundance question specifically
(though still worth investigating on its own terms if it flips unexpectedly).

## Plan Deviations

- **Phase 3's "decided" goal not fully met for `BM_TH_1`/`BM_TH_2`.** The plan's goal statement
  says "Convert the `BM_TH_1`/`BM_TH_2` baseline sides from `inconclusive` to decided." Both
  remained `inconclusive` even at the capped 90s re-run. This is not a deviation from the plan's
  own logic — the plan's Rollback/Contingency section explicitly anticipates this exact outcome
  ("if `BM_TH_1`/`BM_TH_2` remain undecided at the capped budget, keep the original recorded
  values, mark the cells `inconclusive-at-{N}s`... which is what the report already argues, so the
  deliverable is not blocked by this outcome") and the Phase 3 task list's own item 4 names the
  same fallback. Recorded here for visibility rather than treated as silent underdelivery.
- **Host-quiet mitigation partially honored.** The plan's Phase 3 mitigation table calls for
  deferring the re-run entirely if host load exceeds the original run's condition. A bounded
  2-minute wait was used instead of an unbounded defer, because this audit executed inside a
  shared multi-agent orchestration session with several concurrent sibling task dispatches that
  were not expected to clear on a bounded timeline; deferring indefinitely would have blocked the
  entire task on a condition outside this agent's control. Both start and end load are recorded
  honestly (6.79→6.35, vs. the original 4.62) rather than omitted or misrepresented as quiet.
- **`baselines/01_abundance-removal-run.log` is not tracked by git.** The project's `*.log`
  gitignore rule applies to this file; it exists on disk with the full appended Phase 3
  transcript but was not force-added. The durable, tracked record of the Phase 3 host
  conditions and results lives in `01_frame_class_and_verdict_ledger.md`'s Section 2.2 and in
  `01_abundance-removal-verdicts.json`'s `rerun_20260831_phase3` fields, both of which are tracked.
- All other phases followed the plan as written; no other deviations.

## Artifacts

- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` (amended: Sections 0, 1.2, 1.2a, 2.2, 3, 4.1)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` (new)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md` (new)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-verdicts.json` (refreshed cells for `BM_TH_1`–`BM_TH_4`)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-run.log` (appended transcript, not git-tracked per project `.gitignore`)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/02_phase3-rerun-script.py` (new)
- `specs/TODO.md` and `specs/state.json` (tasks 153/154 description fields corrected)
