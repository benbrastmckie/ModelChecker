# Research Report: Harden Certificate Wire Proof-Carrying

- **Task**: 197 - Harden certificate wire proof carrying
- **Started**: 2026-09-27T23:41:14Z
- **Completed**: 2026-09-28T00:05:00Z
- **Effort**: ~25 minutes
- **Dependencies**: Task 196 (completed)
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 6.1-6.3)
  - `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` (trust base, "What remains")
  - `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` (route table, item (f))
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (`recheck`/`recheck_json`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/model.py` (live re-check call site)
  - `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
  - `~/Projects/BimodalLogic` checkout: `specs/TODO.md` (tasks 677, 678), task 677's plan/summary,
    task 678's plan (phase headings), `BimodalTools/README.md`'s "Certificate re-verification
    protocol" section, a live invocation of `lake exe check_certificate`
- **Artifacts**: `specs/197_harden_certificate_wire_proof_carrying/reports/01_harden-certificate-wire-proof-carrying.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **One of the two named blockers has landed; the other has not.** BimodalLogic task 677
  ("Proof producing check certificate") is `[COMPLETED]`, and a live invocation of `lake exe
  check_certificate` in `~/Projects/BimodalLogic` confirms the built binary now emits
  `{"status":"countermodel","time":0,"acceptance":"entailment"}`. BimodalLogic task 678
  ("Canonical wire parser round trip") is `[IMPLEMENTING]` with phases 1-6 of 9 done, phase 7 in
  progress, and phases 8-9 not started — phase 9, "The echo field, the defect guards, and the
  joint contract," is the exact counterpart the parse-echo axis needs, and it has not shipped.
  Task 678's `.return-meta.json` shows an active/very recent dispatch (session
  `sess_1790528746_3f1c95`, HEAD commit `2026-09-27 15:38:31 -0700`), so this is in-flight work,
  not a stalled task.
- **The addition is purely additive on the wire — no coordination-requiring rename occurred.**
  Task 677 added only an output-side `"acceptance"` key (`"entailment"` or `"decided"`, absent
  reads as `"decided"`); `back`, `mid`, `fwd`, `bx`, `lassos`, `target` are untouched, and the
  input schema is untouched. This confirms task 197's premise that consuming this mode is a local
  change, not a breaking-change negotiation.
- **BimodalLogic's own README is explicit that the "fast pre-filter" claim needs both halves
  jointly**, and states in so many words that this "has not landed yet": consuming `acceptance`
  alone does *not* license writing "the Python re-checker is a fast pre-filter" into this
  repository's docs. That claim requires axis 2 (the echo comparison) as well. Task 197's own
  description asks for exactly the joint claim, so only half of it can be honestly written today.
- **There is no live per-run consumption point on this side yet.** `semantic/model.py`'s
  constructor (the actual "presentation path" a real run goes through) calls the pure-Python
  `recheck()` only; it never invokes `lake exe check_certificate`. That invocation exists only in
  the differential test tier (`tests/_lean_check.py`,
  `tests/integration/test_certificate_lean_agreement.py`), which is where `"acceptance"` can
  actually be consumed today. Wiring the Lean check into the live path at all is a separate,
  already-named, unstarted item in `TRUST_PIPELINE.md`'s "What remains" table
  ("Make the Lean check a gate on reported output"), out of this task's scope.
- **Recommendation: scope the plan to axis 1 now, keep axis 2 blocked.** Consume `"acceptance"`
  in the differential test harness and correct the doc sites that currently overstate the
  re-checker's status as a proof, but do not write the trust-base-demotion claim until BimodalLogic
  task 678 phase 9 lands. Re-research (or simply re-check) after that phase completes.

## Context & Scope

Task 197 asks for two independent hardenings of the bimodal theory's certificate wire protocol,
both gated on BimodalLogic counterpart work:

1. **Proof-carrying acceptance** — consume BimodalLogic's proof-producing `check_certificate`
   mode (its accepting branch now constructs `WitnessFamily.Refutes` via
   `WitnessFamily.joint_countermodel` rather than merely printing a verdict), and record that the
   Python re-checker has become a fast pre-filter.
2. **Parse-echo verification** — pair with BimodalLogic's canonical printer / parse-after-print
   round-trip theorem by comparing a Lean-side echo of the parsed certificate against the bytes
   this repository sent, treating a mismatch as `error`, not `rejected`.

The dispatch description records the task as `BLOCKED` on both counterparts. This research's job
was to re-check that blocker status before any planning proceeds — exactly the kind of check a
research dispatch on a `BLOCKED` task exists to perform.

## Findings

### F1 — BimodalLogic task 677 (proof-producing `check_certificate`) is complete and live

- `~/Projects/BimodalLogic/specs/TODO.md` lists task 677 as `[COMPLETED]`, with a full summary at
  `specs/677_proof_producing_check_certificate/summaries/01_proof-producing-check-certificate-summary.md`.
- The summary records: `WitnessFamily.Certifies`, `decidableCertifies`, `WitnessFamily.Refutes`,
  and `refutes_of_certifies` landed in the library; `CertificateImport.lean`'s accepting branch
  (`checkCertified`) now carries a dependent `Acceptance`-tagged `CheckOutcome` whose accepting
  constructor *carries* a `WitnessFamily.Refutes …` term — "that branch cannot be written without
  one." Zero `sorry`, zero `native_decide`/`Lean.ofReduceBool`, no new axioms; full `lake build`
  green.
- **Verified live**, not just from the summary: running
  `echo '{"target": {"premises": [], "conclusions": [{"tag":"atom","name":"p"}], "time": 0}, "bx": [], "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}]}' | lake exe check_certificate`
  from `~/Projects/BimodalLogic` prints
  `{"status":"countermodel","time":0,"acceptance":"entailment"}` — the built binary in the
  checkout this repository's own `_lean_check.py` would invoke already emits the new field.
- The addition is additive only. `BimodalTools/README.md`'s "Certificate re-verification
  protocol" section (updated by 677) states: `"rejected"` and `"error"` are byte-identical to
  before; the input schema is untouched; `"acceptance"` appears on `countermodel` only, with two
  values — `"entailment"` (Lean constructed a term of `Refutes`) and `"decided"` (the four
  decision procedures returned true, nothing more) — and **an absent field must be read as
  `"decided"`**, which is exactly why this is non-breaking and why the two repositories "can land
  this change in either order."

### F2 — BimodalLogic task 678 (canonical wire, round-trip, echo) is in progress, not done

- `specs/TODO.md` lists task 678 as `[IMPLEMENTING]`. Its plan
  (`specs/678_canonical_wire_parser_round_trip/plans/01_canonical-wire-parser-round-trip.md`)
  has 9 phases; phases 1-6 are `[COMPLETED]` (canonical JSON value/printer, certificate-record
  extraction, total fuel parser, lexical round-trip lemmas, the generic prefix round-trip theorem,
  fuel sufficiency). Phase 7 ("Schema codec and the five contract theorems") is `[IN PROGRESS]`.
  Phases 8 ("Migrate the certificate envelope onto the verified codec") and 9 ("The echo field,
  the defect guards, and the joint contract") are `[NOT STARTED]`.
- **Phase 9 is precisely the counterpart axis 2 needs**: it adds `CheckResult.toJsonWithEcho`
  (routing `checkLineToJson` through it on `countermodel` and `rejected`), a new `"echo"` output
  key, D1-D12 negative-test rows, and documents "the echo comparison is modulo surrounding
  whitespace because `main` forwards the producer's trailing newline." None of this exists yet —
  confirmed by the live invocation in F1, whose output carries no `"echo"` key.
- The task's `.return-meta.json` (`specs/678_canonical_wire_parser_round_trip/.return-meta.json`)
  shows `"status": "in_progress"`, session `sess_1790528746_3f1c95`, stage `"initializing"` — stale
  relative to the git log (phases 1-6 already committed), consistent with an actively re-dispatched,
  in-flight task rather than an abandoned one. `git log -1` in that checkout shows the HEAD commit
  timestamped `2026-09-27 15:38:31 -0700`, roughly an hour before this research ran.
- **Conclusion**: axis 2 (parse-echo verification) has no interface to consume yet on either side.
  This part of task 197 remains correctly `BLOCKED`, exactly as the dispatch description states.

### F3 — The task's own "fast pre-filter" framing requires both halves jointly, per BimodalLogic's own doc

`BimodalTools/README.md`'s certificate-protocol section, in the paragraph directly following the
`"acceptance"` key's documentation, states this explicitly:

> "The downstream payoff is jointly gated, and has not landed yet. The producing side's
> pure-Python re-checker becoming a fast pre-filter rather than part of the trust base needs two
> things, and this change is only one of them: (1) the accepting branch constructing the
> entailment, which is what `"acceptance": "entailment"` now reports; and (2) a Lean-side echo of
> the parsed certificate compared against the bytes actually sent... Until (2) lands, a consumer
> that drops its own re-check is trusting this executable's decoding, which is exactly the gap
> (2) closes."

This means: consuming `"acceptance"` now is real and useful (it upgrades what a `countermodel`
verdict *means*, from "four `Decidable` instances returned true" to "Lean constructed an entailment
term from that hypothesis"), but it does **not** license writing "the Python re-checker is now a
fast pre-filter, not part of the trust base" into `ADEQUACY.md`/`TRUST_PIPELINE.md` — that
sentence is only true once the echo comparison (axis 2) also lands, and BimodalLogic's own
authoritative doc says so. Task 197's description asks for exactly this joint claim ("record...
that the Python re-checker has become a fast pre-filter"); only the narrower, honest half of it
can be written today.

### F4 — No live per-run consumption point exists on the ModelChecker side; only the test tier does

- `semantic/model.py`'s model-structure constructor (`bimodal/semantic/model.py:62-96`) is the
  actual "presentation path" every live run with a satisfying Z3 model goes through: it extracts
  a certificate, calls the pure-Python `recheck()` (not `recheck_json`, and never `lake exe
  check_certificate`), and fails fast (`ModelConstructionError`) on anything but `"countermodel"`.
  Nothing here talks to Lean or the `BIMODAL_LOGIC_PATH` checkout at all.
- `lake exe check_certificate` is invoked only from the differential test tier:
  `tests/_lean_check.py` (`run_check_certificate`, `probe`, skip-reason resolution) and its
  consumers `tests/integration/test_certificate_lean_agreement.py` and
  `test_certificate_a2_triangle.py`. `TRUST_PIPELINE.md`'s "What remains" table already names
  "Make the Lean check a gate on reported output" as separate, unstarted work — "Stage 5 is
  currently a *sampled test tier* that clean-skips when `BIMODAL_LOGIC_PATH` is unset."
- **Implication for scope**: "extend the wire's output contract to carry it" (the acceptance mode)
  can only mean, right now, extending what the *test harness* asserts and records — e.g.
  `test_certificate_lean_agreement.py`'s `TestLeanAgreement` currently checks only `status` and
  `condition`, never `acceptance`. There is no live branch to change in `model.py` because the
  live path never reaches Lean. Making the Lean check live at all is out of this task's stated
  scope (it is its own named row in `TRUST_PIPELINE.md`) and should not be folded in silently.

### F5 — Doc sites that currently understate task 677's landed state

These sites still describe a `countermodel` verdict as *only* "the four `Decidable` instances
returned true," without qualification, and would need a one-line correction once axis 1 is
consumed (adding, not replacing, the existing sentence — the "decided" case is still real and
still what the Python re-checker itself produces):

- `docs/ADEQUACY.md` §6.2 (the paragraph this task's own description quotes).
- `docs/TRUST_PIPELINE.md`'s "The trust base" list (currently: "The re-checker implementation,
  mitigated but not eliminated by the dual check") and its "What remains" table row
  ("Consume a proof-producing checker; verify the parse" — this row should split into two rows or
  be marked half-done once axis 1 lands, since it currently bundles both halves as one line item).
- `docs/A2_GAP.md` route (f) ("Consume a proof-producing checker") — its "Cost / status" cell
  currently reads "Named in `TRUST_PIPELINE.md`'s 'What remains' as Lean-side future work"; half
  of that work is no longer future.
- `semantic/model.py`'s own module docstring / inline comments (lines ~20-25) describing the
  re-check as the thing that stands between the encoder and (SOUND)'s antecedent — accurate as
  stated (it is still describing the *live* path, which is unaffected by axis 1), but should not
  be conflated with the test-tier's now-richer verdict.

### F6 — A stale but harmless provenance pin

`tests/_lean_check.py` documents `BIMODAL_LOGIC_COMMIT = "6529c6e853f1c29358a7e74a76055f64f68b7ff7"`
as the commit differential agreement was last observed against. That commit is a confirmed
ancestor of the current BimodalLogic HEAD (from the "task 670" era, well before both 677 and 678).
The constant is documentation only — nothing enforces it — but it is now stale and should be
refreshed alongside whatever change starts asserting on `"acceptance"`, per
`test_certificate_lean_agreement.py`'s own docstring convention ("Re-run this module after
updating the BimodalLogic checkout to confirm the corpus still agrees").

## Decisions

- **Axis 1 (proof-carrying acceptance) is unblocked; axis 2 (parse-echo) is not.** This corrects
  the task description's framing of a single joint blocker into two independently-tracked ones,
  one cleared and one still open.
- **Scope for planning is axis 1 only, in the test/differential tier, plus doc corrections.**
  There is no live code path to change (F4), so implementation work is: (a) have
  `test_certificate_lean_agreement.py` (or a small addition to it) assert `verdict.get("acceptance", "decided")` on accepting fixtures and record what it means when absent vs. present;
  (b) correct the doc sites in F5 to add the narrower, accurate claim (Lean now constructs an
  entailment term on the fixtures it decides) without asserting the joint "fast pre-filter" claim;
  (c) refresh `BIMODAL_LOGIC_COMMIT` in `_lean_check.py`.
- **Do not write the "fast pre-filter" / trust-base-demotion sentence anywhere yet.**
  BimodalLogic's own README states in its own words that this claim is jointly gated and has not
  landed. Writing it now would make this repository's docs say something BimodalLogic's own
  contract explicitly disclaims.
- **Do not attempt axis 2 (parse-echo) in this round.** No `"echo"` key exists on the wire; there
  is nothing to compare against. Re-check after BimodalLogic task 678 (currently at phase 7 of 9,
  with phase 9 being the exact echo-field phase) completes.

## Recommendations

1. **Plan and implement axis 1 now**, scoped narrowly to the differential test tier and the doc
   corrections in F5 — not a change to `semantic/model.py`'s live path, which does not touch Lean.
2. **Leave axis 2 explicitly `BLOCKED`** in the plan, naming BimodalLogic task 678 (specifically
   phase 9) as the concrete unblocking event, and do not schedule work against it this round.
3. **Do not touch `back`/`mid`/`fwd`/`bx`/`lassos`/`target`.** Neither landed nor pending
   BimodalLogic change renames any of them; both additions (`"acceptance"`, the future `"echo"`)
   are output-side and additive, so no cross-repository coordination beyond reading the README is
   required for axis 1, and none will be required for axis 2 either once it lands.
4. **After BimodalLogic task 678 completes**, re-run this research (or a lighter re-check) to
   confirm the `"echo"` key's exact shape (whitespace-tolerant comparison per BimodalLogic's own
   plan) before planning axis 2, and only then write the joint "fast pre-filter" doc claim.
5. **Refresh `BIMODAL_LOGIC_COMMIT`** in `tests/_lean_check.py` to the commit actually exercised
   once axis-1 consumption is implemented and the differential suite is re-run against it.

## Risks & Mitigations

- **Risk**: implementing axis 1 alone and then writing the full joint doc claim by mistake, since
  the task description bundles both. **Mitigation**: F3 quotes BimodalLogic's own README verbatim;
  the plan should cite it directly so a future implementer does not re-derive (and get wrong) the
  same joint-gating fact.
- **Risk**: BimodalLogic task 678 lands mid-implementation of this task's axis-1 work, encouraging
  scope creep into axis 2 without a fresh check. **Mitigation**: treat axis 2 as a separate
  planning round gated on an explicit re-research, not as an opportunistic add-on to axis 1's plan.
- **Risk**: `.return-meta.json`'s stale `"in_progress"`/`"initializing"` snapshot for BimodalLogic
  task 678 could be mistaken for "not actually being worked." **Mitigation**: the git log
  timestamp (F2) contradicts that reading; this report records both so a planner does not
  conclude the task is stalled and attempt to do BimodalLogic-side work from this repository.

## Appendix

- BimodalLogic checkout: `/home/benjamin/Projects/BimodalLogic` (resolved via
  `~/Projects/BimodalLogic`, matching `_lean_check.py`'s default).
- Live verdict observed: `{"status":"countermodel","time":0,"acceptance":"entailment"}`.
- BimodalLogic task 677 summary:
  `~/Projects/BimodalLogic/specs/677_proof_producing_check_certificate/summaries/01_proof-producing-check-certificate-summary.md`.
- BimodalLogic task 678 plan:
  `~/Projects/BimodalLogic/specs/678_canonical_wire_parser_round_trip/plans/01_canonical-wire-parser-round-trip.md`
  (phase headings: 1-6 `[COMPLETED]`, 7 `[IN PROGRESS]`, 8-9 `[NOT STARTED]`).
- BimodalLogic protocol doc: `~/Projects/BimodalLogic/BimodalTools/README.md`, "Certificate
  re-verification protocol" section (lines ~76-216 as read).
