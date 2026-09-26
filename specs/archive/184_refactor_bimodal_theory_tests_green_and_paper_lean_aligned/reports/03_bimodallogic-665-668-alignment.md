# Alignment review: BimodalLogic tasks 665-668 against the certificate redesign reports

- **Task**: 184 - Refactor bimodal theory tests green and paper lean aligned
- **Started**: 2026-09-24T19:00:00Z
- **Completed**: 2026-09-24T19:45:00Z
- **Effort**: about 0.75 hours (archive reads in `~/Projects/BimodalLogic/`, cross-check against reports 01-02)
- **Dependencies**: `01_finite-certificate-redesign.md`, `02_partial-model-formal-results.md`
- **Sources/Inputs**:
  - `~/Projects/BimodalLogic/specs/archive/665_witness_family_certificate_soundness/summaries/01_witness-family-certificate-soundness-summary.md`
  - `~/Projects/BimodalLogic/specs/archive/666_check_certificate_executable/summaries/01_check-certificate-executable-summary.md`
  - `~/Projects/BimodalLogic/specs/archive/667_tableau_bridge_branch_gates_and_frame_class/summaries/01_branch-gates-frame-class-summary.md`
  - `~/Projects/BimodalLogic/specs/archive/668_clear_c34b_residual_enforce_c34b/summaries/01_clear-c34b-residual-enforce-summary.md`
  - `~/Projects/BimodalLogic/specs/TODO.md` (task 623 entry, post-revision)
  - `~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Basic.lean`
  - `~/Projects/BimodalLogic/BimodalTools/README.md` (`## Tableau bridge protocol`, `## Certificate re-verification protocol`)
- **Artifacts**: this report
- **Standards**: report-format.md
- **User focus**: review BimodalLogic tasks 665-668, recently completed, for alignment with this task's authoritative redesign reports (01, 02)

## Executive Summary

1. **All four BimodalLogic tasks that map to the redesign reports' recommendations are complete
   and match the design with no drift.** 665 = report 02's "Witness-family certificates:
   soundness" (T1/T1'/T2/T3); 666 = the `check_certificate` executable named in report 01's New B
   and report 02 recommendation 3; 667 = report 01 section 6.2's "run the branch gates on
   `invalid`" task. Task 623 was revised exactly as recommended: it now depends on 665 and its
   description explicitly defers to 665 for the soundness half. Task 668 (C34b Lean-invariant gate
   enforcement) is unrelated Lean-tooling maintenance with no bearing on this task.
2. **The certificate JSON wire format is no longer a proposal; it is a fixed, documented, external
   contract.** BimodalLogic's own README states renaming `back`/`mid`/`fwd`/`bx`/`lassos`/`target`
   is "a breaking change on the producing side." ModelChecker's certificate-export deliverable
   (dispatch DELIVERABLES, redesign report New B) must mirror this shape field-for-field, not
   just "in spirit." Full schema is reproduced in section 2 below.
3. **The round-trip re-verification target already exists and is live**: `lake exe
   check_certificate` (task 666) takes exactly this JSON on stdin and returns a
   `countermodel`/`rejected`/`error` verdict. Report 01's New B ("a round-trip test through a Lean
   re-verification executable") has nothing left to wait on; it can be planned as a direct
   integration, not a future dependency.
4. **One planning-relevant fact for the follow-on tableau-oracle task (New A), not for 184 itself**:
   at frame class `ZTime`, `region_label_check` and `temporal_witness_check` are *measured false on
   every open branch today* (recorded in BimodalLogic's own protocol docs as a known, named fact,
   not a bug). Under report 01 section 5's own verdict matrix, an `invalid` result only counts as
   evidence when the branch gates pass — so today, every ZTime `invalid` verdict from the tableau
   bridge is heuristic (`gated: false`) and logged-only, never evidential, until a separate,
   already-scoped-and-deferred BimodalLogic repair lands. This should be stated as an expected
   starting condition in New A's plan, not discovered as a surprise mid-implementation.
5. **No revision to reports 01 or 02, or to task 184's description, is needed.** The Lean
   development implemented exactly the searched object, predicates, and model those reports
   specify (same predicate names: `LocalCoherentLab`, `FulfillingLab`, `BoxFaithful`, `Target`),
   and supplies the concrete field names the reports left as "the `Annot` shape" / "field for
   field." Sections 2-3 below are additions the 184 plan should consume, not corrections to 01/02.

## Context & Scope

Reports 01 and 02 recommended four new BimodalLogic tasks (redesign report section 6.2; report 02
section "Recommendations") as prerequisites/companions to this task's certificate redesign: a
soundness task for the witness-family route, a `check_certificate` re-verification executable, the
tableau-bridge branch-gates task, and a revision to task 623. The user asked this dispatch to
confirm that the four BimodalLogic tasks archived as 665-668 — completed since reports 01/02 were
written — match what was recommended, and to surface anything the 184 plan needs to account for.
Scope is confirmation and concrete-detail extraction, not new design; reports 01/02 remain the
authority for the certificate's shape.

## Findings

### 1. Task-by-task mapping

| BimodalLogic task | Report 01/02 recommendation | Match |
|---|---|---|
| 665 `witness_family_certificate_soundness` | Report 02 §Recommendations #1: "Witness-family certificates: soundness," carrying T1 (agreement), T1' (consequence corollary), T2 (decidability), T3 (non-vacuity) | **Exact.** Landed `FormalSystem/Metalogic/Decidability/WitnessFamily/` (7 modules, 2,042 lines): `LabelledLasso`/`WitnessFamily` structures, `shiftTruth_iff_mem`/`truth_iff_mem` (T1), `not_consequence_ztime`/`not_consequence_base`/`joint_countermodel` (T1'), four named `Decidable` instances (T2), `posFamily`/`sepFamily`/`no_witnessFamily_of_validZTime`/`no_witnessFamily_of_MF` (T3). Same predicate names as report 02 §1 (`LocalCoherentLab`, `FulfillingLab`, `BoxFaithful`, `Target`, renamed from `BoxOracleSound`). |
| 666 `check_certificate_executable` | Redesign report New B / report 02 recommendation 3: `lake exe check_certificate`, JSON family in, verdict out | **Exact.** `lake exe check_certificate` reads one certificate on stdin, prints one verdict line; depends on 665 (consumes its `Decidable` instances) and, for build/CI reasons, on 667 (shared `BimodalTools` parser extraction — an implementation-order dependency, not a semantic one). |
| 667 `tableau_bridge_branch_gates_and_frame_class` | Redesign report §6.2 last row: "Tableau bridge: run the branch gates on `invalid`," evaluate the four named gates, reject unrecognized `frame_class` instead of defaulting to `Base` | **Exact, and stronger than asked.** `BranchGates` adds the four named gates plus four further hypotheses (`branchOrderValid`, `saturated`, `noClosure`, `rootDenied`) that the underlying theorems actually need; `"gated"` is the eight-way conjunction. `parseFrameClass` now rejects any unrecognized string with an `error` response — the redesign report's own mitigation ("the oracle client validates the tag before sending," risk section) is now enforced server-side as well. |
| 623 (revision, not archived — still active) | Report 01 §6.2: "Prioritize 623; add to its deliverables a consequence-form soundness statement." Report 02 recommendation 2: "Revise 623 to depend on the new task and keep only T4 + decidability assembly, dropping the soundness deliverables." | **Report 02's revision was the one actually applied.** `specs/TODO.md` now lists 623 depending on 534, 645, **665**, with its description stating verbatim: "The soundness half... has been split out into its own task, on which this task now depends; do not re-prove or re-define any of it here, consume it." 623 itself remains `[NOT STARTED]`; nothing here is a dependency of ModelChecker task 184 (reports 01/02 already note ModelChecker's soundness does not depend on 623). |
| 668 `clear_c34b_residual_enforce_c34b` | *(not recommended by either report)* | **Unrelated.** Lean-invariant tooling maintenance (`scripts/check-module-invariants.sh`'s hypothesis-honesty gate, C34a/C34b). No mention of witness families, certificates, or the bimodal semantics anywhere in its scope. Included in the 665-668 range by numbering coincidence only; no action needed on the ModelChecker side. |

### 2. The certificate JSON wire format, now fixed

`BimodalTools/README.md`'s "Certificate re-verification protocol" section states the field names
mirror the Lean structures exactly and that renaming any of them is a breaking change on the
producing side (i.e. ModelChecker, once it exports certificates). Input shape:

```json
{"target":      {"premises":    [<formula>, ...],
                 "conclusions": [<formula>, ...],
                 "time":        0},
 "bx":          [[<formula>, true], [<formula>, false], ...],
 "lassos":      [{"back": [<label>, ...], "mid": [<label>, ...], "fwd": [<label>, ...]}, ...]}
```

- `target.time` is **required** (no default) — it is the one existential witness (the target
  position `t₀` of report 01 §4.1 condition 4) that must always be explicit.
- `target.premises`/`target.conclusions` default to `[]`.
- `bx` is a **sparse** list of `[formula, bool]` pairs, not a total map: "any formula not listed
  reads as `false`." Report 02's `b : Formula → Bool` phrasing should be read as this sparse
  encoding on the wire, not as requiring every boxed subformula in the closure to be listed.
- `lassos[0]` is always the main lasso (report 01 §4.1's Λ₀); further entries are witness lassos.
  `back`/`fwd` must be non-empty lists of labels; `mid` may be empty.
- A `<label>` is a list of `<formula>` (a set). A `<formula>` uses a fixed tag vocabulary:
  `atom` (field `name`), `bot`, `imp` (`left`, `right`), `box` (`child`), `untl`/`snce` (`event`,
  `guard`). This is the exact vocabulary ModelChecker's Python `Formula`-to-JSON serializer must
  target.
- **Atom identity is base-only.** `Formula.toJson` drops `Atom.freshIndex`, so a fresh-indexed
  (Skolem-style) atom silently changes identity on the wire and a certificate carrying one is
  rejected outright. ModelChecker's exporter must never emit an internal Skolem/fresh-atom
  encoding in a certificate's labels — only base atoms belong in `target`/`bx`/labels.

`lake exe check_certificate`'s three output shapes:

```json
{"status": "countermodel", "time": 0}
{"status": "rejected", "failed": [{"condition": "fulfilling", "lasso": 0, "position": -2,
   "formula": {...}, "detail": "..."}]}
{"status": "error", "message": "..."}
```

`condition` ∈ `structural | local_coherent | fulfilling | box_faithful | target | unlocalized`.
A missing `"target"` or `"target"."time"` is always `error`, never `rejected`.

### 3. Tableau bridge protocol, as it stands after 667

- `frame_class` accepts `Base`, `Dense`, `ZTime`, `Discrete` (alias for `ZTime`), `RTime`
  (Dedekind — incomparable with `ZTime`); omitted defaults to `Base`; anything else is now
  rejected with an `error` response (previously silently coerced to `Base`, which was report 01's
  named risk).
- Every `invalid` response now carries an additive `"gates"` object with eight named booleans plus
  `"gated"` (their conjunction): `time_order_total`, `box_anchored_check`, `region_label_check`,
  `temporal_witness_check`, `branch_order_valid`, `saturated`, `no_closure`, `root_denied`.
  `"gated": true` means the verdict is citable through `not_valid_of_hasOpen_int` /
  `not_validZTime_of_hasOpen_int`; `"gated": false` means it is the decision procedure's own
  heuristic verdict, not a theorem-backed claim of invalidity (and never a claim of validity).
- **Measured fact, stated in BimodalLogic's own protocol docs**: at `"ZTime"` today,
  `region_label_check` and `temporal_witness_check` are `false` on every open branch, so `"gated"`
  is currently always `false` at `ZTime`. Repairing those two gates at `ZTime` is recorded in 667's
  own follow-ups as a separate, larger, open piece of work inside
  `FormalSystem/Metalogic/Decidability/Verified/Bridge/`, explicitly out of scope for 667.

## Decisions

- No changes to reports 01 or 02, or to task 184's description, are warranted by this review. The
  four archived tasks are a faithful, complete implementation of what those reports asked for, at
  the same predicate names, with no compromises or scope cuts that alter the certificate's shape.
- Task 184's plan should treat section 2's field names and formula-tag vocabulary as a fixed
  external contract (not a design choice to be made independently), and should scope the
  round-trip re-verification test against the already-live `lake exe check_certificate` rather
  than as a task blocked on future BimodalLogic work.
- Task 184's plan should **not** attempt to compensate for `gated: false` at `ZTime` inside
  ModelChecker; that is expected, explained, and BimodalLogic's problem to fix later. This applies
  to the follow-on tableau-oracle task (New A in report 01), which is out of scope for 184 itself
  but should carry this expectation forward when it is created.

## Recommendations

1. When planning 184's certificate-export/registry work (dispatch DELIVERABLES: "operators
   rewritten as label-constraint generators," "WitnessRegistry/WitnessConstraintGenerator... the
   natural home"), design the Python `LabelledLasso`/`WitnessFamily` dataclasses to serialize
   exactly to section 2's JSON shape — same field names, same `bx` sparse-pair encoding, same
   nested `target` object, same formula tag vocabulary — so the round-trip test against `lake exe
   check_certificate` is a direct integration rather than a translation layer.
2. Ensure the Python `Formula`→JSON encoder path never serializes an internally-generated
   fresh/Skolem atom into a certificate; only `Atom.base`-equivalent atoms are valid on the wire,
   and `check_certificate` rejects anything else outright.
3. When report 01's New A (tableau oracle) is eventually planned, its plan should state up front
   — not discover mid-implementation — that ZTime `invalid` verdicts are `gated: false` today by
   design-in-progress on the BimodalLogic side, so the verdict matrix's "counts as evidence only
   when gates pass" clause will rarely fire until that separate repair lands. This does not block
   New A: `certificate` vs. tableau `valid` (a ModelChecker-bug signal) is unaffected by the gate
   state.
4. No action needed regarding task 668; it is unrelated Lean-tooling maintenance.

## Risks & Mitigations

- **Risk**: a future BimodalLogic revision to `WitnessFamily`/`LabelledLasso` field names would
  silently break ModelChecker's exporter. **Mitigation**: none needed now beyond noting the
  contract is documented as breaking-change-gated on the Lean side; if 184's plan wants extra
  safety, a schema-version or field-presence check in the Python exporter is cheap and can be a
  plan phase item, not a blocker.
- **Risk**: treating `gated: false` at ZTime as a ModelChecker-side defect once New A is built.
  **Mitigation**: this report and BimodalLogic's own protocol docs both name it as a known,
  explained, pre-existing condition; New A's plan should cite this report rather than re-derive it.
