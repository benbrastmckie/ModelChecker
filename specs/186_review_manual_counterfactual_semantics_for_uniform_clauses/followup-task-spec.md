# Follow-up Task Specification: Close the Remaining Manual/Lean Edits for Settled Event Verification

**Written by**: task 186, Phase 6 (this task is forbidden from making these edits itself; see the
dispatch's SCOPE clause). **Not a task file** — this is the specification a future task's author
reads before creating that task.

**Both target trees are separate repositories from this one** (`ModelChecker`): the manual and its
proof-theory chapter live in `~/Projects/Logos/Theory/typst/manual/chapters/`, and the Lean
development (if the follow-up chooses to touch it) lives in that same repository's Lean tree. This
task and its own repository (`ModelChecker`) never touch either.

## Why this specification is narrower than round 1's report 01 F10 anticipated

Report 01's F10 (round 1, `specs/186_.../reports/01_family-level-settled-verification.md`) listed
ten `03-dynamics.typ` edit sites, two `02-constitutive.typ` sites, and several `11-proof-theory.typ`
sites, on the assumption that none of the recommended principle had yet been adopted. Between round
1's completion and this round's start, a separate task in the Logos repository (task 406, then
407 — the SAME task whose two reports are this task's own provenance input) independently
implemented almost the entire recommendation, converging on the same solution round 1 derived from
first principles. Re-reading the CURRENT manual text (this round, Phase 1 and Phase 6) confirms
the following about each of F10's original ten `03-dynamics.typ` items:

| F10 item | Status, confirmed by direct re-reading (this round) |
|---|---|
| 1. Drop `phi_DT` on `[]->`; replace the exclusion sentence | **Landed.** `03-dynamics.typ`:70, :573 — the DT restriction is lifted, and `@def-event-fragment`'s exclusion sentence is replaced. |
| 2. `@def-maximal-compatible-subevolutions` for an arbitrary bounding family | **Landed.** Current text (`03-dynamics.typ`:320-330) already reads "Fix an anchored family `pi`... and an anchored family `alpha`... Neither `pi` nor `alpha` is required to be an evolution or a thread." |
| 3. New "Settled Event Verification" definition | **Landed, under a different name.** `@def-counterfactual-verification` (`03-dynamics.typ`:1326) states the `V1`/`V2`/`ILMC` clause for the counterfactual; `@rem-box-diamond-inherit`/`@prop-box-diamond-null-verified` derive `[]`/`<>`/`<>->`; `@prop-stability-non-null` gives `stably`'s own instance. The manual did not adopt F2's exact generic-schema PROSE (a single named principle stated once for an arbitrary `O`), instead stating the counterfactual instance directly and deriving the rest by unfolding abbreviations — mathematically equivalent, differently organized. |
| 4. `@def-event-cf-base`'s `==` item becomes a pointer to the derived case | **Not independently re-verified this round** — flagged for the follow-up task's own check. |
| 5. `@def-stability-truth` containment form | **Landed via the schema, not via editing the truth clause itself** — correctly so: the truth clause is stated over world-histories, where containment and equality coincide (`@def-world-state` maximality); `@prop-stability-non-null` computes the containment form explicitly at the recipe level, which is the only place it needs to differ. No edit to `@def-stability-truth` itself is needed. |
| 6. `@rem-cf-antecedent-restriction` rewrite (supervenience paragraph becomes the null-family derivation) | **Landed, in more depth than F10 asked for.** Current text (`03-dynamics.typ`:1580-1603) contains "The dilemma's second horn describes the clause, for a conditional, rather than refuting it" and derives the null-family reading directly, addressing F8's exact point. |
| 7. `@rem-event-status` E1/E3/E4 record for the new events | **CONFIRMED STILL OPEN.** The current `@rem-event-status` (`03-dynamics.typ`:855-898) records only the TENSE fragment's E1/E3/E4 status (the `until`/`since` clause-generated triples); nothing there addresses the `[]->`/`[]`/`<>`/`<>->`/`stably` family's E1/E3/E4. **This is the one item this specification asks the follow-up task to write.** |
| 8. Settler Minimality axiom | **Landed, as an unconditional axiom** (`@def-minimal-settler`, `03-dynamics.typ`:1341-1359, "Minimal Settler Constraint"), not the conditional-sufficiency fallback F5.3 left as an alternative. |
| 9. `@lem-bridge-soundness`/`@lem-cf-verification-soundness`/`@lem-bridge-equivalence` new cases | **Landed** — `11-proof-theory.typ`'s current C1/M5/C2 rows (see below) cite exactly this machinery (`@rem-c1-m5-bridge-soundness`, `@rem-bridge-soundness-counterfactual-cases`, `@rem-c2-discharge-corollary`). |
| 10. `@rem-imposition`, `@rem-store-recall-coverage`, `@rem-multi-time-pinning` wording | **Not independently re-verified this round** — flagged for the follow-up task's own check. |

`02-constitutive.typ`'s two items (E3's history form; a domain-exactness sentence at
`@rem-no-domain-closure`) and `11-proof-theory.typ`'s items (retire
`@rem-dt-antecedent-restriction-ch7`; extend `@rem-c2-discharge-corollary`; rewrite
`@rem-c1-m5-bridge-soundness`; extend `@rem-c3-not-established`; restate `@thm-soundness`) were
**all confirmed landed** by direct re-reading this round (`11-proof-theory.typ`'s current C1/C2/C3
rows and its final coverage-restatement paragraph match F7's table almost verbatim, including the
identical two-obstruction analysis for C3).

## What this task should actually do

**Primary deliverable**: write `@rem-event-status`'s E1/E3/E4 record for the world-quantifying
family (`[]->`, `[]`, `<>`, `<>->`, `S`/`stably`), in the same register as the existing tense-
fragment record at `03-dynamics.typ`:855-898 (`@rem-event-status`). Source content, already
established by report 01/this round and requiring no new derivation:

- **E1 (Closure) holds unconditionally.** The recipe's `V`/`F` are `closure_ext(Min{...})`;
  `closure_ext` is closure under extension-fusion by construction (report 01 F2, "Availability of
  the two extremal steps").
- **E3, history form, holds unconditionally**; **E3, pointwise form, fails** — a vacuous member can
  carry impossibility outside the shared domain (report 01 F9.1, oracle E1), and Phase 3 (F12, this
  round) supplies a REALIZABLE (non-vacuous) pointwise-E3 failure witness on a certified constrained
  frame (`V = {0:b}`, `F = {0:a, 1:a.c}`, `baselines/02_constrained-frame-oracle-output-c12.txt`).
  Record both the vacuous-member case (round 1) and the realizable-member case (round 2) — the
  two forms are what F9.1/F12 established are genuinely distinct at this family.
- **E4 (Exhaustivity) status**: report 01 states this "holds iff sufficiency holds in both
  polarities (F5.3) plus `@thm-bivalence`" — i.e. E4 is CONDITIONAL on Settler Minimality, which the
  manual has since adopted unconditionally (F10 item 8), so E4 should be recorded as holding
  unconditionally given the now-adopted axiom, with a one-sentence note of the dependency (parallel
  to how `@rem-event-status`'s existing tense-fragment record explicitly names its own dependency
  on `@lem-bridge-equivalence`).

**Secondary checks** (not independently re-verified by this task; the follow-up's author should
confirm before treating them as done):
- F10 item 4: does `@def-event-cf-base`'s `==` item already read as a pointer to the derived case,
  or does it still state the null-state convention as an independent stipulation?
- F10 item 10: do `@rem-imposition`, `@rem-store-recall-coverage`, `@rem-multi-time-pinning` still
  carry DT-restricted wording that needs updating?

**Do not**:
- Re-derive or re-argue D1 (the principle) or D3 (Settler Minimality as an axiom) — both are
  already adopted, independently of this report, for reasons this report's F11/F14 corroborate
  rather than establish.
- Adopt a world-history completion axiom for `@rem-occurrence-possible-states` leg (d). This
  report's F11/D7 supplies a precise CANDIDATE strength (a `Completion`-shaped principle, strictly
  weaker than full Saturation-style existence, automatic under discreteness) as a template for a
  future decision, not a recommendation to adopt one now. Recording the template in leg (d)'s own
  remark (a documentation addition, not an axiom adoption) is in scope; adopting the axiom is not.
- Touch `code/src/model_checker/**` in the ModelChecker repository — nothing here proposes a
  ModelChecker implementation change; the manual and Lean edits are entirely in the Logos
  repository.

## Lean landing (recorded, not planned)

Unchanged from round 1's F10: report 406/02's shape 1 remains the landing (truth and world-history
callbacks into `verifies_evo_ext`); the recipe additionally needs `maxCompatSubevolutions` over an
arbitrary bounding family and the counterfactual truth body callable at a family rather than a
world-history (the `I` conjunct); `Min` and `closure_ext` are generic and can be one definition
shared by every world-quantifying arm. This task does not verify whether the Lean development has
already landed any of this (it was out of scope for both round 1 and round 2's re-audit, which
focused on the Typst manual only); the follow-up task's author should check the Lean tree's current
state before planning Lean work, exactly as this specification checked the manual's.

## Re-verification instruction for the follow-up task's own author

Before executing ANY edit this specification names as still open, re-read the cited manual anchor
at ITS CURRENT line number (labels are stable across edits; line numbers are not) — this
specification's own line numbers were current as of this task's completion and may have moved
again by the time a follow-up task starts. `grep -n "] <label-name>" typst/manual/chapters/*.typ`
resolves a label to its current line.
