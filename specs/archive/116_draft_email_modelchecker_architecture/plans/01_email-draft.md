# Implementation Plan: Task #116

- **Task**: 116 - Draft a brief email for a Python expert explaining ModelChecker's modular architecture
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_architecture-pipeline-operators.md
- **Artifacts**: plans/01_email-draft.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: true

## Overview

Draft a single, brief email (~400-800 words) that explains to a Python expert how ModelChecker
supports modular semantic extensions: shared general infrastructure, per-theory model structures,
the operator abstraction, and the live pipeline from a logical claim to a printed model, culminating
in `counterfactual/operators.py` as a worked example. The research report
(`reports/01_architecture-pipeline-operators.md`) has already gathered all needed material —
including exact file paths, class/method names, and a ready-made 6-part narrative arc in its
section (e). The plan has two phases: draft the email against that narrative arc, then run a
targeted accuracy pass against the real source files (especially `counterfactual/operators.py`).
The deliverable is written to `specs/116_draft_email_modelchecker_architecture/email-draft.md`.

### Research Integration

The plan draws directly on `reports/01_architecture-pipeline-operators.md`:
- Section (a) — layered architecture (shared `models/`/`syntactic/`/`solver/` vs. per-theory
  `theory_lib/*`); source for the "architecture" paragraph.
- Section (b) — the live 6-step programmatic pipeline (`Syntax` -> `Semantics` ->
  `ModelConstraints` -> `ModelStructure.solve()` -> `check_result()`/`interpret()`/`print_all()`);
  source for the "pipeline" paragraph and its data-flow one-liner.
- Section (c) — the operator contract (`true_at`, `false_at`, `extended_verify`,
  `extended_falsify`, `find_verifiers_and_falsifiers`, `print_method`); source for the
  "operator abstraction" paragraph.
- Section (d) — the `counterfactual/operators.py` worked example, method by method; source for
  the culminating section.
- Section (e) — the recommended 6-part narrative arc, used directly as the email outline.
- Decisions/Risks — describe the **live programmatic pipeline**, NOT the CLI/`builder` workflow
  (that package was deleted and `__main__.py`/`dev_cli.py` currently raise `ModuleNotFoundError`);
  phrase the "SMT" step as "compiled into SMT-level Z3 constraints," not literal `.smt2` text.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (documentation deliverable, no roadmap flag).

## Goals & Non-Goals

**Goals**:
- Produce one email draft at `specs/116_draft_email_modelchecker_architecture/email-draft.md`.
- Brief (roughly 400-800 words), email-appropriate register, accessible to a Python expert who is
  unfamiliar with the semantics domain.
- Cover, in order: framing -> layered architecture -> the pipeline -> the operator abstraction ->
  the `counterfactual/operators.py` worked example -> a short close.
- Technically accurate against the ACTUAL live pipeline (`Syntax` -> `Semantics` ->
  `ModelConstraints` -> `ModelStructure`), verified against real source files.
- Culminate in `counterfactual/operators.py` (`CounterfactualOperator`, with a brief mention of
  `MightCounterfactualOperator` as the `DefinedOperator` counterpart).

**Non-Goals**:
- No exhaustive architecture documentation — this is an email, not a design doc.
- Do NOT describe or endorse the `model-checker` CLI / `BuildExample`/`BuildModule` workflow as a
  working entry point (it is currently broken; see research report Appendix).
- Do NOT fix the stale docs or broken CLI (flagged in the report as a separate follow-up).
- No code changes; no tests.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Email describes the broken CLI/`builder` workflow as functional | H | M | Phase 1 explicitly uses the programmatic pipeline; Phase 2 greps for any `model-checker`/`BuildExample`/`builder` mentions and removes them |
| Overstating "SMT-LIB" as literal text serialization | M | M | Phrase as "compiled into SMT-level Z3 constraints solved by Z3"; no claim of `.smt2` round-tripping |
| Operator method names or line-level behavior misstated | M | M | Phase 2 reads `counterfactual/operators.py` and `syntactic/operators.py` directly to confirm the six method names and the `CounterfactualOperator` behavior |
| Email too long / too dense for an email | M | M | Target 400-800 words; Phase 2 checks length and trims |
| Too much jargon for a domain-outsider Python expert | M | L | Lead each concept with the Python-level framing (small classes implementing a fixed method contract, callbacks into a shared object) before the semantics terminology |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Draft the email [COMPLETED]

- **Goal:** Write the full email draft to
  `specs/116_draft_email_modelchecker_architecture/email-draft.md`, following the research
  report's 6-part narrative arc (section e), describing the live programmatic pipeline.
- **Tasks:**
  - [x] Create `specs/116_draft_email_modelchecker_architecture/email-draft.md` with a short
    subject line and greeting appropriate for a Python expert.
  - [x] Write the **opening framing** (1-2 sentences): ModelChecker is a Python framework for
    automating Z3-backed model/countermodel search across multiple modal/counterfactual/
    hyperintensional semantic theories, built so new theories and operators plug in without
    touching the shared engine. (Report section e.1.)
  - [x] Write the **layered architecture** paragraph: shared general infrastructure — `models/`
    (semantics base, constraint bridge, solver-facing model structure, propositions),
    `syntactic/` (parsing + operator base classes), `solver/` (Z3/cvc5 abstraction) — versus
    per-theory "model structures" in `theory_lib/{logos,exclusion,imposition,bimodal}/`, each
    supplying its own semantic primitives and operator set; logos further splits operators into
    à-la-carte subtheories. (Report sections a, e.2.)
  - [x] Write the **pipeline** paragraph or short numbered list mapping 1:1 onto report section
    (b): formula string -> `Syntax` (parse) -> `Semantics` (declare Z3 primitives + frame
    constraints) -> `ModelConstraints` (assemble Z3 `BoolRef` assertions — "compiled into
    SMT-level constraints") -> `ModelStructure.solve()` (hand to Z3 via the `solver/` abstraction,
    get sat/unsat + a model) -> `interpret()`/`print_all()` (walk the result back through the same
    `Sentence` tree, calling each operator's own `find_verifiers_and_falsifiers`/`print_method`).
    Name this the programmatic pipeline (as used by every theory's test suite via `run_test()`);
    do NOT cite the CLI. (Report sections b, e.3, Decisions.)
  - [x] Write the **operator abstraction** paragraph: every operator is a small Python class
    (`syntactic.Operator`, or `syntactic.DefinedOperator` for operators defined in terms of
    others) implementing a fixed contract — `true_at`, `false_at`, `extended_verify`,
    `extended_falsify`, `find_verifiers_and_falsifiers`, `print_method` — and free to call back
    into the shared semantics object's own primitives (`is_part_of`, `fusion`, `compatible`,
    theory-specific relations like `is_alternative`) to state its conditions in that theory's
    resources. Emphasize the callback direction: the shared semantics/model-structure/print code
    dispatches INTO the operator methods. (Report sections c, e.4.)
  - [x] Write the **worked example** section on
    `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`: walk
    `CounterfactualOperator` (primitive, `\boxright` / box-arrow, arity 2) briefly through its
    methods — Z3 quantified constraint construction in `true_at`/`false_at` (using
    `extended_verify`, `is_alternative`, `with_world`), the world-identity verifier trick in
    `extended_verify`/`extended_falsify`, post-solve set computation in
    `find_verifiers_and_falsifiers`, and delegation to the inherited `print_over_worlds` helper in
    `print_method`. Add one sentence on `MightCounterfactualOperator` as the `DefinedOperator`
    counterpart (`A diamond-arrow B := not (A box-arrow not B)`). (Report section d, e.5.)
  - [x] Write a **short close** (1-2 sentences): the modular-extension payoff — new theories and
    operators are added by subclassing the same small base classes; optionally note the scope
    (4 theories, 25+ operators). (Report section e.6.)
  - [x] Keep total length in the ~400-800 word range and the tone conversational-but-precise
    (an email to a knowledgeable peer), avoiding heavy semantics jargon without a plain-Python
    gloss.
- **Timing:** ~1 hour
- **Depends on:** none
- **Files to modify:**
  - `specs/116_draft_email_modelchecker_architecture/email-draft.md` - new file, the email draft.
- **Verification:**
  - File exists and is non-empty; contains all six narrative sections in order; ends on the
    counterfactual worked example (before the short close); word count within ~400-800.

### Phase 2: Accuracy pass against source files [COMPLETED]

- **Goal:** Verify every technical claim in the draft against the real source files and correct
  any drift, especially operator method names and `CounterfactualOperator` behavior.
- **Tasks:**
  - [x] Read `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` and
    confirm: the two operators and their symbols via `get_operators()`; that
    `CounterfactualOperator` implements `true_at`, `false_at`, `extended_verify`,
    `extended_falsify`, `find_verifiers_and_falsifiers`, `print_method`; that `true_at` uses
    `extended_verify` + `is_alternative` + `with_world`; that `print_method` delegates to
    `print_over_worlds`; and that `MightCounterfactualOperator` subclasses `DefinedOperator` with
    `derived_definition` = `not (A box-arrow not B)`. Correct the draft to match.
  - [x] Read `code/src/model_checker/syntactic/operators.py` and confirm the `Operator` /
    `DefinedOperator` base-class names, the `name`/`arity`/`primitive` attributes, and that the
    six operator methods named in the email are the ones the concrete operators supply. Correct
    any mismatch.
  - [x] Spot-check the pipeline claim against
    `code/src/model_checker/utils/testing.py` (`run_test`) and/or
    `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py`
    to confirm the `Syntax` -> `Semantics` -> `ModelConstraints` -> `ModelStructure` construction
    order and method names (`check_result`, `interpret`, `print_all`).
  - [x] Grep the draft for `model-checker`, `BuildExample`, `BuildModule`, `builder`, and `.smt2`;
    remove or rephrase any occurrence that implies the CLI works or that literal SMT-LIB text is
    emitted.
  - [x] Re-check length (~400-800 words) and readability for a domain-outsider Python expert;
    trim redundancy and tighten wording.
  - [x] Apply corrections in place to `email-draft.md`.
- **Timing:** ~0.5 hour
- **Depends on:** 1
- **Files to modify:**
  - `specs/116_draft_email_modelchecker_architecture/email-draft.md` - corrections from the
    accuracy pass.
- **Verification:**
  - Every operator method name and class name in the email matches the actual source; no CLI/
    `builder`/`.smt2` claims remain; word count within ~400-800; the email still culminates in the
    counterfactual `operators.py` example.

## Testing & Validation

- [x] `email-draft.md` exists at `specs/116_draft_email_modelchecker_architecture/email-draft.md`
  and is non-empty. *(completed)*
- [x] Word count is roughly 400-800. *(completed: 666 words)*
- [x] The six method names (`true_at`, `false_at`, `extended_verify`, `extended_falsify`,
  `find_verifiers_and_falsifiers`, `print_method`) and the class names
  (`Operator`, `DefinedOperator`, `CounterfactualOperator`, `MightCounterfactualOperator`) match
  the real source files. *(completed: verified directly against counterfactual/operators.py and
  syntactic/operators.py)*
- [x] The pipeline is described as the programmatic `Syntax`/`Semantics`/`ModelConstraints`/
  `ModelStructure` flow — no working-CLI claim, no literal SMT-LIB serialization claim.
  *(completed: verified against `utils/testing.py:run_test()`)*
- [x] The email culminates in the `counterfactual/operators.py` worked example. *(completed)*
- [x] Tone and jargon level are appropriate for a Python expert unfamiliar with the domain.
  *(completed)*

## Artifacts & Outputs

- `specs/116_draft_email_modelchecker_architecture/email-draft.md` - the drafted email (deliverable).
- `specs/116_draft_email_modelchecker_architecture/summaries/01_email-draft-summary.md` -
  implementation summary (created at /implement completion).

## Rollback/Contingency

Deliverable is a single new markdown file with no code impact. To revert, delete
`email-draft.md`. If the accuracy pass surfaces a claim that cannot be reconciled with the
source, prefer removing the claim over guessing; if the pipeline shape has changed materially
since the research report, note the discrepancy and re-verify against `run_test()` before
finalizing.
