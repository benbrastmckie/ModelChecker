# Implementation Plan: Task #165

- **Task**: 165 - Improve py-spec for Haskell port
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: None
- **Research Inputs**: specs/165_improve_py_spec_for_haskell_port/reports/01_haskell-porting-readiness.md
- **Artifacts**: plans/02_py-spec-port-improvements.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Raise `haskell/py-spec/` from an architecturally accurate but content-shallow map to a
self-sufficient porting specification. The research report's verdict is that the tree is
*correct everywhere it was sampled* but omits the semantic content a porter writes total
functions from: no operator truth condition is ever stated (A1), the helper predicates and the
exact frame-constraint list are missing (A2), and the exclusion Skolem-witness mechanism is a
five-word table cell (A3). Work adds three satellite documents (operator semantics, worked
trace, exclusion witnesses), one glossary, targeted corrections (08-, 07-, 12-), and surgical
compression (13-, 09-). The 14-document decomposition by pipeline stage is preserved exactly —
no renumbering, no merging, no reordering.

Definition of done: a competent Haskell engineer reading only `haskell/py-spec/` can state every
primitive operator's truth conditions, every helper predicate, every frame constraint, the
exclusion witness mechanism, and validate a first working run against a concrete golden trace.

### Research Integration

Key findings integrated from `reports/01_haskell-porting-readiness.md`:
- P0 blockers A1/A2/A3 drive Phases 1-4 (helper predicates first, since operator truth
  conditions reference `is_alternative`, `maximal`, `compatible`, `max_compatible_part`).
- P1 items A4-A7 drive Phases 5-6 (worked trace + determinism contract; error taxonomy +
  iteration corrections).
- P2 compression targets (B) and small gaps (A7) drive Phase 7; glossary and map update drive
  Phase 8.
- The report's Risks section supplies the notation discipline (use `05-state-encoding.md`'s
  table style as the template, never Python transliteration) and the golden-trace anchoring
  strategy (source the trace from an existing `unit_tests` entry so it stays tied to the
  executable conformance suite).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found (no `roadmap_path` provided; file not consulted).

## Goals & Non-Goals

**Goals**:
- State the truth/falsity/verification/falsification conditions for every primitive operator in
  all four theories in theory-agnostic mathematical notation; state the expansion for every
  defined operator.
- Define all load-bearing helper predicates and the exact, exhaustive frame-constraint list per
  theory family, with exact Z3 uninterpreted-function signatures for all primitives.
- Specify the exclusion witness-predicate mechanism completely enough to implement without
  reading Python.
- Provide one worked end-to-end trace (one valid example, one countermodel) with actual
  constraints and actual verifier/falsifier output, doubling as a golden test.
- Survey the error/exception taxonomy against the strict/absorb/warn policy with an explicit
  edge-case table; state the determinism/ordering contract for set-typed data.
- Fix the two `08-iteration.md` inaccuracies; compress the identified Python-trivia sections;
  add a glossary.

**Non-Goals**:
- No reorganization of the 14-document decomposition: no renumbering, merging, splitting, or
  reordering of existing documents.
- No Python source changes (including the known defects the spec documents — they are recorded,
  not fixed).
- No Haskell design decisions (type signatures, module layout, library choices) — the tree's
  stated philosophy stands.
- No line-anchored codebase links (per README conventions: file-level links, symbol named in
  prose).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Truth-condition tables drift into Python transliteration | H | M | Discipline: `05-state-encoding.md` table style is the template (`∃x ⊑ w. verify(x, p)` register); each phase's verification includes a notation audit — no Python identifiers except cited method names |
| Exclusion witness write-up describes code rather than the Skolemized condition | H | M | Cross-check against `theory_lib/exclusion/docs/` and the theory's academic source before finalizing; state the quantified condition being replaced, then the Skolemization, then the generated constraints |
| Worked trace drifts stale like other prose docs | M | M | Source it from an existing `unit_tests` entry (e.g. `EXT_TH_1`/`EXT_CM_1` in `theory_lib/logos/subtheories/extensional/examples.py`); capture output by actually running `./dev_cli.py`; name the anchoring example so future edits re-run it |
| Formula transcription errors (a wrong quantifier is worse than a missing one) | H | M | Per-operator source cross-check is a listed verification step in Phases 2-4; every formula row cites its defining file so a reviewer can diff formula against source |
| Operator counts (18/4/13/17) are stale against v1.3.3 source | M | L | Scope hypotheses in Phases 2-3: enumerate `operators.py` per theory before writing tables |
| New satellite filenames disturb reading order or README map conventions | L | L | Satellite naming (`03a-`, `07a-`, `11a-`, `00-glossary`) preserves the 01→14 spine; README map updated in Phase 8; every new doc carries the back-link second line and `## Source files` section |
| Task-number references leak into deliverables under `haskell/py-spec/` | M | L | `haskell/py-spec/` is a deliverable tree — cite the research only by content, never "task 165"; final phase runs the task-reference lint |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 6 | -- |
| 2 | 2, 4, 7 | 1 (for 2, 4); 6 (for 7) |
| 3 | 3, 5 | 2 |
| 4 | 8 | all core phases |

Phases within the same wave can execute in parallel (they touch disjoint files).

---

### Phase 1: Helper Predicates, Frame Constraints, and Primitive Signatures [COMPLETED]

**Goal**: Close A2 — define every load-bearing semantic helper predicate and state the exact,
exhaustive frame-constraint list, plus the exact Z3 uninterpreted-function signatures for all
theory primitives.

**Tasks**:
- [x] Read `theory_lib/logos/semantic/core.py` (helper definitions and `__init__` frame
      constraints), plus the analogous exclusion/imposition/bimodal semantic cores for their
      primitives.
- [x] Extend `05-state-encoding.md` with a **helper-predicate table** in the existing encoding
      table's mathematical register: `compatible(x,y) := possible(x ⊔ y)`;
      `maximal(w) := ∀x. compatible(x,w) → x ⊑ w`; `is_world(w) := possible(w) ∧ maximal(w)`;
      `max_compatible_part(z,x,w)` (the maximality-of-compatible-part condition);
      `is_alternative(u,x,w)` (world u contains x and a maximal w-part compatible with x). Each
      row cites its defining file (file-level link, no line anchors).
- [x] Add a **primitive-signature table**: `verify, falsify : BitVec(N) × AtomSort → Bool`,
      `possible : BitVec(N) → Bool` as genuine uninterpreted `z3.Function` declarations;
      exclusion's `excludes`; imposition's ternary `imposition`; bimodal's `truth_condition` and
      task relation — the exact signature form an SMT binding needs.
- [x] Correct `04-constraint-generation.md`'s open-ended "model-shape axioms" framing: logos
      declares exactly two frame constraints — `possibility_downward_closure` and
      `is_world(main_world)` — and the list is closed, not illustrative. Cross-link to the new
      05- tables. State (or link to) the frame-constraint lists for the other three theories
      (imposition's four Fine frame conditions belong in `11a-`/11- treatment but are named
      here as existing).
- [x] Keep all additions in theory-agnostic notation; Python names appear only as cited symbol
      names in prose.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: prose

**Files to modify**:
- `haskell/py-spec/05-state-encoding.md` - helper-predicate table, primitive-signature table
- `haskell/py-spec/04-constraint-generation.md` - closed frame-constraint list, cross-links

**Verification**:
- Every helper-predicate formula diffed against its definition in
  `code/src/model_checker/theory_lib/logos/semantic/core.py` (semantic equivalence, not
  transliteration).
- Frame-constraint list confirmed exhaustive by reading each theory's semantics `__init__`.
- Notation audit: no Python syntax in any table cell; links are relative, file-level,
  resolvable (`ls` the targets).

---

### Phase 2: Operator Semantics Document — Logos [COMPLETED]

**Goal**: Close the logos half of A1 — create `03a-operator-semantics.md` stating the actual
truth conditions for every logos operator, in the `05-state-encoding.md` mathematical register.

**Tasks**:
- [x] Enumerate all logos operators from the four subtheory `operators.py` files
      (extensional, modal, counterfactual, constitutive) and confirm the count against
      `11-theory-catalog.md`'s "18, all subtheories loaded".
- [x] Create `haskell/py-spec/03a-operator-semantics.md` with README back-link second line, a
      short preamble stating the document's contract (content for `03-operators.md`'s
      abstraction: per-operator formulas, not method shapes), and a `## Source files` section.
- [x] For each **primitive** logos operator, one table block giving `true_at` / `false_at` /
      `extended_verify` / `extended_falsify` as formulas. E.g. negation's pure delegation
      (`true_at(¬A, pt) = false_at(A, pt)`); conjunction's fusion-existential
      (`∃x,y. verify(x,A) ∧ verify(y,B) ∧ s = x ⊔ y`) and disjunction's structurally different
      mirror; necessity's quantification over `is_world` states only (not all `2^N`) with
      `extended_verify` collapsing to the null state; the counterfactual via
      `is_alternative` (`∀x,u. (extended_verify(x,A,pt) ∧ is_alternative(u,x,w)) →
      true_at(B, w:=u)`).
- [x] For each **defined** logos operator, state its definitional expansion instead — and
      explicitly flag the two documented irregularities: `\rightarrow` hand-maintains an
      independent `true_at`/`extended_verify` despite being defined (the concrete instance of
      03-'s abstract three-register drift warning), and might-counterfactual's ad-hoc
      construction of a counterfactual instance bypassing normal operator collection wiring.
- [x] Cross-link: `03-operators.md` gains a short pointer ("method shapes here; the formulas
      each method computes are in `03a-operator-semantics.md`"); `04-constraint-generation.md`'s
      double-dispatch section points at the counterfactual formula it currently elides.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: Logos has 18 operators with all subtheories loaded (per
`11-theory-catalog.md`); the primitive/defined split per subtheory is not yet enumerated.
Confirm by reading the four subtheory `operators.py` files before writing tables; adjust table
count to source, not to the catalog claim.

**Files to modify**:
- `haskell/py-spec/03a-operator-semantics.md` - new document (logos sections)
- `haskell/py-spec/03-operators.md` - pointer to the new document
- `haskell/py-spec/04-constraint-generation.md` - counterfactual formula cross-link

**Verification**:
- Per-operator diff of each formula against its `operators.py` definition (all four subtheory
  files); quantifier domains checked especially (worlds vs. all states).
- Every operator in source appears in the document; no operator in the document is absent from
  source.
- Notation audit as in Phase 1; back-link and `## Source files` sections present.

---

### Phase 3: Operator Semantics Document — Exclusion, Imposition, Bimodal [COMPLETED]

**Goal**: Close the remaining half of A1 — extend `03a-operator-semantics.md` with the other
three theories' operator truth conditions.

**Tasks**:
- [x] Enumerate operators from `theory_lib/exclusion/operators.py`,
      `theory_lib/imposition/operators.py`, and bimodal's operators; confirm counts (4 / 13 /
      17 per the catalog) and identify which imposition operators are logos reuse (cite the
      logos table rather than duplicating) versus imposition-specific (the primitive
      counterfactual over the `imposition` relation).
- [x] Exclusion section: the four unilateral operators' conditions, verifier-only register,
      derived `possible`; where a condition depends on witness predicates, state the surface
      form here and link forward to `11a-exclusion-witnesses.md` for the mechanism (that doc is
      Phase 4's deliverable; use the filename now, content lands in parallel).
- [x] Imposition section: the primitive ternary `imposition` relation's role in the
      counterfactual truth condition; Fine's four frame conditions named with their formulas;
      the side-by-side second counterfactual style noted.
- [x] Bimodal section: `truth_condition` register (no verifiers), (world-id, time) evaluation
      points, task-relation-dependent temporal/modal operator conditions.
- [x] Keep the per-theory sections parallel in shape so a porter can read one theory's block
      and know where everything is in the others.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: Operator counts 4 (exclusion), 13 (imposition), 17 (bimodal) per
`11-theory-catalog.md`; the imposition-reuses-logos subset is claimed "essentially verbatim" but
not enumerated. Confirm all three by reading each theory's `operators.py` before writing;
document actual reuse boundaries found.

**Files to modify**:
- `haskell/py-spec/03a-operator-semantics.md` - exclusion, imposition, bimodal sections

**Verification**:
- Per-operator source diff as in Phase 2, against each theory's `operators.py`.
- Imposition reuse claims verified by class identity in source (reused classes cited, not
  re-derived).
- Forward link to `11a-exclusion-witnesses.md` resolves once Phase 4 lands (checked again in
  Phase 8).

---

### Phase 4: Exclusion Witness-Predicate Specification [COMPLETED]

**Goal**: Close A3 — specify the Skolem witness-predicate mechanism completely: what is
Skolemized, why, the exact function signatures, and the constraints generated.

**Tasks**:
- [x] Read `theory_lib/exclusion/semantic/registry.py` (WitnessRegistry, ~126 lines),
      `theory_lib/exclusion/semantic/core.py` (~572 lines), and
      `theory_lib/exclusion/semantic/constraints.py` (~175 lines) in full; cross-check against
      `theory_lib/exclusion/docs/` and the academic source the theory implements.
- [x] Create `haskell/py-spec/11a-exclusion-witnesses.md`: (1) the minimality-quantified
      negation condition of unilateral semantics as a higher-order formula — the thing being
      replaced; (2) the Skolemization step — why witness *functions* make it first-order;
      (3) the exact signatures: a fresh pair `h, y : BitVec(N) → BitVec(N)` per formula,
      keyed and cached by formula string identity, with the registry's lifecycle (when pairs
      are created, how identity keying interacts with formula interning); (4) the constraints
      generated from `h`/`y` and the `excludes` relation, stated as formulas; (5) the known
      failure modes a port must avoid (this mechanism is a documented source of published
      errata in the source literature — say what goes wrong when witnesses are shared or keyed
      incorrectly).
- [x] Expand `11-theory-catalog.md`'s exclusion row/section from the five-word phrase to a
      short paragraph plus link to `11a-`, matching the depth the catalog already gives the
      logos counterfactual walkthrough.
- [x] Add a Mermaid diagram only if it shows mechanism (e.g. formula → registry → fresh
      function pair → constraint sites); no decorated lists (README convention).

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- `haskell/py-spec/11a-exclusion-witnesses.md` - new document
- `haskell/py-spec/11-theory-catalog.md` - expanded exclusion treatment, link to satellite

**Verification**:
- The stated Skolemized condition checked against both the code path
  (`registry.py`/`core.py`/`constraints.py`) and the theory's own `docs/` — divergence between
  the two is resolved before finalizing, per the research report's mitigation.
- Signatures match the actual `z3.Function` declarations in `registry.py`.
- A reader test: the document alone answers "what functions do I declare, when, keyed how, and
  what constraints mention them" without opening Python.

---

### Phase 5: Worked End-to-End Trace and Determinism Contract [COMPLETED]

**Goal**: Close P1.4 and A6 — one valid example and one countermodel traced through all five
pipeline stages with actual constraints and actual verifier/falsifier output; state the
determinism/ordering contract for set-typed data.

**Tasks**:
- [x] Select anchoring examples from
      `theory_lib/logos/subtheories/extensional/examples.py` (`EXT_TH_1` for validity,
      `EXT_CM_1` or similar for a countermodel) — chosen because the extensional fragment keeps
      the constraint dump small; name the anchors in the document so future editors re-run them.
- [x] Run each via `cd code && ./dev_cli.py` (with print-constraints settings as needed) to
      capture: the actual generated constraint groups (frame, atomic, premise, conclusion), the
      solver verdict, and for the countermodel the actual state space, world set, and
      verifier/falsifier sets per sentence letter.
- [x] Create `haskell/py-spec/07a-worked-trace.md`: stage-by-stage narrative (parse → semantics
      → constraints → solve → interpret) showing at each stage the concrete artifact, with
      constraints rendered in the tree's mathematical register alongside the raw output;
      conclude with a "use as golden test" section telling a porter exactly what to reproduce
      and what is incidental.
- [x] Determine (from `find_proposition` in `theory_lib/logos/semantic/proposition.py` and the
      display path) whether verifier/falsifier display order is canonical or incidental
      Python-set iteration order; state the contract explicitly in `07-propositions.md` (and
      note it in the trace where output is shown). If order is incidental, say so and recommend
      the port define a canonical order (sorted by bit-vector value) for its own golden tests.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: prose

**Files to modify**:
- `haskell/py-spec/07a-worked-trace.md` - new document
- `haskell/py-spec/07-propositions.md` - determinism/ordering contract

**Verification**:
- All shown output is captured from a real `./dev_cli.py` run (no hand-invented models); the
  run command and settings are recorded in the document so the trace is reproducible.
- The countermodel's verifier/falsifier sets shown match the captured run verbatim.
- The determinism claim is verified against source (set construction and iteration on the
  display path), not asserted from memory.

---

### Phase 6: Error Taxonomy Survey and Iteration Corrections [COMPLETED]

**Goal**: Close A5, A4, and the two minor accuracy nits — map the exception hierarchy onto the
strict/absorb/warn policy with an edge-case table; fix `08-iteration.md`'s two inaccuracies.

**Tasks**:
- [x] Survey the nine error modules (`output/errors.py`, `settings/errors.py`,
      `iterate/errors.py`, `models/errors.py`, `theory_lib/errors.py`, `syntactic/errors.py`,
      `builder/error_types.py`, `builder/errors.py`) and add to
      `12-settings-and-registry.md`: a table mapping each exception family to the
      strict/absorb/warn policy tier, and an edge-case behavior table covering at minimum:
      `N` out of `[1, MAX_N]` (raises `SemanticError` — name the type and range in the settings
      table), N=0, empty premises, empty conclusions, malformed formula (the two parser gaps
      from 02-), unknown operator, unknown theory.
- [x] Fold in A7 settings items while in 12-: settings type/range validators beyond the bare
      type column; the registry's full API surface (`set_adapter`, `set_default_theory`,
      `get_default_theory`, `iter_theories`).
- [x] Fix `08-iteration.md`: (a) cite `iterate/constraints.py` directly (file-level link,
      symbol named in prose: `_generate_input_combinations` iterating `range(domain_size)`
      where the width, not the state count, bounds the range) for known-defect #1, instead of
      deferring the citation to 14-; (b) correct "blind to proposition valuations" — per-node
      truth-value properties are computed and stored by the graph builder, then ignored because
      the isomorphism call passes no node/edge matcher: attribute-blind by omitted argument,
      not by design; the tree's recommended fix is a one-argument change, not a rebuild.
- [x] Fix `07-propositions.md`'s source-files list: `proposition.py` calls
      `find_verifiers_and_falsifiers`; it is defined per-operator across subtheory files plus
      the protocol.
- [x] Soften `10-theory-contract.md`'s "roughly ninety places" import-count claim to the
      measured order of magnitude or reword to be count-free.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: Nine error modules and the builder's 9 exception classes per the research
report. Confirm the module list by `ls`/grep before writing the table; the table enumerates what
is found, not what the report predicted.

**Files to modify**:
- `haskell/py-spec/12-settings-and-registry.md` - exception/policy mapping, edge-case table, registry API, validators
- `haskell/py-spec/08-iteration.md` - defect citation, isomorphism correction
- `haskell/py-spec/07-propositions.md` - source-files attribution fix
- `haskell/py-spec/10-theory-contract.md` - import-count rewording

**Verification**:
- Each edge-case row verified by reading the validating code path (e.g. `models/semantic.py`
  for the N range) — no behavior asserted without a source citation.
- The corrected isomorphism claim checked against `iterate/graph.py` (properties stored; the
  isomorphism call has no matcher arguments).

---

### Phase 7: Compression and Small-Gap Folds [NOT STARTED]

**Goal**: Close P2.8, P2.9, and the remaining A7 items — cut Python packaging/UX trivia, keep
every invariant.

**Tasks**:
- [ ] `13-examples-and-cli.md`: compress the project-generation/Jupyter/packaging tail
      (~25 lines) by roughly two thirds to a single paragraph pointing at
      `14-porting-notes.md`'s mechanism-not-to-reproduce table; cut the three-entry-points
      paragraph entirely; keep the 17-flag CLI → settings table intact (drop short-flag-letter
      trivia if present).
- [ ] `09-output-and-display.md`: compress the stdout-identity color-decision detail to one
      sentence (~1/3 reduction of that subsection); preserve the capture-then-format vs.
      data-then-render framing untouched.
- [ ] Fold remaining A7 items: the exact `Result`-tuple shape
      `(is_timeout, model_or_core, is_satisfiable, runtime)` into
      `06-solver-and-results.md` (it directly informs the recommended target sum type); the
      ANSI→Markdown rule (red/green become bold/italic, all other codes stripped) as one
      sentence in 09-; the tracked-assertion `Bool(label)` uniqueness scope (one solver setup
      call) as one sentence in 06-.
- [ ] Re-read both compressed documents end-to-end to confirm no invariant or contract was
      deleted with the trivia.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: prose

**Scope Hypothesis**: Compression targets are ~2/3 of a ~25-line section in 13- and ~1/3 of one
09- subsection, per the research report. Measure the actual sections before cutting; the target
is the report's ratio applied to actual current line counts, and the CLI flag table plus all
14--referenced invariants must survive verbatim in meaning.

**Files to modify**:
- `haskell/py-spec/13-examples-and-cli.md` - tail compression, entry-points cut
- `haskell/py-spec/09-output-and-display.md` - stdout-identity compression, ANSI rule
- `haskell/py-spec/06-solver-and-results.md` - Result tuple shape, tracked-assertion scope

**Verification**:
- Line-count delta roughly matches targets (13- section down ~2/3; 09- subsection down ~1/3).
- Diff read-through: nothing removed that any other document cross-references; the CLI flag
  table row count is unchanged.

---

### Phase 8: Glossary, Map Update, and Tree-Wide Consistency Pass [NOT STARTED]

**Goal**: Close P2.10 and integrate everything — canonical definition site for cross-document
terms, README map covering the new satellites, and a final consistency audit of the whole tree.

**Tasks**:
- [ ] Create `haskell/py-spec/00-glossary.md`: one canonical definition per load-bearing term —
      state, world, possible, compatible, maximal, verifier, falsifier, fusion, part-of,
      evaluation point, main_point, frame constraint, alternative world, witness predicate,
      isomorphism (model), interning, evaluation scheme — each definition one to three lines in
      the tree's mathematical register, linking to the document that treats it fully. Ordered
      for lookup (alphabetical), not narrative.
- [ ] Update `README.md`: add the four new documents to the map tables in their natural
      sections (03a with the compiler pipeline, 07a with solving/semantic values, 11a with the
      theory library, 00-glossary in "How to read this" as the reference companion); keep the
      "start at 01, end at 14" reading instruction intact.
- [ ] Consistency pass over all 19 files: every document's second line back-links to the map;
      every document carries `## Source files`; all relative links resolve (script check: grep
      links, test file existence); no line-anchored links anywhere; all Mermaid fences parse
      (render check via `mmdc` if available, otherwise a syntax review of each fence).
- [ ] Repo lint: run the task-reference check over `haskell/py-spec/` — deliverables must not
      cite task numbers; confirm zero occurrences.
- [ ] Final reader pass in the persona named by the user focus: an engineer learning the
      system to port it — confirm the reading path (README → 01 → ... → 14, glossary and
      satellites as reference) is stated and coherent, and prose is concise throughout.

**Timing**: 1.5 hours

**Depends on**: 2, 3, 4, 5, 7

**Verification Tier**: prose

**Files to modify**:
- `haskell/py-spec/00-glossary.md` - new document
- `haskell/py-spec/README.md` - map and reading-guide updates
- (touch-ups in any document failing the consistency checks)

**Verification**:
- Link-resolution check passes for every relative link in the tree (automated grep + existence
  test, exact command recorded in the summary).
- Task-reference lint reports zero hits under `haskell/py-spec/`.
- Glossary terms each link to a treating document; no term defined differently in two places
  (grep for each term's definition sites).

## Testing & Validation

- [ ] Every formula in `03a-`, `05-`, and `11a-` cross-checked against its cited Python source
      file during the authoring phase (semantic equivalence, mathematical notation).
- [ ] Worked-trace output captured from a real `./dev_cli.py` run with the command recorded;
      re-runnable by a reviewer.
- [ ] All relative links in `haskell/py-spec/` resolve; no line-anchored links introduced.
- [ ] All Mermaid fences syntactically valid (render or careful syntax review).
- [ ] Task-reference lint clean over `haskell/py-spec/` (deliverable tree).
- [ ] Compression phases verified by diff read-through: no cross-referenced invariant deleted.
- [ ] README map lists all 19 documents; each document's back-link and `## Source files`
      section present.

## Artifacts & Outputs

- `haskell/py-spec/03a-operator-semantics.md` (new — per-operator truth conditions, four theories)
- `haskell/py-spec/07a-worked-trace.md` (new — golden end-to-end trace, valid + countermodel)
- `haskell/py-spec/11a-exclusion-witnesses.md` (new — Skolem witness mechanism specification)
- `haskell/py-spec/00-glossary.md` (new — canonical term definitions)
- Expanded: `05-state-encoding.md`, `04-constraint-generation.md`, `11-theory-catalog.md`,
  `12-settings-and-registry.md`, `06-solver-and-results.md`, `07-propositions.md`
- Corrected: `08-iteration.md`, `07-propositions.md`, `10-theory-contract.md`
- Compressed: `13-examples-and-cli.md`, `09-output-and-display.md`
- Updated: `README.md` (map), `03-operators.md` (pointer)
- `specs/165_improve_py_spec_for_haskell_port/summaries/03_implementation-summary.md` (post-implementation)

## Rollback/Contingency

All changes are additive markdown or surgical edits in a git-tracked tree with per-phase
commits; revert is `git revert` of the offending phase commit(s). No Python source, tests, or
build configuration is touched, so no runtime behavior can regress. If a content phase stalls on
domain difficulty (most plausibly Phase 4's Skolemized condition), land the phase as
[PARTIAL] with the code-derived portion complete and the literature cross-check flagged as an
open item rather than publishing an unverified formula — a wrong truth condition is worse for a
porter than a marked gap.
