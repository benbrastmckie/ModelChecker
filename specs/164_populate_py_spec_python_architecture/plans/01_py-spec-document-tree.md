# Implementation Plan: Python Architecture Spec Document Tree

- **Task**: 164 - Populate the Python architecture specification for the ModelChecker
- **Status**: [IMPLEMENTING]
- **Effort**: 8.5 hours
- **Dependencies**: None
- **Research Inputs**:
  - `specs/164_populate_py_spec_python_architecture/reports/01_python-architecture-spec.md` (synthesis)
  - `specs/164_populate_py_spec_python_architecture/reports/findings/01_compiler-pipeline.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/02_core-utilities.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/03_tools-features.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/04_ui-cli.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/05_theory-lib.md`
- **Artifacts**: plans/01_py-spec-document-tree.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Build `haskell/py-spec/` as a flat, README-mapped tree of 14 focused specification documents
describing the Python ModelChecker precisely enough that a Haskell reimplementation could be
designed against it. The research is complete and grounded: every document is written from
assigned sections of the five `findings/` files (which carry `file.py:LINE` citations), never
from fresh exploration. Definition of done: all 15 files exist, every internal and codebase link
resolves mechanically, every document carries the navigation contract (back-link to the map,
bounded sibling links), diagrams are mermaid, Python blocks are real signatures within a stated
budget, and `haskell/py_spec.md` has been disposed of per the decision below.

### Research Integration

The synthesis report supplies the organizing spine (five-stage pipeline; four constraint groups;
countermodel framing) and the two highest-value reusable artifacts (the bit-vector encoding table
and the operator-method table). The five findings files supply the grounded detail. Each phase
below names its **exact source sections** so the implementer reads a bounded slice rather than
re-researching. Recommendations 1-11 of the report map onto documents as follows: R1 → `01`,
R2 → `04`+`05`, R3 → `02`, R4 → `06`+`09`, R5 → `03`+`07`, R6 → `10`, R7 → `13`, R8 → `12`,
R9 → `08`, R10 + R11 → `14`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and `roadmap_flag` is absent; no roadmap
phases are included. `haskell/TODO.md` (a repository-local, user-owned checklist, not
`specs/ROADMAP.md`) carries the bullet "describe model-checker architecture in python" with the
five sub-bullets this tree covers; Phase 9 marks that bullet done and points it at the new map.

## Goals & Non-Goals

**Goals**:
- A document tree under `haskell/py-spec/` whose `README.md` is the single navigational map.
- Each document concise, self-contained, and readable in isolation by a Haskell designer.
- Mermaid diagrams wherever a picture beats prose; real Python signatures where exactness matters.
- Systematic relative links from every document into `code/src/model_checker/**`.
- An explicit, mechanically checkable navigation contract (forward links, back-links, bounded
  sibling links) — not an aspiration in prose.

**Non-Goals**:
- No Haskell design decisions, type signatures, or module layout. This is a description of the
  Python system, per the research report's standing constraint.
- No changes to any Python source under `code/`. Defects found during research are *recorded* in
  `14-porting-notes.md`, not fixed here.
- No corrections to the stale documents under `docs/architecture/` — the divergence inventory is
  recorded as a warning; corrections belong to separate tasks.
- No line-anchored deep links into source (brittle); file-level links with the symbol named in
  prose only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer re-researches the codebase instead of using findings, blowing context and drifting | H | M | Each phase names exact findings file + section range as the source; phases forbid open-ended codebase exploration beyond confirming a cited path exists |
| Parallel phases invent inconsistent filenames, breaking README's forward links | H | M | Phase 1 fixes the canonical 15-file inventory verbatim in this plan and in `README.md`; later phases MUST NOT rename, add, or drop files without amending the plan |
| Link-everything mesh between siblings (explicitly unwanted) | M | M | Sanctioned cross-link table below caps non-hub documents at 4 sibling links, each justified in prose |
| Code-block bloat turning a spec into a source dump | M | M | Per-document code budget stated below and checked in Phase 9 |
| Broken relative links into `code/src/**` (typos, moved paths) | M | M | Phase 9 runs a mechanical resolver over every relative link in every file; each authoring phase runs the same check scoped to its own files |
| Task-number / `specs/` references leaking into deliverables | M | L | Forbidden by `.claude/rules/no-task-references-in-deliverables.md`; write-time hook plus an explicit Phase 9 grep |
| Stale doc claims copied in as fact | H | L | Findings files are ground truth; `docs/architecture/**` is quotable only as *intent*, and only where `14-porting-notes.md` records the divergence |

## Design Decisions (binding on all phases)

### D1. Flat tree, single map

`haskell/py-spec/` is **flat** — one directory, no subdirectories, no sub-READMEs. Rationale:
(a) every document then sits at the same depth, so the codebase-link prefix is uniformly
`../../code/src/model_checker/...` and cannot be got wrong per-file; (b) one map means one place
where an index can go stale; (c) sub-indices would introduce a two-hop maze for a 14-document
set. Grouping is expressed by the numeric filename prefix and by section headings inside
`README.md`.

### D2. Canonical file inventory (15 files)

| File | Specifies |
|---|---|
| `README.md` | Purpose, audience, scope, conventions, the full map |
| `01-pipeline.md` | The five-stage spine, object graph, construction order, aliasing and cycles |
| `02-syntax-and-ast.md` | Surface DSL, parser algorithm, prefix-list shape, the `Sentence` node and its four-phase lifecycle, interning, `AtomSort` |
| `03-operators.md` | `Operator` / `DefinedOperator` / `OperatorCollection`, the six semantic methods, definitional expansion, the three-register pattern |
| `04-constraint-generation.md` | `ModelConstraints`, the four constraint groups, premise/conclusion behaviour, countermodel framing, double dispatch, the semantic base contract |
| `05-state-encoding.md` | Bit-vector state space, mereology, the encoding table, finite quantifier expansion and its cost model, `MAX_N` |
| `06-solver-and-results.md` | Solver backends and protocol, tracked assertions and unsat cores, unknown-as-timeout, per-example context isolation, the concurrency invariant, `ModelStructure`'s result state |
| `07-propositions.md` | The proposition contract, the three evaluation schemes, evaluation points, post-solve extraction |
| `08-iteration.md` | The iteration algorithm, two-tier distinctness, difference constraints, model rebuild, isomorphism, termination budgets |
| `09-output-and-display.md` | Output modes, capture-then-format vs. data-then-render, the display contract, recursive truth-tree printing, `--maximize`, progress feedback |
| `10-theory-contract.md` | What a theory must supply, the required module set, `get_theory`, the layering rule, the executable conformance contracts, the subtheory system |
| `11-theory-catalog.md` | The four shipped theories, the two families, cross-theory variation, a worked operator walkthrough |
| `12-settings-and-registry.md` | Settings declaration sites, precedence chain, the setting inventory, theory registry/discovery, the error-handling policy |
| `13-examples-and-cli.md` | The example-file format (the real user input language), examples-as-tests, the CLI surface, entry points, project generation, Jupyter, packaging |
| `14-porting-notes.md` | Semantics to preserve vs. mechanism not to reproduce; known defects; dead-code inventory; the documentation-reliability warning |

No phase may add, drop, or rename a file in this table without amending this plan first.

### D3. Navigation contract (checkable)

1. `README.md` contains a **forward link to every one of the 14 documents**, grouped under
   section headings, each with a one-line description.
2. **Every document's second line** is exactly `[← Spec map](./README.md)`.
3. Sibling cross-links are **bounded and justified**. `01-pipeline.md` and `14-porting-notes.md`
   are the two hub documents and may link broadly. Every other document carries **at most four**
   sibling links, each placed either inline where the dependency is named in prose or in a final
   `## Related` section, and each annotated with *why* (`— the double dispatch this table feeds`),
   never a bare filename. Reciprocity is not required: a link from A to B does not oblige B to
   link back.

Sanctioned sibling links (a ceiling, not a quota — omit any that the prose does not earn):

| Document | May link to |
|---|---|
| `01-pipeline.md` (hub) | any |
| `02-syntax-and-ast.md` | `03`, `04` |
| `03-operators.md` | `02`, `04`, `07`, `11` |
| `04-constraint-generation.md` | `03`, `05`, `06`, `10` |
| `05-state-encoding.md` | `04`, `11` |
| `06-solver-and-results.md` | `04`, `07`, `08` |
| `07-propositions.md` | `03`, `06`, `09` |
| `08-iteration.md` | `04`, `06`, `10` |
| `09-output-and-display.md` | `07`, `08`, `13` |
| `10-theory-contract.md` | `03`, `04`, `11`, `12` |
| `11-theory-catalog.md` | `03`, `05`, `07`, `10` |
| `12-settings-and-registry.md` | `04`, `10`, `13` |
| `13-examples-and-cli.md` | `09`, `10`, `12` |
| `14-porting-notes.md` (hub) | any |

### D4. Document template

Every document under `haskell/py-spec/` follows this skeleton:

```markdown
# {Title}

[← Spec map](./README.md)

> One sentence stating exactly what this document specifies.

## {Sections}

## Source files

- [`syntactic/sentence.py`](../../code/src/model_checker/syntactic/sentence.py) — the `Sentence` node and its four-phase lifecycle
- ...

## Related

- [Operators](./03-operators.md) — {why}
```

`## Source files` is **required** in every document (not in `README.md`) and lists every
`code/src/model_checker/**` path the document describes, each with the relevant symbol named.

### D5. Codebase links

Relative, file-level, from the flat directory: `../../code/src/model_checker/{package}/{file}.py`.
Directory links (`.../theory_lib/logos/`) are permitted where a package as a whole is the subject.
**No line anchors** — they rot on the next edit. Name the symbol in prose instead
(``the `iterate_generator` loop in [`iterate/core.py`](...)``).

### D6. Diagrams

Mermaid fenced blocks (GitHub renders them natively). Diagram assignments per document are given
in the phases. A diagram must show a *mechanism* — flow, layering, lifecycle, or relationship —
never decorate a list. Keep node labels short; put the detail in the surrounding prose or a table.

### D7. Python code budget

At most **4 fenced Python blocks per document, ≤ 15 lines each**, and every block must be either
a real signature set or a faithful excerpt of real source (elision with `...` is fine; invention
is not). Prefer a markdown table to a code block for anything enumerable. Tables carry no budget.

### D8. Disposition of `haskell/py_spec.md`

**`haskell/py_spec.md` is deleted.** Its one-paragraph blurb is carried verbatim into the
abstract of `haskell/py-spec/README.md`. Rationale: nothing outside `specs/**` links to it, and a
pointer stub would be a second home for the abstract — precisely the two-sources-of-truth drift
the research documents at length in the Python system's own docs. Alternative considered and
rejected: reduce it to a three-line pointer at `haskell/py_spec.md`.

### D9. Deliverable hygiene

Files under `haskell/py-spec/**` are standalone deliverables. They MUST NOT mention task numbers,
`specs/` paths, research reports, findings files, or this plan
(`.claude/rules/no-task-references-in-deliverables.md`). Where a claim needs provenance, cite the
source file or the executable test that enforces it.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5, 6, 7, 8 | 1 |
| 3 | 9 | 1, 2, 3, 4, 5, 6, 7, 8 |

Phases within the same wave can execute in parallel. Wave 2 phases own disjoint file sets (see
each phase's **Files to create**) and must not write outside them; `README.md` is owned by
Phase 1 and Phase 9 only.

---

### Phase 1: Map, conventions, and the pipeline spine [COMPLETED]

**Goal**: Establish `README.md` as the map plus the conventions every later phase follows, and
write the spine document the rest of the tree hangs off.

**Tasks**:
- [ ] Write `haskell/py-spec/README.md`: title; the abstract (the blurb carried verbatim from
      `haskell/py_spec.md`); an "Audience and purpose" paragraph stating this is a description of
      the Python implementation at a level of generality suitable for designing a reimplementation,
      making no design decisions for any target language; a "Scope" note (version 1.3.3; ~46k
      production LOC across 11 packages; runtime dependencies `z3-solver` and `networkx`; the
      `oracle/` tree is out of scope); a "How to read this" paragraph naming `01-pipeline.md` as
      the entry point and `14-porting-notes.md` as the exit; the full grouped index with a
      forward link and one-line description for each of the 14 documents; a "Conventions" section
      recording D5 (file-level codebase links), D6 (mermaid), and that the executable contracts
      named in `10-theory-contract.md` are authoritative over the repository's prose docs.
- [ ] Add one mermaid flowchart to `README.md`: the five-stage pipeline in miniature, as
      orientation.
- [ ] Write `haskell/py-spec/01-pipeline.md` covering: the five-stage construction order
      (`Syntax` → theory `Semantics` → `ModelConstraints` → `ModelStructure` (solves) →
      `interpret`); what each stage consumes and produces; that solving happens inside
      `ModelStructure.__init__`; the ownership/reference graph and its downward aliasing; the
      acyclic-through-stage-4 / cyclic-at-interpretation property; and a short statement of the
      four lifecycle phases with a pointer to `02-syntax-and-ast.md`.
- [ ] Diagrams in `01-pipeline.md`: (a) `flowchart LR` of the five stages with the data shape on
      each edge; (b) `graph TD` of the object graph showing ownership edges and the
      `Sentence` ↔ `Proposition` ↔ `ModelStructure` cycle introduced at interpretation.
- [ ] Delete `haskell/py_spec.md` (D8), after confirming its blurb is present in `README.md`.

**Source material**: report §"Findings" 1.4 and 2.1; `findings/02_core-utilities.md` §1 (§1.1
canonical construction pipeline, §1.2 ownership graph, §1.3 cycles); `findings/01_compiler-pipeline.md`
§"Pipeline at a glance". Scope/measurement figures come from report Appendix C.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: this plan asserts a 15-file inventory (D2) and a 14-entry README index.
Confirm at implementation time by writing the index directly from the D2 table and checking
`ls haskell/py-spec/ | wc -l` equals 2 at the end of this phase (`README.md`, `01-pipeline.md`),
with the index naming exactly the 14 filenames in D2.

**Files to create**:
- `haskell/py-spec/README.md` — the map (overwrite the existing empty file)
- `haskell/py-spec/01-pipeline.md` — the spine

**Files to delete**:
- `haskell/py_spec.md` — per D8

**Verification**:
- `README.md` contains exactly 14 forward links matching the D2 filenames:
  `grep -oE '\]\(\./[0-9]{2}-[a-z-]+\.md\)' haskell/py-spec/README.md | sort -u | wc -l` → 14
- `01-pipeline.md` line 2 is exactly `[← Spec map](./README.md)`
- Both files contain a `## Source files` section (README exempt) and at least one
  ```` ```mermaid ```` block each
- Every relative link in both files resolves (run the resolver from `## Testing & Validation`)
- `haskell/py_spec.md` no longer exists and its blurb text appears in `README.md`
- `grep -nEi 'task [0-9]|specs/|findings/' haskell/py-spec/*.md` returns nothing

---

### Phase 2: The compiler front end [COMPLETED]

**Goal**: Specify the DSL surface syntax, the parser, the AST and its lifecycle, and the operator
abstraction.

**Tasks**:
- [ ] Write `02-syntax-and-ast.md`: token classes (atoms by `isalnum`, operators by leading `\`,
      the two hard-coded nullaries); the notational regime (unary prefix unparenthesized, binary
      infix mandatorily parenthesized, no precedence); tokenization; the recursive-descent
      algorithm and the depth-tracking main-connective scan; the nested prefix-list output shape
      with a worked example; the `Sentence` node's fields; the four-phase mutation lifecycle as a
      table (creation / type update / object update / proposition update) with the trigger and the
      field-type change at each; interning by infix string as hash-consing on syntactic identity;
      sentence letters as `Const(name, AtomSort)` and `AtomSort` being process-global; and the two
      verified parser gaps (leftover tokens silently discarded; arity never checked
      syntactically, with `ArityError` defined but never raised).
- [ ] Diagrams in `02`: (a) `stateDiagram-v2` of the four phases showing what each transition
      changes; (b) a small `graph TD` showing `((p \vee q) \rightarrow r)` as its nested prefix
      list.
- [ ] Write `03-operators.md`: the `Operator` base class fields; the six semantic methods as a
      signature table (`true_at`, `false_at`, `extended_verify`, `extended_falsify`,
      `find_verifiers_and_falsifiers`, `print_method`) with the note that none is declared on the
      base class and the contract is enforced by `AttributeError` at constraint time; splatted
      arguments plus the untyped `eval_point` dict; `DefinedOperator` and `derived_definition`
      returning nested prefix lists of operator *classes*, with arity validated by signature
      inspection; total eager expansion at phase 2 and its two consequences (a defined operator's
      own clauses are dead on the solve path; the circularity check runs after expansion);
      `OperatorCollection` as a name-keyed registry with silent first-registration-wins on
      duplicates; and the three-register pattern as the port-relevant headline.
- [ ] Diagram in `03`: `classDiagram` relating `Sentence`, `Operator`, `DefinedOperator`,
      `OperatorCollection`, and the theory semantics object.

**Source material**: `findings/01_compiler-pipeline.md` §1 (surface syntax, algorithm, prefix-list
shape), §2 (the `Sentence` class, lifecycle, infix rendering), §3 (operator abstraction,
`DefinedOperator`, `OperatorCollection`), §4 (the `Syntax` object, sentence letters and
`AtomSort`); report §1.1-1.3; `findings/05_theory-lib.md` §Q4 intro for the three-register framing
(the worked operator examples themselves belong to Phase 7, not here).

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to create**:
- `haskell/py-spec/02-syntax-and-ast.md`
- `haskell/py-spec/03-operators.md`

**Verification**:
- Both files match the D4 template (line 2 back-link; `## Source files` present)
- Sibling links confined to the D3 table rows for `02` and `03`
- ≤ 4 Python blocks per file, none over 15 lines
- Every relative link resolves; no task/specs references

---

### Phase 3: Constraint generation and the state encoding [COMPLETED]

**Goal**: Specify how a parsed formula becomes SMT constraints, and the bit-vector encoding those
constraints live in.

**Tasks**:
- [ ] Write `04-constraint-generation.md`: `ModelConstraints`' four labelled groups in order
      (frame / model / premise / conclusion) as a table naming what generates each; the
      `premise_behavior` / `conclusion_behavior` lambdas and the countermodel framing they encode
      (premises true and conclusions false at the designated point; `sat` = countermodel =
      invalid, `unsat` = valid), stated as a *baked-in* framing a port must decide to keep or
      generalize; the double-dispatch mutual recursion between the theory semantics and operator
      instances, including the base case on `sentence_letter`; the absence of subformula
      memoization; the `proposition_constraints` cross-class idiom and its restatement as a pure
      function `(settings, semantics, letter) -> [Constraint]`; and the `SemanticDefaults`
      contract split into what the base provides for free vs. what a theory must supply (with the
      note that nothing enforces the latter — failures surface as `NoneType is not callable`).
- [ ] Diagrams in `04`: (a) `flowchart TD` of the four constraint groups converging on the solver
      with their tracking labels; (b) `sequenceDiagram` of `semantics.true_at` ↔ `operator.true_at`
      double dispatch over a two-level formula.
- [ ] Write `05-state-encoding.md`: `N` and the `2^N` state space, `MAX_N = 20` with the recorded
      RSS measurements; mereology over bit-vectors (fusion as `|`, part-of as `s | t == t`, proper
      part, product/coproduct); the full encoding table (state, fusion, part-of, null/full,
      possible, compatible, world, atomic truthmaking, truth at a world, sentence letter); finite
      quantifier expansion as a *semantic* choice, not an optimization, with the `(2^N)^k` cost
      model, no sharing between call sites, and the inconsistency that some sites use native Z3
      quantifiers (hence the MBQI/e-matching configuration); and `M` / `all_times` for temporal
      theories.
- [ ] Diagram in `05`: `graph BT` of the N=2 state lattice under parthood (∅, a, b, a.b) with the
      display-name convention noted.

**Source material**: `findings/01_compiler-pipeline.md` §5 (`ModelConstraints`, the recursive
constraint compiler, `SemanticDefaults`, quantifiers) and §7 (bit-vector encoding);
`findings/02_core-utilities.md` §1.4 (the `proposition_constraints` idiom) and §4 (the base
semantics contract); report §1.4-1.6.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to create**:
- `haskell/py-spec/04-constraint-generation.md`
- `haskell/py-spec/05-state-encoding.md`

**Verification**:
- The encoding table in `05` reproduces all rows from the research encoding summary
- D4 template, D3 sibling ceiling, D7 code budget all satisfied
- Every relative link resolves; no task/specs references

---

### Phase 4: Solving, results, and propositions [NOT STARTED]

**Goal**: Specify the solver boundary, the shape of a solve result, and the semantic value a
solved model assigns to each sentence.

**Tasks**:
- [ ] Write `06-solver-and-results.md`: the backend abstraction (`SolverProtocol` /
      `TrackedSolverProtocol` operations, Z3 and cvc5 adapters, backend selection priority);
      per-group tracked assertion labels and the labelled unsat core they yield; `max_time` in
      **seconds** (converted to ms at the boundary — note the docstring is wrong); **unknown is
      always a timeout, never `unsat`**, as a soundness rule with its rationale; no incremental
      solving on the main path and no constraint caching; per-example C-level context isolation and
      why (learned-lemma leakage, 2-10× slowdowns); the single-threaded construction invariant and
      the reentrant guard that enforces it, stated as an invariant a port must preserve even if it
      drops the mechanism; and `ModelStructure`'s ten-field mutable solver-state block with the
      spec-level restatement as `build : Constraints -> Problem` plus
      `solve : Problem -> Result` where `Result = SAT model | UnsatCore [Label] | Timeout`.
- [ ] Diagram in `06`: `stateDiagram-v2` of a solve — assert-tracked → check → {sat / unsat /
      unknown} with unknown routed to timeout, and what each terminal state populates.
- [ ] Write `07-propositions.md`: a proposition as *the semantic value of one sentence in one
      solved model*, constructed eagerly bottom-up exactly once per solved model; the per-theory
      contract (`proposition_constraints` at constraint time; `find_proposition` /
      `find_extension` / `truth_value_at` / `print_proposition` post-solve); evaluation points as
      untyped dicts (`{"world": w}` vs `{"world": id, "time": t}`); the three post-solve extraction
      names discovered at runtime (`find_verifiers_and_falsifiers`, `compute_verifiers`,
      `find_truth_condition`) and the spec-level statement that "evaluation scheme" should be an
      explicit abstraction with at least three inhabitants; and the hazard that `__hash__`/`__eq__`
      are by formula name only, so propositions from different models compare equal.
- [ ] Diagram in `07`: `flowchart TD` of post-solve interpretation — solved model → bottom-up
      proposition construction per sentence node → truth value at the evaluation point.

**Source material**: `findings/01_compiler-pipeline.md` §6 (solver package roles, `z3_shim`,
solver invocation, adapter specifics); `findings/02_core-utilities.md` §2 (`ModelDefaults` state
and mutation timeline), §3 (`PropositionDefaults`), §4.1 (concurrency contract); report §1.6, §2.2,
§2.3, §2.4; `findings/05_theory-lib.md` §"Variant method sets in other theories" for the three
extraction names.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to create**:
- `haskell/py-spec/06-solver-and-results.md`
- `haskell/py-spec/07-propositions.md`

**Verification**:
- `06` states the unknown-as-timeout rule and the seconds unit explicitly
- D4 template, D3 sibling ceiling, D7 code budget all satisfied
- Every relative link resolves; no task/specs references

---

### Phase 5: Post-solve tooling — iteration, output, comparison [NOT STARTED]

**Goal**: Specify the machinery for finding further countermodels and for presenting them.

**Tasks**:
- [ ] Write `08-iteration.md`: the live loop (generate difference constraints against all previous
      models → permanently add and `check` → extract → rebuild a full `ModelStructure` → reject
      zero-world models → isomorphism check → accept, diff, yield); the **two-tier notion of
      distinctness** (syntactic difference enforced by constraints; semantic distinctness up to
      isomorphism enforced post hoc by a graph check) as the central concept; the generic
      difference constraint's shape; how MODEL 2+ is rebuilt by pinning the found model's concrete
      values as constraints and re-solving; what the isomorphism check does and does not see
      (no `node_match`/`edge_match`, so valuations and hyperintensional structure are invisible);
      the termination budgets (`iterate` target, per-search `max_time`, consecutive-invalid cap,
      lack-of-progress heuristic, exhaustion, interrupt) and that a mid-iteration timeout keeps
      previously yielded models; and the spec-level statement that the theory-declarative half is
      a per-theory list of "model dimensions".
- [ ] Diagram in `08`: `flowchart TD` of one iteration attempt with both distinctness gates and
      every termination exit.
- [ ] Write `09-output-and-display.md`: the three output modes that actually exist (ANSI terminal,
      combined `EXAMPLES.md`, combined `MODELS.json`) and that nothing reads the JSON back;
      capture-then-format (stdout redirect → StringIO → ANSI-regex to markdown) contrasted with
      the specified `model → typed result → renderer`; the display contract a theory must satisfy
      (`print_to`, `print_all`, `print_states`, `print_evaluation`; `print_proposition`;
      operator `print_method` and the three base helpers); recursive truth-tree printing as mutual
      recursion producing the indented evaluation tree, and the identity-test colour hazard under
      capture; `--maximize` as *maximum reachable `N` per theory within the time limit* (not
      validity agreement), one process per theory; genuine cross-theory comparison being the
      ordinary path with translation dictionaries; and the progress bar / deferred-completion
      protocol.
- [ ] Diagram in `09`: `flowchart LR` contrasting the two paths — the implemented
      capture-then-format chain above, the specified data-then-render chain below.

**Source material**: `findings/03_tools-features.md` §1-5 (iteration algorithm, iterator
architecture, isomorphism, differences, termination) for `08`; §6-10 (output subsystem, printing
contract, saving, `--maximize`, progress) for `09`; report §3.1-3.3. The dead-code inventory in
`iterate/` is *named* here in one sentence and *detailed* in `14-porting-notes.md`.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to create**:
- `haskell/py-spec/08-iteration.md`
- `haskell/py-spec/09-output-and-display.md`

**Verification**:
- `08` states both tiers of distinctness explicitly and enumerates every termination condition
- D4 template, D3 sibling ceiling, D7 code budget all satisfied
- Every relative link resolves; no task/specs references

---

### Phase 6: The theory contract and the theory catalog [NOT STARTED]

**Goal**: Specify what makes something a theory in this framework, and describe the four shipped
theories as instances of that contract.

**Tasks**:
- [ ] Write `10-theory-contract.md`: `get_theory(config=None) -> {semantics, proposition, model,
      operators}` as the single entry point; the required module set (a `semantic/` **package**
      with re-export-only `__init__.py`, `core.py`, `model.py`, plus `operators.py`, `iterate.py`,
      `examples.py`, `tests/`, `docs/`); the semantics-class requirements
      (`DEFAULT_EXAMPLE_SETTINGS` including `iterate`, `frame_constraints`, `premise_behavior`,
      `conclusion_behavior`, `main_point`, the truth-condition dispatchers); the `examples.py`
      attribute set defined exactly once each; the `iterate.py` entry points and the marker
      attribute detected by `hasattr` that silently degrades to the eager path when absent; the
      **layering rule** (core may never import the theory library, by any mechanism, and may never
      hardcode a theory name; the theory library may import core freely; only the upper layer knows
      both) presented as an enforced invariant with the enforcing tests named; the four executable
      contracts as authoritative over prose docs; and the logos subtheory system (four subtheories,
      the hardcoded dependency graph, semantics never defined in a subtheory, subset loading as a
      first-class feature, zero-operator subtheories being defects by rule).
- [ ] Diagrams in `10`: (a) `flowchart TD` of the three layers with arrow direction and the
      forbidden edge marked; (b) `graph LR` of the logos subtheory dependency graph.
- [ ] Write `11-theory-catalog.md`: the four-theory comparison table (model theory, atomic
      primitives, distinctive machinery, operator count); the two families — the state-mereology
      family (logos as trunk, exclusion subclassing it, imposition reusing its proposition class,
      model structure, and operator classes) and bimodal as a genuinely different model theory
      (world histories, no verifiers, integer times, ternary task relation, (world-id, time)
      evaluation points); per-theory specifics kept to a paragraph each; and **one** worked
      operator walkthrough showing the three registers diverging — the counterfactual operator,
      whose symbolic clause, concrete verifier computation, and print method each independently
      re-derive alternative worlds.
- [ ] Diagram in `11`: `graph TD` of theory reuse — what exclusion and imposition inherit or reuse
      from logos, and bimodal's separate descent from the abstract core.

**Source material**: `findings/05_theory-lib.md` §Q2 (the theory contract: hard requirements, soft
requirements, layering rule, subtheory contract) and §Q3 (logos in depth, the subtheory system) for
`10`; §Q1 (theory inventory), §Q4.4 (the counterfactual walkthrough), §Q5 (cross-theory variation),
§Q6-Q7 (bimodal, exclusion/imposition specifics) for `11`; report §5.1-5.4.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: this phase asserts per-theory operator counts (logos 18 with all subtheories
loaded, bimodal 17, imposition 13, exclusion 4) and the four-subtheory operator split (extensional
7, modal 4, constitutive 5, counterfactual 2). These come from the research measurements; before
stating them, confirm against `findings/05_theory-lib.md` §Q1 and §Q3, and state them as "as of
version 1.3.3" rather than as timeless facts.

**Files to create**:
- `haskell/py-spec/10-theory-contract.md`
- `haskell/py-spec/11-theory-catalog.md`

**Verification**:
- `10` names the layering rule and the executable contracts that enforce it, with links to those
  test files under `../../code/`
- `11` contains exactly one worked operator walkthrough (not four)
- D4 template, D3 sibling ceiling, D7 code budget all satisfied
- Every relative link resolves; no task/specs references

---

### Phase 7: Settings, registry, examples, and the CLI [NOT STARTED]

**Goal**: Specify the configuration model and the surface through which a user actually drives the
system.

**Tasks**:
- [ ] Write `12-settings-and-registry.md`: the three declaration sites (base general settings; the
      per-theory example and additional-general defaults; the dead module-level fallback); the
      six-step precedence chain, lowest to highest, with the fragile last step (only CLI flags the
      user *actually typed* win, determined by re-scanning raw argv against a hand-maintained
      short→long map, with clustered short flags a known gap); unknown settings producing a printed
      warning and being discarded unless an opt-in strict mode is set that nothing enables, and
      that this contradicts the project's stated fail-fast principle; the setting inventory table
      with per-theory defaults; the `iterate` type-soundness note (specify as a natural number
      ≥ 1); the registry as a generic mechanism containing zero theory-name literals, with a
      four-component entry, thunks memoized per theory, idempotent registration, and deferred
      import errors surfacing at first component access; and the error-handling policy stated
      *as a policy* (strict where a wrong logical verdict is possible; absorbing with placeholders
      in presentation and metadata; warnings for configuration).
- [ ] Diagram in `12`: `flowchart TD` of the settings precedence chain as a merge cascade.
- [ ] Write `13-examples-and-cli.md`: the example file as an ordinary Python module executed on
      load; the two required module-level names and one optional; `TheoryDict`'s validated keys
      plus the `dictionary` operator-rename map applied by plain string replacement before parsing;
      `ExampleCase` as `[premises, conclusions, settings]`; the `{PREFIX}_CM_{n}` /
      `{PREFIX}_TH_{n}` conventions and the `expectation` oracle bit as the actual behavioral
      specification; the curated `example_range` vs. full `unit_tests` distinction and the logos
      aggregation caveat; examples-as-tests (theory tests parametrize over `unit_tests` and rebuild
      the pipeline without the builder); the spec-level statement that a declarative core is
      strictly easier to port, verify, and sandbox than configuration-by-arbitrary-code-execution;
      the CLI surface as a flag table; the three entry points; project generation, Jupyter's
      two-tier integration, and packaging, each in a short paragraph.
- [ ] Diagram in `13`: `flowchart TD` of `model-checker examples.py` — module load → per named
      theory → per example → build → solve → print → optional save.

**Source material**: `findings/02_core-utilities.md` §5 (settings: declaration, precedence,
validation, inventory), §7 (registry / theory discovery), §8 (public API surface), §9 (error
handling philosophy) for `12`; `findings/04_ui-cli.md` §1 (CLI surface), §2 (entry points),
§3 (execution flow), §4 (example-file format), §5 (project generation), §7 (Jupyter), §8
(packaging), §9 (examples as tests) for `13`; report §2.5, §4.1-4.3, §5.5.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: this phase asserts the CLI has 17 options over one positional argument, and
reproduces the per-theory settings defaults and the ~253-example corpus figure. Confirm the flag
table against `findings/04_ui-cli.md` §1 before writing it, and mark the one flag that is
registered but raises `NotImplementedError` as nonfunctional rather than omitting it.

**Files to create**:
- `haskell/py-spec/12-settings-and-registry.md`
- `haskell/py-spec/13-examples-and-cli.md`

**Verification**:
- The precedence chain in `12` is stated as an ordered list of exactly the documented steps
- The CLI table in `13` marks the nonfunctional flag explicitly
- D4 template, D3 sibling ceiling, D7 code budget all satisfied
- Every relative link resolves; no task/specs references

---

### Phase 8: Porting notes [NOT STARTED]

**Goal**: Give a reader the cross-cutting judgement layer: what must be preserved, what must not
be reproduced, and what is known to be wrong.

**Tasks**:
- [ ] Write `14-porting-notes.md` in four sections:
      (a) **Semantics to preserve** — finite quantifier expansion with its cost model, the
      unknown-as-timeout rule, the countermodel framing, the bit-vector encoding, the
      settings-gated atomic-proposition constraint menu, the one-way core/theory dependency, the
      registry as sole source of theory identity, one canonical theory module set, serialized
      model construction, per-example solver isolation;
      (b) **Mechanism not to reproduce** — the single mutable `Sentence` carrying phase-dependent
      field types (state the four phases as four types), solve-inside-the-constructor plus the
      ten-field flag cluster (state a result sum type), capture-then-format output, the three
      independently-written operator registers, three unrelated post-solve extraction method names,
      `sys.path` mutation and configuration-by-code-execution, `hasattr` capability detection,
      opt-in-only settings strictness;
      (c) **Known defects in the described implementation** — the four verified defects, each
      stated as one sentence naming the file, with an explicit note that these are defects in the
      Python system, are not fixed by this document, and should not be reproduced;
      (d) **Dead code and documentation reliability** — the dead-code inventory (the disabled
      sequential-save subsystem, the duplicate iteration loops, the unused push/pop difference
      search and injection module, the aspirational protocol vocabularies) and a standing warning
      that the repository's prose architecture docs contain verified-false API claims, with the
      four executable contracts named as the authoritative alternative.
- [ ] No diagram required in `14`; it is a table-and-list document. Use tables for (a) and (b).
- [ ] As a hub document, `14` links back to the specific document covering each item.

**Source material**: report §"Decisions", §"Recommendations", §"Risks & Mitigations", §6
(documentation reliability), Appendix B; the `## Improvement Opportunities` and
`## Doc/Source Divergences` sections of all five findings files.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: this phase asserts "four verified defects" and an enumerated dead-code list.
Confirm both against the research report's Decisions section and the findings files' Improvement
Opportunities sections before writing; if the count differs, write what the sources support rather
than forcing the number.

**Files to create**:
- `haskell/py-spec/14-porting-notes.md`

**Verification**:
- All four sections present; each defect names a source file
- Section (d) names the four executable contracts with links under `../../code/`
- Every relative link resolves; no task/specs references

---

### Phase 9: Navigation audit and tree acceptance [NOT STARTED]

**Goal**: Prove the navigation contract holds across the finished tree and reconcile the map with
what was actually written.

**Tasks**:
- [ ] Run the link resolver (below) over the whole directory; fix every broken relative link.
- [ ] Verify the file inventory matches D2 exactly — no extra files, none missing.
- [ ] Verify every document's line 2 is exactly `[← Spec map](./README.md)`.
- [ ] Verify `README.md` forward-links all 14 documents and that no README link points at a
      nonexistent file.
- [ ] Audit sibling cross-links against the D3 table: flag any link outside a document's
      sanctioned row, any non-hub document exceeding four sibling links, and any bare link with no
      stated reason. Remove or justify each.
- [ ] Verify every document has a non-empty `## Source files` section and that every path listed
      there exists under `code/src/model_checker/`.
- [ ] Verify the D7 code budget (≤ 4 Python blocks per file, ≤ 15 lines each) and that every
      mermaid block is well-formed enough to render (balanced fences, a declared diagram type on
      the first line).
- [ ] Verify D9: no occurrence of a task number, a `specs/` path, or a research-artifact reference
      anywhere under `haskell/py-spec/`.
- [ ] Confirm `haskell/py_spec.md` is gone and its blurb survives in `README.md`.
- [ ] Update `haskell/TODO.md`: mark the "describe model-checker architecture in python" bullet
      and its five sub-bullets as done, pointing at `py-spec/README.md`. Leave the rest of that
      file untouched.
- [ ] Read the tree end to end once as a reader would, and fix any place where two documents
      contradict each other or repeat the same explanation at length (a short restatement with a
      link is fine; a duplicated section is not).

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8

**Verification Tier**: prose

**Scope Hypothesis**: this phase asserts the tree contains exactly 15 files. Confirm with
`ls haskell/py-spec/`; if a phase legitimately split or merged a document, amend D2 in this plan
and the README index together rather than silently accepting the divergence.

**Files to modify**:
- `haskell/py-spec/README.md` — reconcile the index with what exists
- `haskell/py-spec/*.md` — link and contract fixes only
- `haskell/TODO.md` — mark the architecture bullet done

**Verification**:
- The full acceptance script under `## Testing & Validation` exits clean
- A manual read-through confirms no contradictions and no duplicated sections

---

## Testing & Validation

Run from the repository root. All checks must pass before the task is complete.

- [ ] **Inventory**: `ls haskell/py-spec/ | sort` lists exactly the 15 D2 filenames.
- [ ] **Relative links resolve** (internal and into the codebase):
```bash
cd haskell/py-spec && grep -ohE '\]\([^)]+\)' *.md | sed -E 's/^\]\(//; s/\)$//' \
  | grep -v '^https\?://' | sed 's/#.*$//' | sed '/^$/d' | sort -u \
  | while read -r l; do [ -e "$l" ] || echo "BROKEN: $l"; done
```
  Expect no output.
- [ ] **Back-links**: `for f in haskell/py-spec/[0-9]*.md; do sed -n '2p' "$f" \
      | grep -qF '[← Spec map](./README.md)' || echo "MISSING BACKLINK: $f"; done` → no output.
- [ ] **Forward links**: `grep -oE '\]\(\./[0-9]{2}-[a-z-]+\.md\)' haskell/py-spec/README.md \
      | sort -u | wc -l` → 14.
- [ ] **Source-files section present**: `for f in haskell/py-spec/[0-9]*.md; do \
      grep -q '^## Source files' "$f" || echo "NO SOURCE FILES: $f"; done` → no output.
- [ ] **Code budget**: `for f in haskell/py-spec/*.md; do n=$(grep -c '^```python' "$f"); \
      [ "$n" -le 4 ] || echo "OVER BUDGET: $f ($n)"; done` → no output.
- [ ] **Mermaid present where planned**: every document except `14-porting-notes.md` contains at
      least one ```` ```mermaid ```` block; fences are balanced
      (`grep -c '^```' "$f"` is even for every file).
- [ ] **Deliverable hygiene**: `grep -rnEi 'task [0-9]|specs/|\.return-meta|findings/|reports/' \
      haskell/py-spec/` → no output.
- [ ] **Disposition**: `test ! -e haskell/py_spec.md`.
- [ ] **No source changes**: `git status --short code/` → no output (this task writes no Python).

## Artifacts & Outputs

- `haskell/py-spec/README.md` — the map
- `haskell/py-spec/01-pipeline.md` … `haskell/py-spec/14-porting-notes.md` — 14 specification
  documents per the D2 inventory
- `haskell/py_spec.md` — **deleted** (D8)
- `haskell/TODO.md` — architecture bullet marked done, pointing at the new map
- `specs/164_populate_py_spec_python_architecture/summaries/01_py-spec-document-tree-summary.md`
  — implementation summary (written at completion)

## Rollback/Contingency

All changes are confined to `haskell/`. `git checkout -- haskell/` restores the pre-task state
(including `py_spec.md`, which is tracked); no Python source, tests, or packaging is touched, so
nothing can regress the test suite. If a single phase's document proves too large for one agent
run, split it into two documents, amend D2 and the README index together in the same run, and note
the split in the phase's completion record — never leave the index and the tree out of step.
