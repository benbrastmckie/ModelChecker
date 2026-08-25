# Research Report: Haskell Porting Readiness of haskell/py-spec

- **Task**: 165 - Improve py-spec for Haskell port
- **Started**: 2026-08-19T05:40:00Z
- **Completed**: 2026-08-19T06:19:00Z
- **Effort**: ~2.5 hours (agent time), 3 parallel verification sub-agents + direct source cross-checks
- **Dependencies**: None
- **Sources/Inputs**:
  - `haskell/py-spec/README.md` and `01-pipeline.md` through `14-porting-notes.md` (all 15 files, full read)
  - `code/src/model_checker/**` (Python source, targeted reads: `syntactic/`, `models/`, `solver/`,
    `iterate/`, `output/`, `settings/`, `registry.py`, `theory_lib/logos/**`,
    `theory_lib/exclusion/**`, `theory_lib/imposition/**`, `theory_lib/bimodal/**`, `__main__.py`,
    `pyproject.toml`)
  - `code/tests/test_layering.py`, `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`
  - `.claude/context/formats/report-format.md`
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **Verdict: no.** A competent Haskell developer cannot build a behaviorally faithful port from
  this tree today. The three things that most block them: (1) **no operator ever has its truth
  condition stated** — `03-operators.md` gives method *signatures* only, for negation through
  the counterfactual; (2) the semantic helper predicates the counterfactual/modal operators
  depend on (`is_alternative`, `maximal`, `compatible`, `max_compatible_part`) and the concrete,
  exhaustive frame-constraint list are never given; (3) the **exclusion** theory's Skolem
  witness-predicate mechanism — the hardest, most failure-prone part of the four shipped
  theories to get right — is reduced to a five-word adjective phrase in one table cell with zero
  further specification anywhere in the tree.
- Everywhere the spec's checkable claims were sampled (construction order, parser gaps, solver
  backend selection, tracked-assertion labels, quantifier config, the mutable-field inventory,
  proposition identity, iteration rebuild-and-pin, theory conformance, layering, settings
  precedence, CLI surface, LOC/version/dependency counts) **it was accurate**, often to the exact
  line. The problem is not correctness, it is **depth**: the tree is a faithful map of
  *architecture* (control flow, object graph, construction order) but omits the *content*
  (truth conditions, helper-predicate definitions, one theory's core mechanism) that a port
  actually needs to write total functions from.
- A worked end-to-end example, a glossary, and any conformance artifact showing a concrete
  expected model (not just sat/unsat) are entirely absent — a porter has no golden trace to
  validate a first working stage-1-through-5 run against.
- Roughly a third of `13-examples-and-cli.md` (CLI ergonomics, entry-point plumbing, project
  generation / Jupyter / packaging) and about half of `09-output-and-display.md`'s mechanism
  prose describe Python-specific machinery a port would design fresh, not reproduce; both are
  candidates for compression, not because they're wrong but because they spend space the tree's
  own stated philosophy ("no design decisions for any target language") says isn't theirs to
  spend.
- The 14-document decomposition-by-pipeline-stage is structurally sound and should be kept; it
  needs one new document (operator semantics), one new short artifact (a worked trace / glossary),
  and targeted expansion of the theory-catalog treatment of exclusion — not a reorganization.

## Context & Scope

Reviewed the entire `haskell/py-spec/` tree (15 files, ~1,677 lines) against the Python
implementation it describes (`code/src/model_checker/`, v1.3.3), through the single lens stated
in the task: could a competent Haskell developer, given only this tree and the linked source,
write a behaviorally faithful port? All 15 documents were read in full. Verification used three
parallel sub-agents, each independently cross-checking a subset of documents (01–05, 06–09,
10–14) against source with file:line evidence, plus direct spot-checks by the reviewing agent on
the operator-semantics gap (the single highest-severity finding), determinism/ordering concerns,
the error/exception taxonomy, and the scope claims in the README.

## Findings

Findings are grouped by what a porter needs (A, ranked by severity — the primary deliverable),
then accuracy spot-checks (B).

### A. Missing information (severity-ranked)

**A1 — CRITICAL. No operator has a stated truth condition; only method shapes exist.**
`03-operators.md`'s table gives `true_at`/`false_at`/`extended_verify`/`extended_falsify`/
`find_verifiers_and_falsifiers`/`print_method` as *signatures* — arity and argument shape — never
the formula each computes. Confirmed empty for every sampled operator:
- `NegationOperator.true_at` = `semantics.false_at(argument, eval_point)` — pure delegation
  (`theory_lib/logos/subtheories/extensional/operators.py:41-43`).
- `AndOperator.extended_verify` = `∃x,y. verify(x,A) ∧ verify(y,B) ∧ state = fusion(x,y)`; `Or`'s
  is the structurally different disjunctive mirror (`extensional/operators.py:93-183`).
- `ConditionalOperator` (`\rightarrow`), despite being a `DefinedOperator`, hand-maintains a full
  independent `true_at`/`extended_verify` (`extensional/operators.py:300-354`) — the "dead code
  on the solve path" duplication `03-operators.md` warns about abstractly is never shown
  concretely for the one operator where a porter would most want to see it.
- `NecessityOperator.true_at` = `∀u. is_world(u) → true_at(A, world:=u)` — quantifies over
  `is_world` states only, not all `2^N`; its `extended_verify` collapses to
  `state == null_state ∧ true_at(...)` (`modal/operators.py:44-73`).
- `CounterfactualOperator.true_at` = `∀x,u. (extended_verify(x,A,pt) ∧ is_alternative(u,x,w)) →
  true_at(B, world:=u)` (`counterfactual/operators.py:43-58`) — `04-constraint-generation.md`'s
  double-dispatch diagram never shows this formula or names `is_alternative`.
- `MightCounterfactualOperator.true_at` is defined as
  `¬CounterfactualOperator.true_at(A, ¬B, pt)`, implemented by constructing a
  `CounterfactualOperator()` instance ad hoc and manually setting `.semantics`
  (`counterfactual/operators.py:198-207`) — an unusual construction pattern bypassing
  `Operator.__init__`/`OperatorCollection` entirely, undocumented anywhere in 03.

Without this, no formula — not even conjunction — can be translated to a constraint from the
spec tree alone. This is the port's actual blocker, and it is the single most valuable thing to
add.

**A2 — CRITICAL. The helper predicates the counterfactual/modal operators are built on are
undefined, and the frame-constraint list is smaller and more concrete than the tree implies.**
`LogosSemantics.__init__` declares exactly **two** frame constraints —
`possibility_downward_closure` and `is_world(main_world)` (`theory_lib/logos/semantic/core.py:83-108`)
— not the open-ended "model-shape axioms" `04-constraint-generation.md` implies. `is_world(w) =
possible(w) ∧ maximal(w)`, and `maximal`, `is_alternative`, and `max_compatible_part` are three
separate, load-bearing helper predicates (`core.py:118-149, ~280-347`) that never appear in
`04-` or `05-`. `compatible(x,y) = possible(fusion(x,y))` is used pervasively but only glossed
informally in 05's table. `verify`/`falsify` are declared as genuine `z3.Function(name,
BitVecSort(N), AtomSort, BoolSort())` (uninterpreted first-order functions), `possible` as
`z3.Function(name, BitVecSort(N), BoolSort())` (`core.py:63-80`) — the exact Z3 signature form a
Haskell SMT binding needs is never spelled out, only named informally.

**A3 — HIGH. The exclusion theory's core mechanism (Skolem witness predicates) is one adjective
phrase, nowhere specified.** `11-theory-catalog.md`'s table cell says "per-formula Skolem witness
functions making minimality-quantified negation first-order" — four words of mechanism for what
is, in the actual source, a dedicated 126-line `WitnessRegistry` (`theory_lib/exclusion/semantic/registry.py`)
that declares a fresh pair of Z3 functions `h_pred, y_pred : BitVec(N) → BitVec(N)` per formula
string, keyed and cached by formula identity, consumed by `excludes`-relation constraints in
`theory_lib/exclusion/semantic/core.py` (572 lines) and `constraints.py` (175 lines). This is
historically the hardest part of unilateral/exclusion truthmaker semantics to implement
correctly (a documented source of published errata in the literature this theory is drawn from)
and exactly the kind of thing the task's own review brief calls out as needing to be "specified
sharply enough to implement... without reading Python." It is not.

**A4 — HIGH. Iteration's isomorphism check computes attributes it then discards — not merely
"blind" to them.** `08-iteration.md` says the isomorphism check is "blind to proposition
valuations." In fact `iterate/graph.py:75-121` computes and stores per-node sentence-letter
truth-value properties, and the comparison at `graph.py:494` calls `nx.is_isomorphic(g1, g2)`
with **no `node_match`/`edge_match`**, so that computed data is built and then silently ignored.
A porter reproducing "attribute-blind by design" vs. "attribute-blind by omitted argument" needs
to know which one this is, since the fix (the tree itself recommends attribute-matching) is a
one-argument change, not a rebuild. Related: known-defect #1 ("iterates over the first N states
rather than all `2^N`," named in `14-porting-notes.md` without a citation) is precisely
`iterate/constraints.py:296-311` (`_generate_input_combinations(1, N)` over `range(domain_size)`
where `N` is the bit-width, not the state count) — `08-iteration.md` itself never cites this
file/line even though it is the exact defect `14-` references by description only.

**A5 — MEDIUM. No survey of the error/exception taxonomy; edge-case behavior stated as policy,
not as cases.** Nine dedicated error modules exist (`output/errors.py`, `settings/errors.py`,
`iterate/errors.py`, `models/errors.py`, `theory_lib/errors.py`, `syntactic/errors.py`,
`builder/error_types.py` with 9 exception classes, `builder/errors.py`) implementing the policy
`12-settings-and-registry.md` states in prose ("errors that could produce a wrong logical verdict
are handled strictly; presentation/metadata absorb; configuration warns"). No document maps that
policy onto the actual class hierarchy, or states concrete edge-case behavior: `N` is validated
to `[1, MAX_N]` and raises `SemanticError` outside that range (`models/semantic.py:142-176`), but
this exact exception type and range are not named in `12-`'s setting table (which says only
"positive int, ≤ MAX_N"). Empty premises/conclusions and malformed-formula error shapes are
likewise never surveyed as a case table, only touched incidentally (the two parser gaps in `02-`).

**A6 — MEDIUM. Determinism/ordering of verifier/falsifier sets is unaddressed.** Verifier and
falsifier extraction (`find_proposition`, `theory_lib/logos/semantic/proposition.py:192-210`)
returns real Python `set()` objects — unordered by contract. Neither `05-state-encoding.md` nor
`07-propositions.md` says whether display/output order is meant to be canonical (e.g., sorted by
bit-vector value) or incidental. This is exactly the "ordering, determinism, identity" class the
review brief calls out by name as prone to breaking silently in a pure-functional port (a
Haskell `Data.Set` orders by `Ord`, which will not accidentally match Python's set-iteration
order) and a porter building golden-output tests needs to know which one is intended.

**A7 — LOW/MEDIUM, several smaller gaps** (each independently confirmed against source):
- The exact `Result`-tuple shape underlying `06-solver-and-results.md`'s "raw positional result
  tuple" is `(is_timeout: bool, model_or_core: Any, is_satisfiable: bool, runtime: float)`
  (`models/structure.py:199-213`, via `_create_result`) — not spelled out, though it directly
  informs the target `Result` sum type the document itself recommends.
- ANSI→Markdown conversion (`09-`) only gives red/green semantic meaning
  (`**bold**`/`_italic_`); every other ANSI code is stripped (`output/formatters/markdown.py:108-140`)
  — not documented, relevant only if a port intends to reproduce this output mode rather than
  redesign it (see B2 below).
- The registry's fuller API (`set_adapter`, `set_default_theory`, `get_default_theory`,
  `iter_theories`) is unmentioned in `12-`; a porter designing the Haskell registry interface
  needs the complete surface, not just registration/lookup.
- Settings type/range validators beyond the bare type column (`settings.py:303-385`) aren't
  surveyed.
- Tracked-assertion Z3 vars are created via `z3.Bool(label)` with uniqueness scoped to one
  `_setup_solver` call (`z3_adapter.py:86`) — worth naming for a port using a similar
  tracked-assertion design, not itself a defect.

### B. Not needed / cuttable material

- **`13-examples-and-cli.md`, "Project generation, Jupyter, and packaging" section (~25 lines,
  roughly a third of the document)**: describes machinery the tree's own `14-porting-notes.md`
  table would classify as "mechanism not to reproduce" (regex version rewriting, `hasattr`-gated
  Jupyter degrade, importlib-manifest project copying) but does so at CLI/UX narrative length
  instead of the terse "what, not how" the rest of the tree uses. **Recommend**: compress to a
  single paragraph pointing at `14-`'s table, ~2/3 reduction of this section. The CLI *flag
  table* itself (17 options → settings mapping) should stay; the short-flag letters and the
  three-entry-points prose (console script / `python -m` / dev wrapper prepending the source
  tree) are pure Python packaging trivia a Haskell CLI (e.g. `optparse-applicative`) would design
  fresh — cut the entry-points paragraph entirely.
- **`09-output-and-display.md`**, the "Recursive truth-tree printing" paragraph's detail on
  "color choice is decided by testing object identity against the real terminal stdout" — this
  is a Python-stdout-redirection implementation detail with no analogue in a typed port and no
  invariant to preserve (unlike the capture-then-format vs. data-then-render framing above it,
  which *is* worth keeping). **Recommend**: cut to one sentence, ~1/3 reduction of that
  subsection.
- No whole document is dead weight — each of the 14 documents carries information a porter needs
  and does not duplicate another document's content. The apparent repetition between `03-`'s
  general three-register claim and `11-`'s worked counterfactual example is deliberate
  (general claim → concrete instance), not redundant, and should stay as-is.
- `14-porting-notes.md`'s "known defects" and "dead code" sections are correctly placed —
  they are framed as porter-facing warnings ("not to be reproduced"), not code-review commentary
  about the Python codebase for its own sake, and each entry ties to a semantic invariant. Keep.

### C. Accuracy spot-checks

Sampled broadly (construction order, parser algorithm, mutable-state inventory, backend
selection precedence, quantifier configuration, tracked-assertion labels, timeout unit
conversion, proposition identity, rebuild-and-pin procedure, theory conformance test contents,
layering enforcement, settings precedence, CLI flag count, operator counts per theory, LOC/test
counts, version, dependencies) — **every claim checked out**, several to the exact line
(e.g. the max_time docstring-says-milliseconds-but-is-seconds claim, `models/structure.py:244`
vs. `:262`; the single-threaded guard's exact mechanism, `models/concurrency.py:61-111`; the
`PropositionDefaults.__eq__`/`__hash__` name-only identity claim, `models/proposition.py:74-80`).
Two minor imprecisions found, neither materially misleading:
- `07-propositions.md`'s source-files list credits
  `theory_lib/logos/semantic/proposition.py` with *defining* `find_verifiers_and_falsifiers`;
  it only calls it (`proposition.py:231`) — the method is defined per-operator across four
  subtheory files plus a protocol (`theory_lib/logos/protocols.py:138`).
- `10-theory-contract.md`'s "core imports theory_lib in zero places, theory_lib imports core in
  roughly ninety places" is directionally right but loosely quantified (grep gives ~57
  files / 208 import statements for the theory→core direction).

README's scope claims are all accurate: v1.3.3 (`pyproject.toml:11`); ~46k production LOC
(measured 47,391); ~40.7k test LOC across 174 files (measured 40,731 across 172 files — trivial
undercount, likely a file-naming-pattern edge case); exactly two runtime dependencies
(`z3-solver`, `networkx`, `pyproject.toml:28-31`).

## Decisions

- **Structural decomposition-by-pipeline-stage is correct and should be preserved.** The
  five-stage spine (`01-`) genuinely organizes the other 13 documents well, and no document
  should be merged, split, or reordered wholesale.
- **The tree needs one new document dedicated to operator semantics** (the truth-condition
  content named in A1), not a restructuring of `03-operators.md` in place — `03-` correctly
  covers the *abstraction* (base class, `DefinedOperator`, `OperatorCollection`, the three-register
  risk); a new document should carry the *content* (the actual formula, per operator, per
  theory family), analogous in form to `05-state-encoding.md`'s encoding table.
- **A worked end-to-end example is missing as a document class**, not just as a paragraph: no
  file traces one concrete example (e.g. `EXT_TH_1`/modus ponens or an `_CM_` countermodel case)
  through all five pipeline stages showing actual generated Z3-level constraints and, where
  applicable, an actual solved model's verifier/falsifier sets. This is the natural place to
  also pin down A6 (is output order canonical?).
- **A glossary is missing.** Terms load-bearing across multiple documents — state, world,
  possible, verifier, falsifier, fusion, part-of, evaluation point, main_point, frame
  constraint, alternative world, witness predicate, isomorphism — are each defined once,
  informally, in whichever document happens to need them first, with no single canonical
  definition site a porter can jump to.
- **The exclusion theory needs a real walkthrough**, matching the depth `11-theory-catalog.md`
  already gives the logos counterfactual operator (A3). This is theory-specific content, so it
  belongs in `11-` (expanded) or a new `11a-exclusion-witnesses.md` satellite, not folded into
  the general operator-semantics document.
- **No document should be cut wholesale.** Compression targets (B) are surgical: roughly a third
  of `13-`'s tail section and roughly a third of one `09-` subsection.

## Recommendations

Prioritized; P0 items are the actual port-blockers, P1 is high-value but not blocking, P2 is
compression/polish.

**P0 — do first, blocks a faithful port entirely:**
1. Write the operator truth-condition content (A1): for every primitive operator in all four
   theories, state `true_at`/`false_at`/`extended_verify`/`extended_falsify` as a formula in
   theory-agnostic mathematical notation, not Python. This is the single highest-leverage
   addition to the whole tree.
2. Document the helper predicates and the exact, exhaustive frame-constraint list (A2):
   `maximal`, `is_alternative`, `compatible`, `max_compatible_part`, plus the exact
   `z3.Function` signatures for `verify`/`falsify`/`possible` (and the analogous primitives for
   exclusion's `excludes` and imposition's ternary `imposition` relation).
3. Write a concrete specification of the exclusion witness-predicate mechanism (A3): what is
   Skolemized, why (the minimality-quantified negation clause it replaces), the exact function
   signatures (`h_pred, y_pred : BitVec(N) → BitVec(N)`, per-formula-keyed), and the constraints
   generated from them.

**P1 — high value, not fully blocking:**
4. Add a worked end-to-end trace document (one valid example, one countermodel example) showing
   actual constraints and, for the countermodel, actual verifier/falsifier output — doubles as
   the golden test a porter needs to validate their first working run.
5. Survey the error/exception taxonomy (A5) and map it explicitly onto the stated
   strict/absorb/warn policy; state N=0, empty-premises, and malformed-input behavior as an
   explicit case table.
6. State the determinism/ordering contract for verifier/falsifier sets and any other
   Python-set-typed data (A6) — is display order canonical or incidental?
7. Fix `08-iteration.md` to (a) cite `iterate/constraints.py:296-311` directly for defect #1
   rather than deferring the citation to `14-`, and (b) correct "blind to proposition valuations"
   to note the data is computed then discarded, not merely never computed (A4).

**P2 — compression and polish:**
8. Compress `13-examples-and-cli.md`'s project-generation/Jupyter/packaging tail by roughly two
   thirds (B); cut the entry-points paragraph.
9. Compress `09-output-and-display.md`'s stdout-identity-testing detail by roughly a third (B).
10. Add a short glossary document or section.
11. Fold in the smaller gaps from A7 (Result-tuple shape, ANSI→Markdown color table, registry API
    surface, settings validators) opportunistically while doing P0/P1 work, rather than as a
    separate pass.

## Risks & Mitigations

- **Risk**: writing full per-operator truth-condition tables (P0.1) is the single largest content
  addition and could balloon into Python transliteration if not disciplined to mathematical
  notation. **Mitigation**: use `05-state-encoding.md`'s existing table style as the template —
  it already demonstrates the right level of abstraction (`∃x ⊑ w. verify(x, p)`, not Python).
- **Risk**: the exclusion witness-predicate write-up (P0.3) requires enough domain literacy in
  unilateral truthmaker semantics to state the Skolemized condition correctly, not just describe
  the code. **Mitigation**: cross-check against the theory's own `docs/` (per the
  one-canonical-theory-layout contract in `10-theory-contract.md`) and, if available, the
  academic source the theory implements, before finalizing.
- **Risk**: a worked end-to-end example (P1.4) risks drifting stale the same way the tree warns
  prose documentation does generically. **Mitigation**: source it directly from an existing
  `unit_tests` entry (e.g. `EXT_TH_1`/`EXT_CM_1` in
  `theory_lib/logos/subtheories/extensional/examples.py`) so it stays anchored to the executable
  conformance suite `14-porting-notes.md` already names as authoritative.

## Appendix

- Verification sub-agent territories: docs 01–05 (pipeline/AST/operators/constraints/state
  encoding), docs 06–09 (solver/results/propositions/iteration/output), docs 10–14
  (theory-contract/catalog/settings/registry/CLI/porting-notes). Each independently confirmed
  file:line evidence for the findings above; this report synthesizes and re-verifies the
  highest-severity items directly.
- Primary source files consulted beyond those cited inline: `syntactic/operators.py`,
  `syntactic/collection.py`, `utils/parsing.py`, `models/constraints.py`, `models/semantic.py`,
  `utils/z3_helpers.py`, `solver/protocols.py`, `solver/registry.py`, `solver/z3_adapter.py`,
  `models/concurrency.py`, `utils/context.py`, `iterate/core.py`, `iterate/constraints.py`,
  `iterate/models.py`, `iterate/graph.py`, `output/manager.py`, `output/collectors.py`,
  `output/formatters/markdown.py`, `builder/module.py`, `builder/comparison.py`,
  `builder/example.py`, `theory_lib/logos/__init__.py`, `theory_lib/logos/operators.py`,
  `theory_lib/imposition/operators.py`, `registry.py`, `theory_lib/__init__.py`,
  `settings/settings.py`, `__main__.py`, `pyproject.toml`.
