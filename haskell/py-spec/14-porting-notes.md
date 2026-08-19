# Porting Notes
[← Spec map](./README.md)

> The cross-cutting judgement layer: what semantics a port must preserve, what mechanism it
> should not reproduce, what is verified broken in the described implementation, and a standing
> warning about the reliability of the repository's own prose documentation. This is a hub
> document and links broadly.

## (a) Semantics to preserve

These are deliberate semantic choices, not implementation incidents — a port that drops any of
them changes what the system computes, not just how.

| Semantics | Where specified | Why it matters |
|---|---|---|
| Finite quantifier expansion over the state space, with its `(2^N)^k` cost model | [`05-state-encoding.md`](./05-state-encoding.md) | decidability and model-completion friendliness; not an optimization to revisit casually |
| Unknown-as-timeout: any inconclusive solver result is a timeout, never `unsat` | [`06-solver-and-results.md`](./06-solver-and-results.md) | soundness — the alternative would report invalid arguments as valid |
| The countermodel framing (premises true, conclusions false at the designated point) | [`04-constraint-generation.md`](./04-constraint-generation.md) | this *is* the query the pipeline answers; alternative queries must be expressed through it |
| The bit-vector mereology (fusion = OR, part-of = `s\|t==t`) and the full encoding table | [`05-state-encoding.md`](./05-state-encoding.md) | the entire semantic core of the state-mereology theory family |
| The settings-gated atomic-proposition constraint menu (contingent / non-empty / non-null / disjoint) | [`04-constraint-generation.md`](./04-constraint-generation.md), [`07-propositions.md`](./07-propositions.md) | the per-theory notion of "what counts as an atomic proposition" |
| The one-way core → theory dependency, with the theory registry as the sole source of theory identity | [`10-theory-contract.md`](./10-theory-contract.md) | keeps the core theory-agnostic and extensible without editing it |
| One canonical theory module set, executably enforced | [`10-theory-contract.md`](./10-theory-contract.md) | the real, verified contract — more reliable than any prose description of it, including this tree |
| Serialized model construction (one model built at a time) | [`06-solver-and-results.md`](./06-solver-and-results.md) | the underlying solver library is not safe for concurrent AST construction |
| Per-example solver isolation | [`06-solver-and-results.md`](./06-solver-and-results.md) | prevents learned-lemma leakage between unrelated examples |

## (b) Mechanism not to reproduce

These are Python-specific or historically-accreted workarounds, not semantics. Preserving the
*invariant* each one protects (noted in column three) matters; reproducing the *mechanism* does
not.

| Mechanism | Where specified | Invariant to preserve instead |
|---|---|---|
| A single mutable AST node whose field *types* change across four lifecycle phases | [`02-syntax-and-ast.md`](./02-syntax-and-ast.md) | model the four phases as four distinct types |
| Solving inside the model-structure constructor, plus a ten-field mutable result-state block | [`06-solver-and-results.md`](./06-solver-and-results.md) | separate `build : Constraints -> Problem` from `solve : Problem -> Result`; make `Result` a sum type |
| Capture-then-format output (redirect stdout, re-print, regex ANSI to Markdown) | [`09-output-and-display.md`](./09-output-and-display.md) | `model → typed result → renderer`, one canonical result datatype |
| Three independently hand-written operator registers per truth condition | [`03-operators.md`](./03-operators.md), [`11-theory-catalog.md`](./11-theory-catalog.md) | derive the concrete and display registers from the symbolic one |
| Three unrelated post-solve extraction method names for what is one concept | [`07-propositions.md`](./07-propositions.md) | one explicit "evaluation scheme" abstraction with named inhabitants |
| Import-path mutation and configuration-by-arbitrary-code-execution for example files | [`13-examples-and-cli.md`](./13-examples-and-cli.md) | a declarative example record (premises, conclusions, settings, expectation) with an explicit escape hatch for the rare case that needs more |
| Capability detection via `hasattr` on marker attributes (e.g. the generator-interface marker) | [`10-theory-contract.md`](./10-theory-contract.md) | an explicit, checked capability declaration instead of a silent degrade |
| Opt-in-only settings strictness, contradicting the project's own fail-fast principle | [`12-settings-and-registry.md`](./12-settings-and-registry.md) | make strictness the default |

## (c) Known defects in the described implementation

These are defects **in the Python system as described**, verified during the research this tree
is based on. They are recorded here for a port's awareness — not fixed by this document, and not
to be reproduced:

1. The model iterator's generic difference constraint iterates over the first `N` states rather
   than all `2^N` states of the state space, under-constraining the search and relying on the
   (expensive) isomorphism check to reject the duplicates this omission lets through — see
   [`iterate/constraints.py`](../../code/src/model_checker/iterate/constraints.py).
2. A solver handle kept alive past construction for the iterator's fallback path is the *wrong*
   one — a solver created before constraints were asserted, not the one that was actually
   checked — see [`models/structure.py`](../../code/src/model_checker/models/structure.py).
3. Every shipped theory's own difference-constraint and non-isomorphism-constraint hooks are
   dead code on the live iteration path, which calls a separate generic component instead — see
   [`iterate/core.py`](../../code/src/model_checker/iterate/core.py).
4. The Jupyter integration's validity check reads a settings key that nothing ever sets, so it
   silently degenerates to "was any model found" and reports validity inverted relative to the
   `expectation`-based check the CLI and test paths use — see
   [`builder/example.py`](../../code/src/model_checker/builder/example.py).

## (d) Dead code and documentation reliability

**Dead code**, named so a port does not treat its presence in the source tree as a design
recommendation: a fully scaffolded but hard-disabled sequential-per-model save subsystem
([`09-output-and-display.md`](./09-output-and-display.md)); multiple near-duplicate iteration
loops differing only in progress-reporting plumbing, with only one of them live
([`08-iteration.md`](./08-iteration.md)); an unused push/pop-based difference-search mechanism
that is structurally cleaner than the live accumulate-forever approach it was never wired to
replace; an unused model-injection module; and an aspirational protocol/enum vocabulary in the
iteration package with no implementing code anywhere.

**Documentation reliability — a standing warning.** The repository's own prose architecture
documentation is extensive and often conceptually right, but contains numerous specific,
verified-false claims about method signatures, constructor arguments, prefix-list shapes, and
setting names. Any future reader — including a reader of this tree, should it ever drift from the
source it was written against — should prefer, in order: (1) the four executable contracts named
below, (2) the source itself, (3) prose documentation, including this tree, treated as a
hypothesis to verify rather than a fact.

The four executable contracts, authoritative over any prose claim about the areas they cover:

- [`code/tests/test_layering.py`](../../code/tests/test_layering.py) — the core/theory dependency
  direction (see [`10-theory-contract.md`](./10-theory-contract.md))
- [`code/src/model_checker/theory_lib/tests/test_theory_conformance.py`](../../code/src/model_checker/theory_lib/tests/test_theory_conformance.py)
  — the required theory module set (see [`10-theory-contract.md`](./10-theory-contract.md))
- [`code/tests/cli/test_docs_flag_matrix.py`](../../code/tests/cli/test_docs_flag_matrix.py) — the
  CLI surface (see [`13-examples-and-cli.md`](./13-examples-and-cli.md))
- [`code/tests/packaging/`](../../code/tests/packaging/) — wheel/sdist contents (see
  [`13-examples-and-cli.md`](./13-examples-and-cli.md))

## Source files

- [`iterate/constraints.py`](../../code/src/model_checker/iterate/constraints.py),
  [`iterate/core.py`](../../code/src/model_checker/iterate/core.py) — defects 1 and 3; the dead
  duplicate iteration loops and the unused push/pop difference search
- [`models/structure.py`](../../code/src/model_checker/models/structure.py) — defect 2
- [`builder/example.py`](../../code/src/model_checker/builder/example.py) — defect 4
- [`output/manager.py`](../../code/src/model_checker/output/manager.py) — the disabled sequential
  save subsystem

## Related

This document links broadly, as a hub, to every other document in the tree — see the per-item
citations above rather than a separate list here.
