# Implementation Summary: Task #220

- **Task**: 220 - Implement user-specifiable unicode characters for operators in theory operators.py files with infix or prefix form
- **Status**: [COMPLETED]
- **Started**: 2026-09-29T15:42:15Z
- **Completed**: 2026-09-29T17:55:00Z
- **Effort**: ~2.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_unicode-operator-aliases.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Added an optional `aliases: List[str]` class attribute to `syntactic.Operator`, registered
alongside the canonical LaTeX `name` by `OperatorCollection.add_operator`, so a theory's
`operators.py` can declare one or more user-facing Unicode glyphs (e.g. `aliases = ["∧"]` on the
class whose `name` is `"\\wedge"`) that parse to the same operator class. No parser changes were
needed or made. All seven shipped theory `operators.py` files now declare curated Unicode aliases
for their arity-1/arity-2 operators, alias collisions fail loudly via `DuplicateOperatorError`,
unregistered-operator lookups raise `UnknownOperatorError` with suggestions, and
`docs/usage/OPERATORS.md` documents the mechanism.

## What Changed

- `code/src/model_checker/syntactic/operators.py` — added `aliases: List[str] = []` class
  attribute to `Operator`, documented as read-only/never-mutated.
- `code/src/model_checker/syntactic/collection.py` — `add_operator` now registers each declared
  alias alongside `name`; added a conflict-aware duplicate policy (`_register_key`): re-adding the
  *same* class under a key it already owns is a silent no-op, a *different* class claiming that
  key raises `DuplicateOperatorError`; `__getitem__` now raises `UnknownOperatorError` (with an
  `available_operators` suggestion list) instead of a bare `KeyError`.
- `code/src/model_checker/syntactic/formulas.py` — `is_syntactically_wff`'s "atomic sentence
  letter" branch is now gated on `len(prefix) == 1`, with an explicit new branch accepting a
  non-backslash operator head applied to arguments as a connective. Zero change to which formulas
  are accepted or rejected; a characterization test suite pins the full before/after set.
- `code/src/model_checker/theory_lib/logos/operators.py` — `get_operator_by_name` now also
  catches `UnknownOperatorError` (in addition to the now-unreachable-via-this-path `KeyError`).
- Seven theory `operators.py` files (logos's extensional/modal/constitutive/counterfactual
  subtheories, exclusion, imposition, bimodal) — added `aliases = [...]` to arity-1/arity-2
  operators with a standard glyph; operators with no standard glyph (`\CFBox`/`\CFDiamond`,
  `\boxrightlogos`/`\diamondrightlogos`, `\Until`/`\Since`, the discrete
  `\future`/`\past`/`\next`/`\prev` duals) carry an inline `# No Unicode alias: ...` comment
  instead. `\top`/`\bot` (arity-0) are untouched, per the task's own "infix or prefix form" scope.
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` — added an
  explicit `aliases: List[str] = []` override on the shared `CandidateCounterfactual` base class
  (see Plan Deviations).
- `code/src/model_checker/theory_lib/imposition/operators.py`'s `LogosCounterfactual` — added an
  explicit `aliases = []` override for the same reason.
- New test files: `syntactic/tests/unit/test_collection.py`, `syntactic/tests/unit/test_formulas.py`,
  and a `test_unicode_aliases.py` in each of the seven theories' test directories.
- `code/src/model_checker/syntactic/tests/integration/test_collection.py` — updated
  `test_add_duplicate_operator` (split into a same-class no-op test and a different-class
  `DuplicateOperatorError` test) to match the new conflict-aware duplicate policy.
- `docs/usage/OPERATORS.md` — added a Unicode Alias column to the operator table, a new
  `## Unicode Aliases` section with a worked example and the two constraints (non-alphanumeric;
  `\top`/`\bot` excluded), reworked Best Practices item 6 and the Troubleshooting list.
- `code/docs/specific/FORMULAS.md`, `code/docs/core/DOCUMENTATION.md`,
  `code/docs/standards/documentation/DOCUMENTATION_STANDARDS.md`,
  `code/docs/implementation/ERROR_HANDLING.md`, `code/docs/core/CODE_STANDARDS.md` — fixed the
  same now-false "Unicode is never permitted in code" absolute claim, surfaced by a docs-tree
  grep.

## Decisions

- Duplicate policy is conflict-aware, not blanket-raise (plan Decision 1): required because
  `builder/serialize.py::deserialize_operators` re-adds the same class once per serialized
  dictionary key (once per name/alias).
- `is_syntactically_wff` was tightened by structure (gating on `len(prefix)`), not by adding a
  registry lookup — it remains pure and registry-free.
- Alias adoption in shipped theories is curated: only operators with a widely recognized,
  non-alphanumeric Unicode glyph got an alias.

## Plan Deviations

- **Discovered during Phase 4 (not a plan checklist item)**: loading logos's constitutive+modal
  subtheories (which transitively load counterfactual) raised `DuplicateOperatorError('□→ already
  registered')` at import time. Root cause: `counterfactual/candidates.py` defines six
  context-free candidate operator subclasses (`ImpositionLocalCounterfactual`,
  `WorldStateCounterfactual`, `SettlerCounterfactual`, `SettlingImpositionClosureCounterfactual`,
  `ExactSettlingImpositionCounterfactual`, `GeneratedSettlerCounterfactual`) that subclass
  `CounterfactualOperator` (via `CandidateCounterfactual`) without declaring their own `aliases`,
  so they inherited `CounterfactualOperator`'s `"□→"` alias via ordinary Python attribute
  inheritance and collided with it — and each other — the moment more than one was registered in
  the same collection. This file was outside the plan's originally-scoped seven theory
  `operators.py` files. Fixed with an explicit `aliases: List[str] = []` override on the shared
  `CandidateCounterfactual` base class. The identical pattern recurred in
  `theory_lib/imposition/operators.py`'s `LogosCounterfactual` (imports `CounterfactualOperator`
  as `LogosCounterfactualOperator` and subclasses it) and was fixed the same way.
- **Phase 2's Task 6** ("Move the existing guard so it runs after the None check"): implemented as
  a new `_register_key` helper (called once for `name`, once per alias) rather than reordering the
  original single-name guard in place — achieves the same after-None-check ordering while also
  serving Phase 1's multi-key alias registration need.
- **Phase 4's glyph enumeration task**: `\Until`/`\Since` were rejected per this task's own
  alphanumeric rule (their obvious candidate glyphs "U"/"S" are alphanumeric); the discrete
  `\future`/`\past`/`\next`/`\prev` duals and `\CFBox`/`\CFDiamond`/`\boxrightlogos`/
  `\diamondrightlogos` were left alias-free with an inline comment, none having a standard glyph
  distinct from an already-aliased sibling.
- **Phase 5's Unicode Aliases subsection**: landed as `## Unicode Aliases` (H2, matching the
  Table of Contents entry and the surrounding H2 rhythm) rather than nested as an H3 under
  `## Using Defined Operators`.
- **Phase 5's docs-tree grep**: fixed only the hits asserting the actually-false absolute claim
  ("NEVER permitted", "breaks parser"); the many other "LaTeX notation" mentions the grep pattern
  also matched remain true (LaTeX is still the required canonical/default spelling) and were left
  unchanged.

## Verification

- Build: N/A (Python, no build step)
- Tests: Passed — `PYTHONPATH=code/src pytest code/tests/ -q` (647 passed, 5 skipped, run
  multiple times across phases); `PYTHONPATH=code/src pytest code/src/model_checker/ -q` (2834
  passed, final run); `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -q` (1811
  passed); imposition and exclusion unit suites run explicitly (106 and 86 passed).
- Files verified: Yes — `git diff --stat` over the whole task confirms zero changes to
  `utils/parsing.py`, `syntactic/sentence.py`, `syntactic/syntax.py`, `jupyter/unicode.py`, or
  `builder/translation.py`, and no `examples.py` file was touched.

## Impacts

- Theory authors (in the shipped theories or their own generated projects) can now declare
  `aliases = [...]` on any `Operator` subclass to accept an additional user-facing spelling
  (typically Unicode) alongside the canonical LaTeX `name`, with no parser changes required.
- `OperatorCollection` lookups now raise `UnknownOperatorError` (with suggestions) instead of a
  bare `KeyError` on a missing key; any external code catching `KeyError` around an operator
  lookup would need updating (a repo-wide grep found and fixed the one such call site,
  `theory_lib/logos/operators.py`'s `get_operator_by_name`).
- Operator subclasses built from an already-aliased parent (a theory-local or experimental variant
  with its own distinct `name`) must now explicitly declare `aliases = []` to avoid silently
  inheriting — and colliding on — the parent's alias; this is now documented in
  `docs/usage/OPERATORS.md`'s Unicode Aliases section.

## Follow-ups

- None. The `\top`/`\bot` nullary constants remain unaliased (a declared non-goal); a follow-up
  task would need to touch the 8+ hardcoded string-literal call sites the research report
  identified.

## References

- `specs/220_unicode_operator_characters/reports/01_unicode-operator-characters.md`
- `specs/220_unicode_operator_characters/plans/01_unicode-operator-aliases.md`
- `docs/usage/OPERATORS.md`
