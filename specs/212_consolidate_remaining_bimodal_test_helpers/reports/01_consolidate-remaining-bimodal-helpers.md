# Research Report: Consolidate Remaining Bimodal Test Helpers

## Task

Consolidate the remaining bimodal test modules that define their own `_settings`/`_build`
helpers onto `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`. A prior task
(206) folded four byte-equivalent call sites onto the shared helper
(`test_certificate_a2_triangle.py`, `test_search_period_coverage.py`, `unit/test_structure.py`,
`unit/test_pinned_eval.py`); the rest were declared out of that task's scope.

## Method

- Re-ran the dispatch's own discovery command,
  `grep -rln '^def _settings\|^def _build' code/src/model_checker/theory_lib/bimodal/tests/`
  (excluding `_build_support.py`), immediately before starting. It reproduced the same ten
  modules named in the dispatch.
- Read `_build_support.py` in full (`_settings`, `_build`, and its own docstring, which already
  documents the `test_structure.py` exception).
- Read every one of the ten modules' full `_settings`/`_build`-matching function bodies via a
  small AST-based extraction script, then read full file context (imports, other call sites,
  other uses of the constituent symbols) for every module whose body was not an obvious verbatim
  match, to establish genuine equivalence rather than assuming the shared name implies a shared
  shape (per the dispatch's explicit instruction).
- Confirmed a baseline: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q` collects cleanly (686 tests, no import errors) before any change.

## Finding: the ten-module list contains three distinct categories, not one

Reading each helper against `_build_support.py`'s own shape (rather than trusting the `_build`/
`_settings` names) splits the ten modules the dispatch names into three groups:

### Group A — full duplicates of both `_settings` and `_build`: consolidate to a bare import (2 modules)

| Module | `_settings` | `_build` | Notes |
|---|---|---|---|
| `integration/test_data_extraction.py` | verbatim duplicate | verbatim duplicate of the shared pipeline, no `'verify'` override | No test in this module inspects verification output/labels — it reads `structure.certificate`, `extract_states()`, etc., which are unaffected by `'verify'`'s value. Safe to drop to a bare `_build_support` import. |
| `integration/test_output_gate.py` | verbatim duplicate | verbatim duplicate of the shared pipeline (docstring claims to match `test_structure.py`'s wrapper, but the body has **no** `'verify'` default — the docstring is stale/misleading, not the code) | Confirmed every one of this module's 8 `_build(...)` call sites passes `verify=` explicitly (`"auto"`, `"off"`, `"required"`, `"paranoid"`) — the module's whole purpose is exercising the three `'verify'` values, so it never relies on `_build_support`'s `'auto'` default. Safe to drop to a bare `_build_support` import despite the misleading docstring. |

Both modules' local `_settings`/`_build` are followed immediately by unused-import fallout: once
the local defs are replaced by an import, `ModelConstraints`, `Syntax`, `bimodal_operators`,
`BimodalStructure`, `BimodalProposition`, and (for these two modules specifically) `BimodalSemantics`
itself become unused — in both files, `BimodalSemantics` is referenced **only** inside the local
`_settings`/`_build` bodies being removed (confirmed by grep: exactly 3 occurrences each, all
inside the doomed functions or their own import line). All six imports must be deleted alongside
the function bodies, not just the two function defs, or the module will fail a lint/vulture pass
on dead imports.

### Group B — `_settings`-only duplicates, no local `_build` (5 modules)

| Module | `_settings` shape | Other pipeline helper present? |
|---|---|---|
| `integration/test_iterate.py` | verbatim duplicate | `_mock_build_example` and `_real_build_example` — **not** duplicates; see "Non-candidates" below |
| `integration/test_until_since_integration.py` | verbatim duplicate | `_run` builds an `[premises, conclusions, settings]` triple for the `run_test()` API, not the `Syntax -> ModelConstraints -> BimodalStructure` pipeline — a different, unrelated helper, not a `_build` duplicate |
| `unit/test_operators.py` | verbatim duplicate | none |
| `unit/test_proposition.py` | verbatim duplicate | none |
| `unit/test_semantics_core.py` | verbatim duplicate | none |

All five call `BimodalSemantics(_settings())` directly (never the full `Syntax`/`ModelConstraints`/
`BimodalStructure` pipeline), and all five reference `BimodalSemantics` elsewhere in the file
body too (not just inside `_settings`), so — unlike Group A — `BimodalSemantics`'s own import
stays needed after consolidation; only the local `_settings` def is removable, replaced by
`from model_checker.theory_lib.bimodal.tests._build_support import _settings`.

### Group C — same-shape pipeline, different local name: needs a call-site decision (1 module)

`integration/test_injection.py` defines `_settings` (verbatim duplicate) plus `_build_solved`
(not `_build` — the grep matched it only because `^def _build` is a prefix match against
`def _build_solved(...)`). Reading `_build_solved`'s body shows it is behaviorally identical to
`_build_support._build` — same three-line pipeline, same no-`'verify'`-override shape, just
under a different local name used at 3 call sites in the module. This is genuine duplication, not
a documented behavioral difference like `test_structure.py`'s wrapper, so per the dispatch's own
rule ("keep a documented local wrapper... rather than either forcing the module onto the shared
form or leaving a full duplicate" — reserved for a *real* difference) this should not become a
`test_structure.py`-style wrapper. Two ways to close it, for the planner to pick between:

- **(a) Rename call sites** — `from ...tests._build_support import _build`, and change all 3
  `_build_solved(...)` call sites to `_build(...)`. Matches the naming convention every other
  already-migrated call site uses; slightly larger diff.
- **(b) Import-alias, no call-site renames** — `from ...tests._build_support import _build as
  _build_solved`. Zero call-site diff, but leaves a locally-meaningful name whose docstring no
  longer applies (nothing left to document).

(a) is the closer match to the pattern already established by the four modules task 206
migrated (all of which import the name `_build` directly); this report recommends (a), but
either closes the duplication.

`BimodalSemantics` stays imported in this module regardless of which option is taken — it is
used directly at a fourth call site (`semantics = BimodalSemantics(_settings())`) outside the
removed function, unlike the two Group A modules.

## Non-candidates found among the ten dispatch-named modules

Two of the ten modules the grep command names are **not** duplicates of `_build_support`'s
`_settings`/`_build` at all, despite matching the discovery regex:

- **`unit/test_structure.py`** — the dispatch itself already excludes this one: its local
  `_build` is the deliberate, documented four-line wrapper defaulting `'verify'` to `'off'`
  (output-gate determinism fix), delegating to the shared `_build`. Leave unedited, as instructed.
- **`unit/test_witness_constraints.py`** — a **grep false positive**, not a second undocumented
  exception. This module defines no `_settings` at all, and its only `^def _build`-prefixed
  function is `_build_selector_family(nb, nm, nf, pattern)`, which builds a `WitnessFamily`/
  `LabelledLasso` test double for constraint-generator unit tests — it never touches
  `BimodalSemantics`, `Syntax`, `ModelConstraints`, or `BimodalStructure`, and shares nothing
  with `_build_support.py`'s shape. It matched the grep only because `_build_selector_family`
  starts with the literal substring `def _build`. There is nothing here to consolidate, and no
  wrapper is warranted — the module is simply out of scope, confirmed by reading rather than by
  the name match.

`integration/test_iterate.py`'s `_mock_build_example`/`_real_build_example` are a related but
narrower instance of the same false-positive risk: they matched the original discovery list only
via that file's *`_settings`* definition (which genuinely is a duplicate, see Group B above) —
neither `_mock_build_example` nor `_real_build_example` themselves matches the `^def _build`
grep pattern (they start with `def _mock_build_example`/`def _real_build_example`, not
`def _build`). They are Mock/`BuildExample`-based iterator test doubles, unrelated to
`_build_support`'s real-pipeline `_build`, and must not be touched.

## Net scope after equivalence-checking

| Module | Action |
|---|---|
| `integration/test_data_extraction.py` | Replace local `_settings`+`_build` with a `_build_support` import; drop the six now-unused imports |
| `integration/test_output_gate.py` | Replace local `_settings`+`_build` with a `_build_support` import; drop the six now-unused imports |
| `integration/test_injection.py` | Replace local `_settings` with a `_build_support` import; replace local `_build_solved` with imported `_build` (recommend renaming the 3 call sites; import-alias is an acceptable fallback) — `BimodalSemantics` import stays |
| `integration/test_iterate.py` | Replace local `_settings` with a `_build_support` import only — leave `_mock_build_example`/`_real_build_example` untouched |
| `integration/test_until_since_integration.py` | Replace local `_settings` with a `_build_support` import only — leave `_run` untouched |
| `unit/test_operators.py` | Replace local `_settings` with a `_build_support` import |
| `unit/test_proposition.py` | Replace local `_settings` with a `_build_support` import |
| `unit/test_semantics_core.py` | Replace local `_settings` with a `_build_support` import |
| `unit/test_structure.py` | **No change** — dispatch-excluded, documented wrapper stays |
| `unit/test_witness_constraints.py` | **No change** — grep false positive, no shared shape exists to consolidate |

Eight modules carry a genuine consolidation; two of the ten named modules turn out, on direct
read, to carry nothing consolidatable.

## Verification guidance for the implementation phase

The dispatch requires verifying with the full four-theory gate rather than the bimodal subset
(i.e. `PYTHONPATH=code/src pytest code/tests/ -v` or equivalent project-wide invocation covering
logos/exclusion/imposition/bimodal together), not merely the bimodal directory — consolidating
imports is low-risk but touches import surfaces shared with other theories only incidentally (it
does not), so the four-theory run is primarily a regression backstop per project standards
(`code/docs/core/TESTING_GUIDE.md`) rather than because cross-theory coupling is expected here.
A `--collect-only` pass across `code/src/model_checker/theory_lib/bimodal/tests/` already
confirms 686 tests collect cleanly pre-change (baseline recorded above); the same command should
be re-run post-change before the full gate, to catch an import-order/unused-import mistake
cheaply.

## Prior-task context

`specs/206_refactor_verification_test_harness/plans/01_refactor-verification-test-harness.md`
Phase 2 is the task that introduced `_build_support.py` and consolidated the first four
byte-equivalent call sites; its own scoping note (F2) explicitly declined to touch grid-table
duplication elsewhere in the same tree, establishing the precedent this task continues under a
narrower, purely-`_settings`/`_build` mandate.
