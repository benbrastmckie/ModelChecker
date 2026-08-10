# Implementation Summary: Task #126 (Phases 10-17, Waves 4-6)

**Completed**: 2026-07-25
**Scope**: Phases 10 through 17 (waves [10,11], [12,13,14], [15,16,17]) of the 26-phase
core/theory_lib refactor plan, resumed from a continuation handoff after phases 1-9 (waves 1-3)
completed in a prior dispatch. This summary supersedes nothing; it extends
`02_phases-1-9-summary.md`.

## Overview

Completed all 8 phases of waves 4-6: introduced the single-source core theory registry with
lazy resolution (Phase 10); fixed the bimodal `test_example_range` gap and unified all four
theories' `get_theory()` signatures (Phase 11); moved theory-aware helpers out of `utils/` into
a new upper-layer `model_checker/api.py` (Phase 12); rederived `builder/`'s theory identity
entirely from the registry, fixing a live drift bug where three of four theories silently fell
through to a name-based fallback (Phase 13); normalized imposition onto the canonical contract,
establishing the normalization template (Phase 14); fully reclassified `jupyter/` and eliminated
every hardcoded theory-name literal in the package, including two mechanisms not explicitly
named in the plan — a structural adapter-class-name-derivation scheme and a registry-driven
default-theory concept (Phase 15); relocated `builder/z3_utils.py` into `iterate/` as the
iteration-domain primitive it actually is (Phase 16); and split exclusion's 600-line
`semantic/__init__.py` into `core.py`/`model.py`/`proposition.py`, establishing the
`proposition.py` naming convention Phase 18 will reuse for logos (Phase 17).

**The core/theory_lib layering test (`code/tests/test_layering.py`) is now fully GREEN**: both
RED-baseline assertions established in Phase 9 (zero core-to-theory_lib string/import
dependencies, zero hardcoded theory-name literals across core+upper) now pass with zero
violations, repo-wide — not just within the phases' individually-scoped subsets.

## What Changed

- `code/src/model_checker/registry.py` — new. Single-source theory registry:
  `register_theory()`/`get_registered()`/`get_theory_entry()`/`iter_theories()` plus
  `set_adapter()`/`set_default_theory()`/`get_default_theory()` (the latter three added in
  Phase 15, not originally scoped to Phase 10). Contains zero theory-name literals.
- `code/src/model_checker/theory_lib/__init__.py` — registers all four theories into the
  registry at import time via lazy, cached component loaders; `AVAILABLE_THEORIES` is now a
  view over the registry; `discover_theories()` reframed as a dev lint with a new
  `check_registry_drift()` companion; marks `'logos'` as the default theory.
- `code/src/model_checker/__init__.py` — bootstraps registration via `from . import theory_lib`;
  `get_theory` now sourced from the new `.api` module.
- `code/src/model_checker/api.py` — new upper-layer module: theory-aware `get_theory()`,
  `get_semantic_theories()`, `get_available_theories()`.
- `code/src/model_checker/utils/api.py`, `utils/version.py` — stripped of all theory_lib
  awareness; `get_theory_version()`/`check_theory_compatibility()` moved to
  `theory_lib/meta_data.py`.
- `code/src/model_checker/builder/loader.py`, `strategies.py`, `runner.py`, `project.py` —
  theory identity (both the `prop_to_theory`/`theory_patterns` drift-bug dicts and the
  `_is_theory_lib_file()` path sniff) now entirely registry-derived; zero theory_lib
  string/import references and zero theory-name literals remain in `builder/`.
- `code/src/model_checker/jupyter/adapters.py`, `interactive.py`, `display.py`,
  `environment.py`, `utils.py`, `unicode.py` — every hardcoded theory-name literal removed;
  adapter selection derives theory identity from adapter-class-name convention
  (`"{Name}TheoryAdapter"`), not a dict literal; theory resolution and defaults are
  registry-driven; `unicode.py`'s exclusion-specific glyph table moved to
  `theory_lib/exclusion/__init__.py` as `UNICODE_OPERATOR_EXTENSIONS`, discovered generically.
- `code/src/model_checker/theory_lib/bimodal/examples.py` — added `test_example_range`.
- `code/src/model_checker/theory_lib/logos/examples.py`, `logos/__init__.py` — removed the
  duplicate `example_range` assignment; `get_theory()` signature unified to
  `get_theory(config=None, *, subtheories=None)`.
- ~24 files across `code/` and `docs/` — every `get_theory([...])` call site for logos updated
  to `get_theory(subtheories=[...])` for the new keyword-only parameter.
- `code/src/model_checker/theory_lib/imposition/tests/conftest.py` — new.
- `code/src/model_checker/builder/z3_utils.py` → `iterate/z3_utils.py` (git mv); its test moved
  alongside it; `builder/example.py`'s dead import block removed.
- `code/src/model_checker/theory_lib/exclusion/semantic/{__init__,model,proposition}.py` —
  `__init__.py` reduced from 600 to 27 lines (pure re-exports); `WitnessModelAdapter` and
  `WitnessStructure` moved into `model.py`; `WitnessProposition` moved into a new
  `proposition.py`.
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` — repointed to
  `registry.get_registered()`; four xfail-reason dicts emptied (bimodal
  `test_example_range`/`get_test_examples`, logos duplicate `example_range`, logos
  `get_theory()` signature); the signature-uniformity test rewritten to allow logos's
  documented keyword-only `subtheories` exception.
- `code/tests/test_layering.py` — `registry.py` and `api.py` added to the core/upper file
  inventories.
- `code/tests/unit/test_registry.py` — new, 7 tests (registration/duplicate/unknown-name/lazy
  caching/iteration order/bootstrap sanity).
- `code/src/model_checker/builder/tests/unit/test_loader.py` — new
  `TestDiscoverTheoryModuleRegression`, exercising all four theories' real `get_theory()` dicts.
- Documentation: `THEORY_ARCHITECTURE.md`-adjacent READMEs, per-theory docs, and
  `iterate`/`builder` test READMEs updated where paths or signatures changed.

## Decisions

- **Adapter attachment is post-hoc, not registration-time**: `theory_lib`'s `register_theory()`
  calls always pass `adapter=None`; `jupyter/adapters.py` calls the new `registry.set_adapter()`
  on its own, after both sides exist. Passing jupyter-specific adapter classes directly from
  `theory_lib/__init__.py` would require `theory_lib` to import `jupyter` (upper layer),
  inverting the sanctioned one-way dependency direction.
- **Theory-name-to-class association is derived structurally, never hardcoded**: jupyter's
  adapter registration strips the `"TheoryAdapter"` suffix from each adapter class's own
  `__name__` and lowercases it, rather than writing a `{name: class}` dict literal. The same
  principle drives `jupyter/unicode.py`'s glyph-table discovery (via
  `getattr(theory_module, 'UNICODE_OPERATOR_EXTENSIONS', None)`) instead of a
  `{theory_name: {...}}` dict.
- **A registry-driven "default theory" concept was added (Phase 15, not originally scoped)**:
  several jupyter functions hardcoded `theory_name="logos"` as both a parameter default and an
  unsupported-name fallback — themselves flagged literals. `registry.set_default_theory()` /
  `get_default_theory()` let `theory_lib` (the one place literals are permitted) mark `'logos'`
  as default once, with every other call site querying the registry instead of repeating the
  literal.
- **Lazy component resolution shares one cache per theory, not one per component**: each
  theory's four registry components (semantics/proposition/model/operators) share a single
  `cache` dict closure, so `get_theory()` is invoked at most once per theory regardless of how
  many of the four properties are read.
- **`_register_theories()` is idempotent, not fail-fast, for its own re-execution**: observed
  under pytest's `--import-mode=importlib` re-executing `theory_lib/__init__.py`'s top-level
  code against an already-populated registry module instance during isolated single-file test
  collection. `registry.register_theory()` itself remains strict for every other caller.
- **`builder/strategies.py:290`'s violation was prose, not logic**: `TheoryLibImportStrategy`'s
  path-to-module-name conversion is generic (keys off `'model_checker'`, not
  theory_lib-specific); only its error message contained the flagged literal, so it was
  reworded rather than routed through the registry.
- **Exclusion's proposition class got its own `proposition.py`**, matching what Phase 18 will
  introduce for logos, rather than folding it into `model.py` — establishes one consistent
  three-file (`core`/`model`/`proposition`) convention across the theories still to be
  normalized.

## Plan Deviations

- **Phase 11**: an initial bulk `get_theory([` → `get_theory(subtheories=[` substitution
  over-matched 5 `builder/tests/` fixture files that call **bimodal's** `get_theory(config=None)`
  with a harmless unused positional placeholder — reverted after the builder suite regressed
  from 249/6-known-failures to 222/38-failures, then re-verified back to baseline.
- **Phase 11**: the conformance test's `test_get_theory_uses_uniform_config_parameter` rewritten
  (not simply un-xfailed) to accept logos's documented keyword-only `subtheories` exception
  instead of requiring `params == ['config']` exactly.
- **Phase 12**: `model_checker/api.py` added to the layering test's `UPPER_LAYER_SINGLE_FILES` —
  the file's own module docstring had already named it as the eventual home in advance.
- **Phase 13**: fixed `builder/project.py:99`'s hardcoded `theory: str = 'bimodal'` default
  (not named in the phase's task list, but required by its own "zero violations under builder/"
  verification bullet) and added a module-level `_resolve_theory_lib_root()` helper (not a
  `ModuleLoader` method) after discovering a structural test asserts `ModuleLoader` has `<=7`
  methods.
- **Phase 15**: fixed `jupyter/unicode.py:278`'s hardcoded exclusion glyph table and added the
  registry default-theory mechanism — both flagged by Phase 9's audit or required by Phase 15's
  "no theory-name string literals remain anywhere in jupyter/" verification, neither named in
  the phase's task list.
- **Phase 16**: updated three stale `z3_utils.py` doc references the phase's own
  `grep -rn "z3_utils" builder/` verification bullet required be cleared.
- **Phase 17**: fixed a `core.py` <-> `model.py` circular import (discovered via the first
  post-move smoke test, not anticipated by the plan) by making `model.py`'s `WitnessSemantics`
  import function-local; dropped four already-dead imports from `semantic/__init__.py`.

None of these deviations altered scope beyond what each phase's own verification bullets
already required, or reversed an unintended side effect of a mechanical bulk edit.

## Verification

- `bash code/scripts/verify-refactor.sh --skip-oracle` passes cleanly as of the final commit:
  289 bimodal collected/passed, 2162 full in-package collected (2100 baseline + 62 new tests
  from Phases 8-9 and this dispatch's `test_registry.py`/`TestDiscoverTheoryModuleRegression`),
  550 oracle collected, xfail lines unchanged, 0 baseline regressions.
- `code/tests/test_layering.py`: **4 passed, 0 failed** — both RED-baseline assertions from
  Phase 9 are now fully GREEN, zero violations of either kind, repo-wide.
- `theory_lib/tests/test_theory_conformance.py`: 45 passed, 5 xfailed (down from 41/9 at the
  Phase 9 baseline — imposition, bimodal's examples-contract gaps, and logos's signature/
  duplicate-assignment gaps are now green; the 5 remaining xfails are bimodal's semantic-package
  form and missing `iterate.py` (2 assertions each) and relevance's empty operators, all
  scoped to later phases).
- `code/tests/unit/test_registry.py`: 7 passed.
- `builder/tests/`: 249 passed, 6 pre-existing failures (verified against the documented
  baseline list — identical test names, all pre-existing timing/known issues untouched by this
  dispatch).
- `theory_lib/exclusion/tests/`: 143 passed. `theory_lib/imposition/tests/`: 110 passed (253
  combined, matching the Phase 1-9 baseline). `theory_lib/logos/tests/`: 323 passed.
  `theory_lib/bimodal/tests/`: 289 passed. `jupyter/tests/`: 72 passed.
- `builder/tests/unit/test_serialize.py`: 17 passed, 1 pre-existing failure (unrelated to
  exclusion; same documented bimodal-pickling-module baseline failure).
- Files verified: Yes.

## Notes

- **Phase 2 is still PARTIAL, not COMPLETED** (carried forward, untouched this dispatch): the
  full serial oracle suite run remains unattempted since the Phase 1-9 dispatch — this dispatch
  did not run the oracle suite either (per the orchestrator's explicit instruction not to spend
  this dispatch re-running it). Collection count (550) and xfail line locations remain pinned
  and verified clean.
- Phases 18-26 are explicitly out of scope for this dispatch and were not started. Phase 18
  (splitting logos's 1283-line `semantic.py`, the most widely-imported module in the tree,
  including from other theories) is the next wave-7 phase and is a materially larger,
  higher-risk unit of work than any phase completed in this dispatch — flagged for the next
  dispatch to begin fresh rather than starting it with reduced context budget remaining.
- The core/theory_lib layering test reaching fully GREEN two waves ahead of Phase 23 (which was
  planned as the phase that flips it green) is expected and correct: Phase 23's job is to also
  strip the *conformance* test's remaining xfails and add the zero-xfail guard assertion, not to
  be the first point the layering test passes. Nothing needs to be redone.
