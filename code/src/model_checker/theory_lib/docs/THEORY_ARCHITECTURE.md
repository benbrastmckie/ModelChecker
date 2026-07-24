# Theory Architecture in ModelChecker

This document defines the single canonical module set that every theory in `theory_lib/` must
implement, plus the optionality policy and the three-layer dependency model that keeps
`theory_lib` and the core packages cleanly separated. For usage-oriented guidance, see
[README.md](README.md) and [USAGE_GUIDE.md](USAGE_GUIDE.md).

There is one pattern, not two. Every theory shares the same required file set; logos additionally
carries a `subtheories/` layer because its operator set is large enough to benefit from
categorical organization, not because it follows a different architecture.

## Required Theory File Set

Every entry under `theory_lib/` (e.g. `bimodal/`, `exclusion/`, `imposition/`, `logos/`) MUST
provide:

- **`__init__.py`** — the theory's public API. Exposes `get_theory(config=None)`, returning a
  dict with `semantics`, `proposition`, `model`, and `operators` keys.
- **`semantic/`** — a package, not a module (a directory containing `__init__.py`). Required
  members:
  - `__init__.py` — re-export-only; it imports and re-exports the theory's semantics,
    proposition, and model classes from the modules below, and defines no class bodies of its
    own.
  - `core.py` — the core semantic framework (the `SemanticDefaults` subclass and its primitives).
  - `model.py` — the model structure class (the `ModelDefaults` subclass).
  - additional theory-specific modules as needed (for example, imposition's `helpers.py` or
    exclusion's `constraints.py` and `registry.py`).
- **`operators.py`** — the theory's operator collection (or, for logos, the registry that loads
  operators from `subtheories/`).
- **`iterate.py`** — **required for every theory**, not optional. Every theory's
  `DEFAULT_EXAMPLE_SETTINGS` declares an `iterate` setting, so a theory lacking `iterate.py` has a
  live, reachable `ImportError` the moment a user sets `iterate: 2` on an example. Must expose:
  - `{Theory}ModelIterator` — the iterator class.
  - `iterate_example` — the eager iteration entry point.
  - `iterate_example_generator` — the generator-interface entry point, wrapped so that
    `iterate_example_generator.__wrapped__.returns_generator` is truthy. The builder's runner
    layer selects between the two entry points and detects the generator interface via
    `hasattr(fn, '__wrapped__') and hasattr(fn.__wrapped__, 'returns_generator')` — theories that
    omit the marker silently fall back to the eager path.
- **`examples.py`** — see "Required `examples.py` Attributes" below.
- **`tests/`** — `__init__.py`, `conftest.py`, `unit/`, `integration/`, `README.md`.
- **`docs/`** — the six-file set: `README.md`, `API_REFERENCE.md`, `ARCHITECTURE.md`,
  `ITERATE.md`, `SETTINGS.md`, `USER_GUIDE.md`.
- **`README.md`**, **`CITATION.md`**, **`LICENSE.md`**, **`VERSION`** — theory-level metadata,
  documentation entry point, and citation/licensing files.

## Required `examples.py` Attributes

`examples.py` MUST define each of the following exactly once (a plain `hasattr` check cannot
detect a duplicate assignment where the second overwrites the first without either raising or
being visibly wrong):

- `example_range` — the full dict of named examples.
- `test_example_range` — the subset (often identical to `example_range`) exercised by the test
  suite.
- `semantic_theories` — the dict describing this theory's semantic configuration(s), keyed by
  display name, each value shaped like the `get_theory()` return dict.
- `unit_tests` — the dict of examples used for unit-level testing.

## Optional Elements

- **`notebooks/`** — optional, and reported but not enforced by the conformance test. Some
  theories (exclusion, imposition) ship Jupyter demonstrations; others (bimodal, logos) do not.
  Absence is not a defect.

## Subtheory File Set (logos)

Semantics stays centralized in `logos/semantic/`; subtheories never define their own semantics.
Each entry under `logos/subtheories/` MUST provide:

- `__init__.py`
- `operators.py` — MUST return a **non-empty** dict from `get_operators()`. A subtheory
  contributing zero operators is a defect, not a valid configuration: it means the subtheory has
  no independent content and its operators (if any exist) belong to another subtheory it silently
  depends on.
- `examples.py`
- `tests/`
- `README.md`

## End-to-End Testing

`e2e/` is **not** part of the per-theory test set. End-to-end coverage exercises the CLI and
project-generation pipeline, not theory semantics, and lives at core level
(`code/tests/e2e/`, `builder/tests/e2e/`, `iterate/tests/e2e/`), parametrized over all four
theories. No theory directory should carry its own `tests/e2e/`.

## Layering

The codebase is organized into three layers with a strictly enforced dependency direction:

1. **Core** — `models`, `syntactic`, `solver`, `utils`, `iterate`, `builder`, `settings`,
   `output`, `z3_shim`. Core modules MUST NOT import `theory_lib`, whether via a static
   `import`/`from … import` statement, a function-local import, or a string-literal reference
   passed to `importlib.import_module`. Core modules MUST NOT hardcode any theory name
   (`bimodal`, `exclusion`, `imposition`, `logos`) as a string literal; theory identity is
   obtained by querying the theory registry, never by naming a theory directly.
2. **`theory_lib`** — may import core freely. May never be imported by core.
3. **Upper layer** — `model_checker/__init__.py`, `model_checker/api.py`, `__main__.py`,
   `jupyter/`. May import both core and `theory_lib`; this is where "needs to know about all
   theories" logic legitimately lives.

This boundary is enforced by an executable layering test (`code/tests/test_layering.py`), not
just documented here — the test is the authoritative check; this document is the contract it
encodes.

## Conformance Test

The required/optional file set and `examples.py` attribute rules above are the specification that
`code/src/model_checker/theory_lib/tests/test_theory_conformance.py` encodes as a parametrized
test over the theory registry (see `registry.py` in the core layer). A theory is conformant when
that test passes for it with zero `xfail` markers.
