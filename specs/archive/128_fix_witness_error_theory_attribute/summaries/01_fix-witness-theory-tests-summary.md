# Implementation Summary: Fix Witness Error `.theory` Contract Tests

- **Task**: 128 - Resolve the contradiction between the witness error classes and their tests
- **Plan**: specs/128_fix_witness_error_theory_attribute/plans/01_fix-witness-theory-tests.md
- **Status**: Complete — all 3 phases executed, primary verification command green

## Outcome

`test_witness_registry_error_basic` and `test_witness_constraint_error_basic` in
`code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` were failing because they
constructed `WitnessRegistryError` / `WitnessConstraintError` without a `theory=` kwarg and then
asserted `.theory == "exclusion"`, but neither class (nor any class in the witness error
hierarchy) sets a class-level `theory` default — so `.theory` was `None`.

The fix was applied entirely in the test file, per the plan's non-goal on `errors.py`:

- Both tests now construct their error with an explicit `theory="exclusion"` kwarg, matching the
  pattern already used by the sibling `test_witness_error_construction` and
  `test_semantic_error_with_imposition_theory` tests in the same file.
- Both test docstrings, and the `TestWitnessErrorHandling` class docstring, now record why no
  class-level `theory` default exists: the witness error hierarchy is shared by the exclusion
  theory (`exclusion/semantic/registry.py`, `constraints.py`, `core.py`) and the bimodal theory
  (`bimodal/semantic/witness_registry.py`, `witness_constraints.py`). A hardcoded
  `theory="exclusion"` class default would mislabel every error raised from bimodal's witness
  modules. Callers that know their theory pass it explicitly via the `theory=` keyword; no
  raise site in either theory currently does so, and threading a theory identifier through the
  five production raise sites remains an available future improvement, deliberately out of scope
  here.

## Contract Decision

The witness error hierarchy (`WitnessError` and its subclasses `WitnessNotFoundError`,
`WitnessRegistryError`, `WitnessConstraintError`, `WitnessPredicateError`) stays theory-agnostic
by design. The stale contract lived in the tests, not in `errors.py`, and `errors.py` was
confirmed unmodified throughout (`git diff -- code/src/model_checker/theory_lib/errors.py` is
empty).

## Verification

Phase 1 (RED baseline, pre-edit):
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v
-> 2 failed, 10 passed in 0.57s
   Both failures: AssertionError: assert None == 'exclusion'
   (test_witness_registry_error_basic, test_witness_constraint_error_basic)
```

Audit gate: grepped the full `code/` tree for `.theory`/`assertEqual` assertions and all
witness-error-class usages. The only assertions on a witness error's `.theory` are the seven
lines in `test_error_handling.py` (39, 66, 80, 86, 99, 136, 155); no other file in the repo
depends on witness `.theory` being `None` or `"exclusion"`. `WitnessSemanticError` does not
exist anywhere in the codebase.

Pre-edit baseline for dependent suites:
```
PYTHONPATH=code/src pytest \
  code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py \
  code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py \
  code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -q
-> 47 passed in 0.78s
```

Phase 2 (GREEN, post-edit):
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v
-> 12 passed in 0.49s
```

Phase 3 (regression, post-edit):
```
PYTHONPATH=code/src pytest \
  code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py \
  code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py \
  code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -q
-> 47 passed in 0.64s   (matches Phase 1 baseline, no regressions)

PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/ -q
-> 12 passed in 0.49s

PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v
-> 12 passed in 0.45s   (final confirmation)
```

`git diff --stat -- code/src/model_checker/theory_lib/` lists exactly one changed file:
`tests/unit/test_error_handling.py` (26 insertions, 5 deletions). `errors.py` carries no changes.

`grep -niE "task [0-9]+" code/src/model_checker/theory_lib/tests/unit/test_error_handling.py`
returns one pre-existing match (line 28, referencing a prior refactor, unrelated to and
predating this diff); no new task-number citations were introduced.

## Files Modified

- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` — two test constructions
  updated to pass `theory="exclusion"` explicitly; three docstrings (both tests plus the
  `TestWitnessErrorHandling` class) expanded to record the shared-class rationale.

## Plan Deviations

- None (implementation followed plan)
