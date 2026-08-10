# Research: Witness Error `.theory` Attribute Contract

## Problem

`code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` has two failing tests:

```python
def test_witness_registry_error_basic(self):
    """Test basic WitnessRegistryError."""
    error = WitnessRegistryError("Registry operation failed")
    assert error.theory == "exclusion"          # FAILS: error.theory is None

def test_witness_constraint_error_basic(self):
    """Test basic WitnessConstraintError."""
    error = WitnessConstraintError("Constraint generation failed")
    assert error.theory == "exclusion"          # FAILS: error.theory is None
```

Reproduced with `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v`:
2 failed, 10 passed — both failures are `AssertionError: assert None == 'exclusion'`.

## Current hierarchy (`code/src/model_checker/theory_lib/errors.py:163-194`)

```python
class WitnessError(TheoryError):
    """Base for witness errors."""
    pass

class WitnessNotFoundError(WitnessError): pass
class WitnessRegistryError(WitnessError): pass
class WitnessConstraintError(WitnessError): pass
class WitnessPredicateError(WitnessError):
    def __init__(self, predicate_name, operation, **kwargs): ...
```

None of the witness classes sets a `theory` default. `TheoryError.__init__` (`errors.py:29-43`) defaults `theory=None` unless a caller passes it explicitly. No sibling error class in the file
(`TheoryLoadError`, `SemanticError`, `OperatorError`, `SubtheoryError`, `ConstraintError`,
`Z3IntegrationError`, ...) hardcodes a `theory` default either — every class in the current
hierarchy is theory-agnostic; only call sites supply a `theory=` string.

## Raise sites — the decisive fact: witness errors are shared across two theories

`grep` for every raise of `WitnessRegistryError` / `WitnessConstraintError` / `WitnessPredicateError`
/ `WitnessError` outside tests turned up two independent call sites, **not one**:

- `code/src/model_checker/theory_lib/exclusion/semantic/registry.py` (raises `WitnessRegistryError`, `WitnessPredicateError`)
- `code/src/model_checker/theory_lib/exclusion/semantic/constraints.py` (raises `WitnessConstraintError`)
- `code/src/model_checker/theory_lib/exclusion/semantic/core.py` (raises `WitnessError`)
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` (raises `WitnessRegistryError`, `WitnessPredicateError`)
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` (raises `WitnessConstraintError`)

**None of the five raise sites passes a `theory=` kwarg today.** Critically, `bimodal`'s own
`witness_registry.py`/`witness_constraints.py` modules exist specifically because bimodal has its
own accessible-world witness-predicate machinery (single `accessible_world` predicate vs.
exclusion's dual `h`/`y` predicates — see the module docstrings), and they deliberately reuse the
*same* `WitnessRegistryError`/`WitnessConstraintError`/`WitnessPredicateError` classes rather than
defining bimodal-specific subclasses.

## Git history: the hardcoded default existed once and was deliberately removed

`errors.py` has only two commits in its full history: `task 12` (created the hierarchy) and
`task 100 phase 4` (later restructuring). It carries **no commit from the core/theory_lib
refactor** (tasks 122-130) — this bug predates that work entirely.

At creation (`task 12`), the hierarchy had an intermediate class:

```python
class WitnessSemanticError(SemanticError):
    """Base for witness semantics (exclusion theory) errors."""
    def __init__(self, message: str, **kwargs):
        super().__init__(message, theory="exclusion", **kwargs)

class WitnessRegistryError(WitnessSemanticError): pass
class WitnessConstraintError(WitnessSemanticError): pass
class WitnessPredicateError(WitnessSemanticError): pass
```

`task 100 phase 4` ("clean residual source references") deliberately removed this intermediate
class. Its commit message states outright:

> "Fix WitnessRegistryError inheritance (kept for bimodal tests). ... 172 bimodal gate tests pass."

The diff changed `WitnessRegistryError(WitnessSemanticError)` → `WitnessRegistryError(WitnessError)`
(dropping the `theory="exclusion"` default), and changed the `WitnessError` docstring from
`"Base for witness errors (exclusion-specific)"` to `"Base for witness errors."` — an explicit,
intentional generalization made *because* bimodal's witness-predicate code needed to raise these
same classes without being mislabeled as `exclusion`.

**`test_witness_registry_error_basic`/`test_witness_constraint_error_basic` were never updated
after that architectural change.** They still assert the pre-task-100 contract (auto-defaulted
`"exclusion"`), which task 100 correctly recognized as wrong for a class used by two theories.

Task 121 phase 3 partly touched this same test file (repairing collection errors from a different,
unrelated import bug — `WitnessSemanticError` no longer existed as an importable name). While
fixing `test_witness_error_construction` it already established the correct post-task-100 pattern
in this very file:

```python
def test_witness_error_construction(self):
    """Test that WitnessError (the base witness exception) can be constructed
    with an explicit theory (the class itself does not default theory)."""
    error = WitnessError("Test witness error", theory="exclusion")
    assert error.theory == "exclusion"
```

and, in the sibling `TestImpositionErrorHandling` class:

```python
def test_semantic_error_with_imposition_theory(self):
    """Test that SemanticError carries an explicit imposition theory tag."""
    error = SemanticError("Test imposition error", theory="imposition")
    assert error.theory == "imposition"
```

Both already model the correct contract — explicit `theory=` kwarg at construction, no class
default — but task 121 missed applying the same fix to the two `WitnessRegistryError`/
`WitnessConstraintError` "basic" tests directly below `test_witness_error_construction` in the
same class, which is why they are still broken today.

## Weighing the two options

**Option A — bind a theory identifier in the class/constructor.** Rejected. A hardcoded
`theory="exclusion"` default (re-adding `WitnessSemanticError`-style binding) would be actively
wrong: it would mislabel every bimodal witness-registry/constraint error as belonging to the
`exclusion` theory, contradicting the class's own (now-generalized) docstring and directly
undoing the intentional fix task 100 phase 4 made "for bimodal tests." A constructor-argument
variant (each raise site supplies its own theory name) is architecturally sound and matches how
`SemanticError(..., theory="imposition")` is already used elsewhere, but is out of scope here:
none of the five raise sites currently thread a theory identifier through their call chains
(`WitnessRegistry`, `WitnessConstraintGenerator` etc. take `N`/`M`/`semantics` — no theory-name
constant is passed in), and there is no existing "theory names itself" constant/registry lookup
(`grep` for `THEORY_NAME`/`theory_name =` in exclusion/bimodal found nothing) to source one from
without inventing new plumbing. That is a larger, separately-scoped change and isn't needed to
resolve the two failing assertions — it would also cut against the core/theory_lib refactor's
principle of not hardcoding theory-name literals into shared/core code paths.

**Option B — fix the two tests to assert the actual (and correct) contract.** This is the right
fix. It is:
- Consistent with the shared-class design task 100 phase 4 deliberately established (one error
  hierarchy, no theory baked in, because both exclusion and bimodal raise these classes).
- Consistent with the pattern already used one test up in the same class
  (`test_witness_error_construction`) and in the sibling imposition test — explicit `theory=`
  kwarg at construction, asserted back.
- Zero production-code risk: no changes to `errors.py`, `registry.py`, `constraints.py`, or the
  bimodal witness modules, all of which currently work correctly with `theory=None`.

## Recommendation

Fix the two tests, not the class hierarchy. Change:

```python
def test_witness_registry_error_basic(self):
    """Test basic WitnessRegistryError."""
    error = WitnessRegistryError("Registry operation failed")
    assert error.theory == "exclusion"
```
to
```python
def test_witness_registry_error_basic(self):
    """Test basic WitnessRegistryError, constructed with an explicit theory
    (the class itself does not default theory — it is shared by exclusion
    and bimodal, which both raise it without a hardcoded theory label)."""
    error = WitnessRegistryError("Registry operation failed", theory="exclusion")
    assert error.theory == "exclusion"
```
and the analogous change for `test_witness_constraint_error_basic`. This makes both tests pass,
matches the already-established sibling-test pattern in the same file, and records in the
docstring exactly why no class-level default exists (bimodal reuses the same error classes).

No source changes to `errors.py` or any raise site are needed or recommended.
