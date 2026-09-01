# Bimodal Theory Tests

Test suite for the bimodal theory implementation: world-history semantics, temporal and modal
operators, witness constraints, and frame constraints.

## This Suite Is Non-Gating

**The bimodal theory is under active construction and is deliberately not part of what a release
run must pass.** Every test collected from this directory carries the `development` marker, and
all six release-gating pytest invocations across the repository's CI drivers deselect it with
`-m "... and not development"`. A failing bimodal test therefore does not turn a gating run red.

The marker is applied by the `pytest_collection_modifyitems` hook in this directory's
`conftest.py`, which is path-scoped so that it can only ever mark tests collected from here.
`code/docs/core/TESTING_GUIDE.md` section 8.14 is the source of truth: it records why this theory
is the one authorized theory-wide blanket, what the blanket accepts (a bimodal test regressing
from passing to failing no longer gates), and what retires it.

Two things this status does **not** mean:

- **It is not a skip.** These tests still run, still report, and are expected to be maintained.
  They are quarantined from the gate, not silenced.
- **It does not cover bimodal's soundness.** The cross-oracle differential and soundness
  regression tests in `oracle/bimodal_logic/tests/` are fully gating and stay that way — the
  `development` marker is deliberately unregistered in the `oracle/` tree, so no semantic claim
  about bimodal's correctness can be quarantined by this status.

## Running the Tests

From `code/`:

```bash
# The whole bimodal suite -- runs normally; addopts carries no -m filter
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v

# Explicit opt-in by marker (equivalent selection; also works from any root)
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -m development -v

# Unit tests only / integration tests only
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/unit/ -v
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/integration/ -v

# A single example (example tests are parametrized by example name)
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -k BM_CM_1 -v

# Via the unified runner
./run_tests.py bimodal
```

To reproduce a **gating** run's selection locally — i.e. to confirm a change has not broken
anything outside bimodal — deselect this suite the way CI does:

```bash
PYTHONPATH=src pytest tests src/model_checker -m "not development"

# Equivalent, via the unified runner's --markers/-m passthrough
./run_tests.py bimodal --markers "not development"
```

To explicitly select only the in-development set (equivalent to the whole-suite run above, but
via the same `--markers` flag used to reproduce the gate):

```bash
./run_tests.py bimodal --markers development
```

## Directory Structure

```
tests/
├── README.md      # This file
├── __init__.py
├── conftest.py    # Fixtures, plus the `development` marker application
├── unit/          # Component tests: semantics, operators, witness machinery
└── integration/   # Cross-component tests: iteration, injection, data extraction
```

### `unit/`

| File | Focus |
|---|---|
| `test_bimodal.py` | Example tests: every countermodel and theorem example in `examples.py` |
| `test_bound_var_counter_isolation.py` | Bound-variable counter isolation across semantics instances |
| `test_enriched_equivalence.py` | Equivalence of the enriched and primitive formulations |
| `test_foralltime.py` | The `\Foralltime` operator |
| `test_frame_class_mapping.py` | Frame-class settings to asserted frame constraints |
| `test_frame_constraints.py` | Individual frame-constraint builders on `BimodalSemantics` |
| `test_modal_witness_integration.py` | Modal operators against the witness registry |
| `test_next_prev.py` | The `\Next` and `\Prev` operators |
| `test_semantic_module_registration.py` | `semantic/` package registration and exports |
| `test_until_since.py` | The `\Until` and `\Since` operators |
| `test_witness_constraints.py` | `WitnessConstraintGenerator` |
| `test_witness_registry.py` | `WitnessRegistry` lifecycle |

### `integration/`

| File | Focus |
|---|---|
| `test_api_consistency.py` | Public API shape against the other theories |
| `test_data_extraction.py` | Model data extraction from a solved structure |
| `test_injection.py` | Theory injection into the builder pipeline |
| `test_iterate.py` | `BimodalModelIterator` end to end |
| `test_strict_semantics.py` | Strict-semantics behaviour |
| `test_until_since_integration.py` | `\Until`/`\Since` through the full solve path |

## Solve Budgets

Bimodal examples are among the most expensive in the repository. Tests that solve real models set
an explicit `max_time` rather than inheriting `BimodalSemantics`'s 1-second default, which is
below the actual solve time for most non-trivial bimodal formulas. See
`code/docs/core/TESTING_GUIDE.md` section 8.6 for the budget-and-headroom policy and section 8.13
for the enforced floor.

## See Also

- [`code/docs/core/TESTING_GUIDE.md`](../../../../../docs/core/TESTING_GUIDE.md) — testing
  standards; section 8.14 covers the `development` marker
- [`../README.md`](../README.md) — the bimodal theory itself
- [`../docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md) — semantics design, including the
  frame-class axiom ledger
