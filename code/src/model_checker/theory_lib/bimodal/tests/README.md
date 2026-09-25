# Bimodal Theory Tests

Test suite for the bimodal theory's witness-family certificate encoding: certificate datatypes,
Z3 constraint generators, the semantics/structure/proposition classes, operators, and iteration.

## This Suite Is Non-Gating

**The bimodal theory is under active construction and is deliberately not part of what a release
run must pass.** Every test collected from this directory carries the `development` marker, and
all ten release-gating pytest invocations across the repository's CI drivers deselect it with
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
| `test_bimodal.py` | Example tests: every countermodel and theorem example in `examples.py` (no exclusions -- `KNOWN_TIMEOUT_EXAMPLES`/`UNSTABLE_EXAMPLES` are both empty) |
| `test_certificate.py` | `LabelledLasso`/`WitnessFamily` datatypes and the pure-Python re-checker (`recheck`, conditions C1-C4) |
| `test_certificate_fixtures.py` | Hand-built certificate fixtures, independent of `semantic/`, for exercising the re-checker in isolation |
| `test_formula.py` | The `Formula` ADT (`atom`/`bot`/`imp`/`box`/`untl`/`snce`) and sentence-to-`Formula` translation |
| `test_next_prev.py` | The defined `\next`/`\prev` operators (`U(p, bot)`/`S(p, bot)`) |
| `test_operators.py` | Every primitive/defined operator's `true_at`/`false_at` against `translate`'s own rules; the quantifier-free constraint-set claim |
| `test_proposition.py` | `BimodalProposition`: label-membership truth values, empty `proposition_constraints`, the no-certificate case |
| `test_semantic_module_registration.py` | `semantic/` package registration and exports |
| `test_semantics_core.py` | `BimodalSemantics`: settings, vestigial `N`/`all_states`, `true_at` as translate-then-lookup, certificate extraction |
| `test_structure.py` | `BimodalStructure`: the finalize hook, the S3 re-check obligation (including its fail-fast guard on a corrupted certificate), printing, and the A0 frame-class standing test |
| `test_witness_constraints.py` | `WitnessConstraintGenerator`: local coherence, fulfilment, box faithfulness, target constraints -- all quantifier-free |
| `test_witness_registry.py` | `WitnessRegistry`: `wrap`'s slot arithmetic, label bits, box guesses, witness-lasso allocation |

### `integration/`

| File | Focus |
|---|---|
| `test_certificate_lean_agreement.py` | Round-trips a found certificate through BimodalLogic's `lake exe check_certificate` (skipped cleanly when unavailable) |
| `test_data_extraction.py` | `extract_states`/`extract_evaluation_world`/`extract_relations`/`extract_propositions` against real solved structures |
| `test_injection.py` | `inject_z3_model_values`: pinning label bits, box guesses, and the target selector from a previous solve |
| `test_iterate.py` | `BimodalModelIterator`: difference/non-isomorphism constraints over labels and guesses |
| `test_until_since_integration.py` | `\Until`/`\Since` semantic claims (top-guard equivalence to `future`/`past`, the open guard interval, boundary/immediate-witness behaviour) through the full solve path |

## Solve Budgets

The certificate encoding is quantifier-free (no `ForAll`/`Exists`/MBQI/E-matching anywhere in the
search), so every bimodal example now decides in well under 100ms -- measured directly, not
assumed (see the implementation plan's Phase 17/19 sections for the per-example timings). Every
example's `max_time` sits at the repository-wide 10s floor (`code/tests/ci/test_example_budget_floor.py`);
none needs raising for solver-cost reasons. This is a reversal of the retired window-and-abundance
encoding's status quo, under which bimodal examples were among the most expensive in the
repository and several needed individually recalibrated budgets (60s-120s) to absorb heavy-tailed
Z3 solve distributions -- those recalibration records are retired along with the encoding that
needed them (see `examples.py`'s own historical notes on `BM_CM_1`/`BM_CM_4`). See
`code/docs/core/TESTING_GUIDE.md` section 8.6 for the general budget-and-headroom policy and
section 8.13 for the enforced floor.

## See Also

- [`code/docs/core/TESTING_GUIDE.md`](../../../../../docs/core/TESTING_GUIDE.md) — testing
  standards; section 8.14 covers the `development` marker
- [`../README.md`](../README.md) — the bimodal theory itself
- [`../docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md) — semantics design, including the
  frame-class axiom ledger
