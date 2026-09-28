# Bimodal Theory Tests

Test suite for the bimodal theory's witness-family certificate encoding: certificate datatypes,
Z3 constraint generators, the semantics/structure/proposition classes, operators, and iteration.

## This Suite Is Gating

**The bimodal theory is a gating theory again.** The witness-family certificate redesign
replaced the retired window-and-abundance encoding, restoring the speed and semantic-alignment
properties that previously justified quarantining this theory: every example (including the nine
previously excluded) now decides correctly in well under 50ms. The `development` marker that used
to quarantine this whole tree from release-gating runs is retired — no test here carries it any
more, and no release-gating pytest invocation filters on it any more. A failing bimodal test now
turns a gating run red, exactly like any other theory's test.

`code/docs/core/TESTING_GUIDE.md` section 8.14 records the marker's full history and retirement
for anyone who needs the historical context.

The cross-oracle differential and soundness regression tests in `oracle/bimodal_logic/tests/`
were already fully gating throughout the marker's lifetime and remain so.

## Running the Tests

From `code/`:

```bash
# The whole bimodal suite
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v

# Unit tests only / integration tests only
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/unit/ -v
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/integration/ -v

# A single example (example tests are parametrized by example name)
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -k BM_CM_1 -v

# Via the unified runner
./run_tests.py bimodal
```

This suite runs exactly like any other theory's: no `-m` filter is required to reproduce what a
gating run collects here, and none is applied by `addopts` or by this directory's `conftest.py`.

## Directory Structure

```
tests/
├── README.md      # This file
├── __init__.py
├── conftest.py    # Fixtures only -- no marker-application hook (retired; see TESTING_GUIDE.md 8.14)
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
| `test_certificate_a2_triangle.py` | ADEQUACY.md section 7.3's A2-triangle encoding-completeness test: per-candidate comparison vs. a solver-free pinned evaluation, plus a retained aggregate check against the real Z3 search (Tier 1), plus a bounded Lean sample (Tier 2, skipped cleanly when unavailable). Liveness/regression evidence for the UNSAT direction (A2), never for countermodel trust -- see `docs/TRUST_PIPELINE.md`'s "The standing test for A2" |
| `test_certificate_lean_agreement.py` | Round-trips the fixture corpus through BimodalLogic's `lake exe check_certificate` (skipped cleanly when unavailable) |
| `test_data_extraction.py` | `extract_states`/`extract_evaluation_world`/`extract_relations`/`extract_propositions` against real solved structures |
| `test_injection.py` | `inject_z3_model_values`: pinning label bits, box guesses, and the target selector from a previous solve |
| `test_iterate.py` | `BimodalModelIterator`: difference/non-isomorphism constraints over labels and guesses |
| `test_sentence_translation_agreement.py` | Round-trips BimodalLogic's `Tests/fixtures/sentence-translation-fixtures.jsonl` fixture corpus through this repository's own `Sentence.update_types` + `formula.translate` + `formula.to_json` (skipped cleanly when the checkout is unavailable), plus an optional live differential leg against the built `translate_sentence` binary on a small representative row selection (skipped cleanly when `lake`/the binary are unavailable, independently of the fixture-only leg). Forward-only (`tr` is not injective) and compares parsed JSON, never serialized bytes -- see the module's own docstring |
| `test_until_since_integration.py` | `\Until`/`\Since` semantic claims (top-guard equivalence to `future`/`past`, the open guard interval, boundary/immediate-witness behaviour) through the full solve path |

## Declined Reorganizations

An assessment of this tree's organization (implementation plan Phase 2) considered three further
consolidations and declined each, for reasons recorded here rather than only in the assessment
itself:

- **The three grids stay separate.** `test_certificate_a2_triangle.py`'s A2-triangle
  parametrize table, `test_search_period_coverage.py`'s `_GRID`, and `test_structure.py`'s
  `_A0_SWEPT_GRID` each pin an independent property over its own premises/conclusions and grid
  points. Merging them into one declarative registry would either force three unrelated test
  purposes to share entries they have no logical reason to share, or just relocate three still-
  separate tables into one file with no reduction in what a reader has to understand at each
  call site. Each grid's own module docstring states why it exists.
- **Tier-gating mechanics are unchanged.** Tier membership (Tier 1 exhaustive vs. Tier 2 bounded
  Lean cross-check, in `test_certificate_a2_triangle.py`) is expressed via module docstring
  prose, `pytest.mark.slow`, and a `skipif` keyed on `BIMODAL_LOGIC_PATH` availability. These are
  three different *mechanisms* pytest requires at three different decision points -- prose for a
  human reader, `slow` for local `-m "not slow"` deselection, `skipif` for environment-
  availability gating -- not one fact restated three times. A home-grown registry wrapping
  pytest's own marker/`skipif` mechanics would add indirection without removing duplication.
- **`_pinned_eval.py` stays inside `tests/`.** It is a compile-once, interpret-many evaluator and
  candidate-to-assignment builder that behaves like a library, but it already matches this
  tree's own precedent: `_lean_check.py` is the same kind of leading-underscore, non-test,
  library-like module living inside `tests/`. Moving it into `theory_lib` proper would be a real
  elevation in surface area (a stable public API, docs, likely its own `tests/` directory) that
  only makes sense if it becomes a *shipped* artifact -- a promotion decision owned by a separate,
  concurrent task, not this one. **Coordination note**: if that task promotes a checker onto the
  production path, `_pinned_eval.py`'s natural destination is alongside `semantic/certificate.py`
  in `semantic/` (mirroring that module's own home), with a narrowed public surface -- its
  existing explicit `__all__` already lists every name deliberately, which would ease that future
  move. Stated here for coordination; no promotion decision is made and no location changed by
  this task.

The one real duplication found -- four byte-equivalent `_settings`/`_build` pipeline-construction
helpers, in `test_certificate_a2_triangle.py`, `test_search_period_coverage.py`,
`test_structure.py`, and `test_pinned_eval.py` -- is consolidated into `_build_support.py`
(sibling of `_pinned_eval.py`/`_lean_check.py`, same leading-underscore convention).
`test_structure.py` keeps a four-line local wrapper around the shared `_build` to default
`'verify'` to `'off'` (see that module's own `_build` docstring); the other three call sites
import the shared helper directly. Several other modules in this tree (`test_injection.py`,
`test_iterate.py`, `test_data_extraction.py`, `test_semantics_core.py`, `test_operators.py`,
`test_proposition.py`, `test_until_since_integration.py`, `test_output_gate.py`) carry their own,
independent `_settings`/`_build`-shaped helpers; these were not part of what this task's
dispatch named as restated, and consolidating them is out of this task's scope.

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
