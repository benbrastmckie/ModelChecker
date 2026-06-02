# Research Report: Integration Testing and Validation

**Task**: 105 - Integration testing and validation
**Date**: 2026-06-01
**Dependencies**: 103 (completed), 104 (completed), 112 (completed)

## 1. Executive Summary

This report documents the complete landscape of existing test coverage, the OracleProvider protocol, the 52 bimodal examples, the 11 enriched operators, and the BimodalHarness integration points for task 105. The existing codebase already has substantial coverage (710 tests across the bimodal test suite), but there are specific gaps that task 105 must fill: a dedicated `test_oracle_interface.py` that runs all 52 examples through `OracleProvider.find_countermodel()` (not `run_test`), enriched formula round-trip tests via the oracle (not the internal pipeline), cross-signal validation using BimodalHarness SPOT_CHECK_FORMULAS, ternary serialization validation at the oracle output level, entry-point discovery tests, and edge-case handling (timeout, unsupported frame class, malformed JSON).

## 2. OracleProvider Protocol

### 2.1 Protocol Definition

**Location**: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/protocol.py`

The `OracleProvider` is a `@runtime_checkable` Python Protocol with:

**5 Required Properties**:
| Property | Type | Example Value |
|----------|------|---------------|
| `provider_id` | `str` | `"bmlogic_z3_base_v1"` |
| `provider_version` | `str` | `"0.1.0"` |
| `semantics_version` | `str` | `"bimodal-logic-v0.1.0"` |
| `supported_frame_classes` | `frozenset[str]` | `frozenset({"Base"})` |
| `capabilities` | `dict[str, Any]` | `{"max_N": 4, "max_M": 8, ...}` |

**2 Required Methods**:

1. `find_countermodel(formula_json, frame_class="Base", timeout_ms=5000) -> dict | None`
   - Returns `None` for valid formulas (UNSAT) or unsupported frame_class
   - Returns countermodel dict for invalid formulas (SAT)

2. `validate_self(spot_check_formulas: list[dict]) -> bool`
   - Returns `True` if all spot-check formulas produce countermodels

### 2.2 Z3OracleProvider Implementation

**Location**: `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/provider.py`

The `Z3OracleProvider` class implements the protocol with:
- `provider_id = "bmlogic_z3_base_v1"`
- `provider_version = "0.1.0"`
- `semantics_version = "bimodal-logic-v0.1.0"`
- `supported_frame_classes = frozenset({"Base"})`
- `capabilities = {"max_N": 4, "max_M": 8, "supports_enriched_tags": True, "z3_timeout_configurable": True}`

Pipeline: `json_to_prefix() -> prefix_to_infix() -> Syntax -> BimodalSemantics -> ModelConstraints -> BimodalStructure -> serialize_countermodel()`

Time bound formula: `M = max(depth + 2, 3)` (boundary-safe, fixed in task 114)

### 2.3 Countermodel Output Schema

SAT results (non-None) contain:
```python
{
    # StructuredCountermodel fields
    "temporal_depth": int,      # non-negative integer
    "boundary_safe": bool,      # M > depth + 1
    "time_bound": int,          # M value used
    "semantics_version": str,   # matches provider.semantics_version
    "formula_folded_json": dict, # fold_formula result (enriched tags)
    
    # SimpleCountermodel fields
    "formula": dict,            # original formula_json input
    "trueAtoms": list,          # [{"name": str}, ...]
    "falseAtoms": list,         # [{"name": str}, ...]
    "world_histories": list,    # [{"world_id": int, "times": {str: str}}, ...]
    "task_relation": list,      # [{"source": int, "duration": int, "target": int}, ...]
    
    # Evaluation point metadata
    "evaluation_world": int,
    "evaluation_time": int,
    "world_count": int,
}
```

### 2.4 Entry-Point Discovery

**Configuration** (in `code/pyproject.toml`):
```toml
[project.entry-points."bimodal_harness.oracle_providers"]
z3_base = "bimodal_logic.provider:Z3OracleProvider"
```

**Discovery Mechanism**: `OracleRegistry.discover()` uses `importlib.metadata.entry_points(group="bimodal_harness.oracle_providers")` to find and instantiate providers. Each discovered class is checked with `isinstance(provider, OracleProvider)` before registration.

**Registry Location**: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/registry.py`

**Note**: Entry-point discovery requires `pip install -e .` (or `pip install bimodal-logic`) so that the package metadata is registered. Without installation, `entry_points()` returns empty.

## 3. Catalog of 52 Bimodal Examples

### 3.1 Overview

Total examples in `examples.py`: 52
- Countermodel examples (expectation=True): 13
- Theorem examples (expectation=False): 39

### 3.2 Full Example List

**Countermodel Examples (expectation=True, SAT -- countermodel expected)**:

| # | Name | Category | N | M | Description |
|---|------|----------|---|---|-------------|
| 1 | EX_CM_1 | Extensional | 2 | 1 | Disjunction to conjunction |
| 2 | MD_CM_1 | Modal | 2 | 1 | Distribute necessity over disjunction |
| 3 | MD_CM_2 | Modal | 2 | 1 | Distribute possibility over conjunction |
| 4 | MD_CM_3 | Modal | 2 | 1 | Actuality to necessity |
| 5 | MD_CM_4 | Modal | 2 | 1 | Possibility to actuality |
| 6 | MD_CM_5 | Modal | 2 | 1 | Possibility to necessity |
| 7 | MD_CM_6 | Modal | 2 | 1 | Incompatible possibilities |
| 8 | TN_CM_1 | Tense | 2 | 2 | A => Future A |
| 9 | TN_CM_2 | Tense | 2 | 3 | future A, future B => future(A and B) |
| 10 | BM_CM_1 | Bimodal | 2 | 2 | All future to necessity (contingent) |
| 11 | BM_CM_2 | Bimodal | 2 | 2 | All past to necessity (contingent) |
| 12 | BM_CM_3 | Bimodal | 2 | 2 | Possibility to some future (contingent) |
| 13 | BM_CM_4 | Bimodal | 2 | 2 | Possibility to some past (contingent) |

**Theorem Examples (expectation=False, UNSAT -- no countermodel expected)**:

| # | Name | Layer | N | M | Description |
|---|------|-------|---|---|-------------|
| 1 | EX_TH_1 | Extensional | 2 | 1 | Conjunction to disjunction |
| 2 | MD_TH_1 | Modal | 2 | 2 | K axiom (necessity distributes over implication) |
| 3 | MD_TH_2 | Modal | 2 | 2 | Box A => A (contingent) |
| 4 | TN_TH_2 | Tense | 2 | 2 | A => Future(past A) |
| 5 | BM_TH_1 | Bimodal | 2 | 3 | Box A => Future A (perpetuity) |
| 6 | BM_TH_2 | Bimodal | 2 | 3 | Box A => Past A (perpetuity) |
| 7 | BM_TH_3 | Bimodal | 2 | 2 | future A => Diamond A |
| 8 | BM_TH_4 | Bimodal | 2 | 2 | past A => Diamond A |
| 9 | BM_TH_5 | Bimodal | 2 | 2 | Box A => Future(Box A) (contingent) |
| 10-13 | PROP_K/S/EX_FALSO/PEIRCE | Layer 1 | 1-3 | 1 | Propositional axioms |
| 14-18 | MODAL_T/4/B/5 | Layer 2 | 1 | 1-2 | S5 modal axioms |
| 19-30 | BX1..BX12P | Layer 3 basic | 1-3 | 2-4 | Temporal axioms (serial, mono, connect, until/since) |
| 31 | MF_MODAL_FUTURE_TH | Layer 4 | 2 | 2 | Modal-temporal interaction (contingent) |
| 32-39 | BX5..BX13P | Layer 3 adv | 2-3 | 4 | Advanced temporal (accum, absorb, linearity, enrichment) |
| 40-41 | BX7/BX7P | Layer 3 complex | 4 | 5 | Linearity 4-variable axioms |

### 3.3 Known Timeout/Exclusion Examples

9-10 examples are routinely excluded from automated testing due to timeout or non-determinism:
- TN_CM_1, TN_CM_2, BM_CM_3 (timing-sensitive countermodels)
- MD_TH_2, BM_TH_1, BM_TH_2, MF_MODAL_FUTURE_TH (contingent or long timeouts)
- BX7_LINEAR_U_TH, BX7P_LINEAR_S_TH (complex 4-variable axioms, max_time=60)
- BM_CM_1 (additionally excluded in test_oracle_provider.py, pre-existing timeout)

### 3.4 Important Note on Example Count

The task description says "43 examples" but there are actually **52 examples** in `unit_tests` (13 countermodels + 39 theorems). After excluding 9 timeout examples, 43 are actively tested in `test_boundary_regression.py`. The oracle regression test in `test_oracle_provider.py` uses 42 (adds BM_CM_1 to exclusions).

## 4. The 11 Enriched Operators

### 4.1 Operator Catalog

**Location**: Defined in `bimodal_logic/translation.py`, tested in `test_enriched_equivalence.py`, `test_fold_unfold.py`, `test_json_translation.py`

| # | Enriched Tag | Level | JSON Schema | Primitive Expansion |
|---|-------------|-------|-------------|-------------------|
| 1 | `neg` | L1 | `{"tag":"neg","arg":...}` | `imp(A, bot)` |
| 2 | `top` | L1 | `{"tag":"top"}` | `imp(bot, bot)` |
| 3 | `next` | L1 | `{"tag":"next","arg":...}` | `untl(A, bot)` |
| 4 | `prev` | L1 | `{"tag":"prev","arg":...}` | `snce(A, bot)` |
| 5 | `and` | L2 | `{"tag":"and","left":...,"right":...}` | `imp(imp(A, imp(B, bot)), bot)` |
| 6 | `or` | L2 | `{"tag":"or","left":...,"right":...}` | `imp(imp(A, bot), B)` |
| 7 | `diamond` | L2 | `{"tag":"diamond","arg":...}` | `imp(box(imp(A, bot)), bot)` |
| 8 | `some_future` | L2 | `{"tag":"some_future","arg":...}` | `untl(A, imp(bot, bot))` |
| 9 | `some_past` | L2 | `{"tag":"some_past","arg":...}` | `snce(A, imp(bot, bot))` |
| 10 | `all_future` | L3 | `{"tag":"all_future","arg":...}` | `imp(untl(imp(A,bot),imp(bot,bot)),bot)` |
| 11 | `all_past` | L3 | `{"tag":"all_past","arg":...}` | `imp(snce(imp(A,bot),imp(bot,bot)),bot)` |

### 4.2 Existing Enriched Test Coverage

- `test_enriched_equivalence.py`: 69 tests verifying enriched<->primitive biconditional equivalences via `run_test()` (internal pipeline)
- `test_fold_unfold.py`: 90 tests for `unfold_formula`, `fold_formula`, `normalize_formula` (structural, not Z3)
- `test_json_translation.py`: 75+ tests for `json_to_prefix`, `temporal_depth`, `prefix_to_infix`, `Sentence.from_prefix`

**Gap for task 105**: None of these test enriched operators through `find_countermodel()` (the oracle interface). Task 105 needs tests that submit enriched-tag JSON formulas to the oracle and compare against primitive-tag equivalents.

## 5. SPOT_CHECK_FORMULAS (BimodalHarness)

### 5.1 Location and Content

**Location**: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/_mock.py`

10 known-invalid formulas, each a JSON dict:

| # | Formula | Description |
|---|---------|-------------|
| 1 | `imp(atom(p), box(atom(p)))` | p -> Box p (invalid in Base frame) |
| 2 | `imp(box(atom(p)), atom(p))` | Box p -> p (invalid non-reflexive) |
| 3 | `imp(box(atom(p)), box(box(atom(p))))` | Box p -> Box Box p (invalid in Base) |
| 4 | `imp(untl(p,q), untl(q,p))` | Until not symmetric |
| 5 | `imp(snce(p,q), untl(q,p))` | Since and Until different |
| 6 | `box(bot)` | Necessarily false |
| 7 | `imp(atom(p), untl(p,bot))` | p -> p Until bot |
| 8 | `imp(box(p), box(q))` | Box p -> Box q |
| 9 | `imp(untl(p,q), atom(p))` | Until implies first arg |
| 10 | `imp(snce(p,q), atom(p))` | Since implies first arg |

### 5.2 Cross-Signal Considerations

The MC oracle uses "universal-over-all-worlds" Box semantics (S5-like), while BimodalHarness uses Kripke accessibility semantics. This means:
- **Formulas 1-3, 6, 8** (box-containing): MC and BH oracles may disagree on SAT/UNSAT
- **Formulas 4-5, 7, 9-10** (temporal-only): MC and BH oracles should agree

Existing `test_cross_oracle_differential.py::TestMockOracleSpotCheck::test_spot_check_all` already filters for temporal-only spot-check formulas and verifies MC oracle finds countermodels.

## 6. Boundary/Temporal Depth System

### 6.1 Temporal Depth Computation

`temporal_depth(formula_json)` returns the nesting depth of temporal operators:
- Leaf nodes (atom, bot, top): depth 0
- Extensional operators (neg, imp, and, or): max of children depths (no increment)
- Modal operators (box, diamond): pass through children (no increment)
- Temporal operators (untl, snce, next, prev, some_future, some_past, all_future, all_past): 1 + max of children depths

### 6.2 Boundary Safety

Formula: `M_safe(d) = max(d + 2, 3)` where d = temporal_depth

`boundary_safe = M > depth + 1` (equivalently, `M >= depth + 2`)

After task 114 fix, the oracle always uses `M = max(depth + 2, 3)`, so `boundary_safe` is True for all formulas.

### 6.3 Existing Boundary Test Coverage

- `test_boundary_regression.py`: Pure-Python boundary math tests, Z3 behavioral boundary tests, 43-example regression, all-17-tags temporal_depth coverage
- `test_soundness_regression.py`: Boundary vacuity, shift closure, guarded compositionality, 100+ state isolation calls, known boundary-unsafe formulas

## 7. Existing Test Coverage Map

### 7.1 Test File Inventory (bimodal/tests/)

| File | Tests | Focus |
|------|-------|-------|
| `test_oracle_provider.py` | ~70 | Provider properties, output contract, validate_self, state isolation (100 calls), formula_folded_json, 42-example regression |
| `test_enriched_equivalence.py` | 69 | Enriched<->primitive equivalences via run_test |
| `test_boundary_regression.py` | ~50 | Boundary math, Z3 boundary behavior, 43-example regression, temporal_depth all-tags |
| `test_soundness_regression.py` | ~50 | Boundary vacuity, shift closure, frame axioms, state isolation with temporal |
| `test_fold_unfold.py` | 90 | fold/unfold/normalize structural tests, 120+ round-trip |
| `test_json_translation.py` | 75+ | json_to_prefix, temporal_depth, prefix_to_infix, Sentence.from_prefix |
| `test_cross_oracle_differential.py` | ~50 | Formula enumerator, differential infrastructure, BH comparison, CI gates |
| `test_frame_class_mapping.py` | ~30 | Post-hoc TaskFrame axiom validation |
| `test_bimodal.py` | ~50 | Core bimodal example regression |
| Others (witness, next/prev, foralltime, etc.) | ~175 | Operator-specific tests |
| **Integration tests** (5 files) | ~50 | API consistency, data extraction, injection, strict semantics, until/since |
| **Total** | **~710** | |

### 7.2 Identified Coverage Gaps

**Gap 1: Oracle Interface Regression (test_oracle_interface.py)**
- Need: Run all 52 examples through `OracleProvider.find_countermodel()` (not `run_test`)
- Status: `test_oracle_provider.py::TestOracleExampleRegression` runs 42 examples through `run_test()`, NOT through `find_countermodel()`
- The existing test uses `_run_oracle_on_example()` which calls `run_test()` directly. Task 105 needs to convert each example's conclusion to JSON and run it through the oracle's `find_countermodel()` interface.

**Gap 2: Enriched Formula Round-Trip via Oracle**
- Need: For each enriched operator, submit enriched-tag JSON and primitive-tag JSON to `find_countermodel()`, verify identical SAT/UNSAT
- Status: `test_enriched_equivalence.py` verifies equivalences via `run_test()` (internal pipeline), not via the oracle API
- Need: Also verify `formula_folded_json` is present and correct in all non-None outputs
- Need: Test mixed formulas (combining enriched and primitive tags)

**Gap 3: Cross-Signal with SPOT_CHECK_FORMULAS**
- Need: Use all 10 SPOT_CHECK_FORMULAS as ground truth for `validate_self()`
- Status: `test_cross_oracle_differential.py::TestMockOracleSpotCheck::test_spot_check_all` tests temporal-only subset but skips box-containing formulas
- The MC oracle should return True for `validate_self()` on temporal-only formulas, and documented behavior for box-containing formulas

**Gap 4: Ternary Serialization Validation**
- Need: Verify ALL `task_relation` entries are `{"source": int, "duration": int, "target": int}` dicts
- Status: `test_oracle_provider.py::test_task_relation_ternary_format` checks this for one formula (SIMPLE_SAT_JSON)
- Need: Check across ALL SAT results from the 52-example suite

**Gap 5: Temporal Depth Reporting via Oracle**
- Need: Verify `temporal_depth` is present and correct in ALL oracle outputs, including enriched-tag formulas
- Status: Existing tests check depth for individual formulas but not systematically across all oracle outputs
- Need: Verify depth is identical regardless of enriched vs primitive form

**Gap 6: Edge Cases**
- Need: Timeout handling (formula that exceeds timeout_ms)
- Need: Unsupported frame_class ("Dense" -> None)
- Need: Malformed formula JSON
- Status: `test_oracle_provider.py::test_unsupported_frame_class_returns_none` covers frame_class edge case, but timeout and malformed JSON are not tested

**Gap 7: Entry-Point Discovery**
- Need: Verify `pip install bimodal-logic` followed by `OracleRegistry.discover()` finds the provider
- Status: Not tested; entry-point tests are in BimodalHarness (`tests/test_oracle/test_registry.py`), not in ModelChecker
- Implementation note: This requires the package to be installed (`pip install -e .`), so the test should check whether the entry point is registered and skip gracefully if not installed

**Gap 8: Z3 Isolation / Memory Growth**
- Need: Run `find_countermodel()` 100+ times in sequence, verify no state leakage or memory growth
- Status: `test_oracle_provider.py::TestStateIsolation` already tests 100 sequential calls with consistent results AND checks `_semantics is None` afterward. Additional memory growth testing could use `tracemalloc` but the core isolation is covered.

## 8. Test Infrastructure Patterns

### 8.1 Standard Pattern for run_test Tests

```python
from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalStructure, BimodalProposition, BimodalSemantics, bimodal_operators
)
from model_checker.utils.context import isolated_z3_context

with isolated_z3_context():
    result = run_test(example_case, BimodalSemantics, BimodalProposition,
                      bimodal_operators, Syntax, ModelConstraints, BimodalStructure)
```

### 8.2 Standard Pattern for Oracle Tests

```python
from bimodal_logic import Z3OracleProvider

provider = Z3OracleProvider()
result = provider.find_countermodel(formula_json, frame_class="Base", timeout_ms=5000)
# result is dict (SAT) or None (UNSAT/unsupported)
```

### 8.3 Key Test Utilities

- `isolated_z3_context()`: Context manager that resets Z3 state between tests
- `pytest.mark.parametrize`: Used for example-level regression tests
- `REGRESSION_TIMEOUT_EXAMPLES`: Set of example names excluded from automated testing

### 8.4 Important: Converting Examples to Oracle JSON

The existing examples use infix string formulas (e.g., `'\\Box A'`). To test through the oracle, these must be converted to JSON. Two approaches:
1. **Parse and convert**: Use Syntax to parse infix, then convert the parsed Sentence to JSON (complex)
2. **Hand-craft JSON equivalents**: For the conclusion formulas, manually construct JSON dicts
3. **Use bimodal_logic.translation**: Convert known JSON dicts to infix via `json_to_prefix -> prefix_to_infix`, then compare results

The most practical approach for a test_oracle_interface.py is to construct JSON formula dicts that match the conclusions from each example and run them through `find_countermodel()`.

## 9. Technical Risks and Challenges

1. **Example-to-JSON conversion**: The 52 examples use infix notation with premises+conclusions. The oracle takes single JSON formulas. For examples with premises, the oracle test can only check the conclusion formula independently (the oracle has no premises support). This means oracle SAT/UNSAT may differ from pipeline SAT/UNSAT for examples with premises.

2. **Timeout sensitivity**: Several examples (BM_TH_1, BM_TH_2, BX7 variants) have `max_time=30-60s`. Running these through the oracle may be slow. The test suite should use appropriate timeout settings and skip markers.

3. **TopOperator bug**: `TopOperator` (\\top) has a known evaluation bug in `derived_definition`. All tests using "top" should use `\\neg \\bot` expansion instead.

4. **Box semantics divergence**: MC oracle uses S5 (universal) Box semantics while BimodalHarness uses Kripke accessibility. Cross-signal tests must account for this.

5. **Entry-point discovery**: Requires package installation. Tests should gracefully skip if not installed.

6. **Memory testing**: Verifying no memory growth over 100+ calls is inherently noisy. Use `tracemalloc` with generous thresholds.

## 10. Recommendations for Test Organization

### 10.1 Proposed Test Files

**`test_oracle_interface.py`** (new, primary deliverable):
- Phase 1: Oracle property compliance (5 properties, 2 methods, return format)
- Phase 2: 52-example regression via `find_countermodel()` (with appropriate exclusions for examples with premises)
- Phase 3: Enriched formula round-trip tests (11 operators x 2 forms)
- Phase 4: Cross-signal with SPOT_CHECK_FORMULAS via `validate_self()`
- Phase 5: Boundary regression (M = max(d+2, 3), boundary_safe=True for all)
- Phase 6: Ternary serialization validation across all SAT outputs
- Phase 7: Temporal depth consistency (enriched vs primitive same depth in output)
- Phase 8: Edge cases (timeout, unsupported frame class, malformed JSON)
- Phase 9: Entry-point discovery (conditional on installation)
- Phase 10: Z3 isolation stress test (100+ sequential calls)

### 10.2 Estimated Test Count

Based on the requirements in the task description:
- Oracle protocol compliance: ~15 tests
- 52-example regression: ~52 parametrized tests (with exclusion set for timeout examples)
- Enriched round-trip: ~22 tests (11 operators x 2 directions)
- Mixed enriched/primitive: ~5 tests
- Cross-signal (SPOT_CHECK): ~5 tests
- Boundary regression: ~10 tests
- Ternary serialization: ~5 tests
- Temporal depth: ~10 tests
- Edge cases: ~10 tests
- Entry-point discovery: ~3 tests
- Z3 isolation: ~3 tests
- **Total: ~140 tests**

### 10.3 Test Dependencies

All tests should import from:
- `bimodal_logic` (Z3OracleProvider, translation functions)
- `bimodal_harness.oracle._mock` (SPOT_CHECK_FORMULAS -- conditional import with skip)
- `bimodal_harness.oracle.registry` (OracleRegistry -- conditional import with skip)
- `model_checker.theory_lib.bimodal.examples` (countermodel_examples, theorem_examples)
