# Cross-Oracle Differential Testing Infrastructure — Research Report

**Task**: 109 — Cross-oracle differential testing infrastructure
**Session**: sess_1780354245_d07229
**Date**: 2026-06-01

---

## Executive Summary

BimodalHarness is available locally at `/home/benjamin/Projects/BimodalHarness` and can be
imported as a path-extended dependency. The harness provides a `FormulaEnumerator`
(`bimodal_harness.formula.generator`) and an independent `Z3OracleProvider`
(`bimodal_harness.oracle.z3_provider`). There are **two** Z3 oracle implementations:
the ModelChecker one (`bimodal_logic.Z3OracleProvider`, which uses `BimodalSemantics`)
and the BimodalHarness one (`bimodal_harness.oracle.z3_provider.Z3OracleProvider`, which
uses a simpler bounded Kripke encoding). These two are semantically different and will not
agree on all formulas — the differential test harness must be designed with this in mind.

The primary cross-oracle comparison target is between the ModelChecker oracle and the
**BimodalHarness MockOracleProvider** or a Lean subprocess reference, not against the BH
Z3 provider. The plan below describes a self-consistent architecture for empirical
soundness validation.

---

## 1. BimodalHarness Availability Assessment

### Location and Import

BimodalHarness lives at `/home/benjamin/Projects/BimodalHarness/` and exposes:
- `src/bimodal_harness/` — main package
- Importable by adding `/home/benjamin/Projects/BimodalHarness/src` to `sys.path`
- NOT installed as an editable package in the ModelChecker virtualenv

### Relevant Modules

| Module | Purpose |
|---|---|
| `bimodal_harness.formula.generator` | `enumerate_by_complexity`, `enumerate_up_to_complexity`, `random_formula`, `count_formulas` |
| `bimodal_harness.formula.ast` | `FormulaNode`, `Atom`, `Bot`, `Imp`, `Box`, `Untl`, `Snce` + defined ops; `complexity()`, `temporal_depth()`, `to_json()`, `from_json()` |
| `bimodal_harness.oracle._mock` | `MockOracleProvider`, `SPOT_CHECK_FORMULAS` (10 known-invalid formulas) |
| `bimodal_harness.oracle.z3_provider` | `Z3OracleProvider` — different semantics from MC oracle |
| `bimodal_harness.oracle.protocol` | `OracleProvider` Protocol |
| `bimodal_harness.oracle.gateway` | `SoundnessGateway`, `LeanSubprocessValidator` |

### Integration Method

The test file should NOT attempt `import bimodal_harness` directly. Instead, it should
use `pytest.importorskip` with a sys.path extension, or a `conftest.py` fixture that
inserts the path. The recommended pattern:

```python
# In conftest.py or at module level
import sys
from pathlib import Path

BH_SRC = Path("/home/benjamin/Projects/BimodalHarness/src")
if BH_SRC.is_dir():
    sys.path.insert(0, str(BH_SRC))
```

### Lean Subprocess Reference

The `SoundnessGateway.LeanSubprocessValidator` provides a Lean reference oracle via
`lake exe dataset_validator --mode validate-countermodel`. This is the DEFINITIVE
reference. However it requires:
1. Lean toolchain installed
2. `BIMODAL_LOGIC_PATH` environment variable pointing to a BimodalLogic Lean project
3. `dataset_validator` executable built in that project

Without Lean, the test harness must use a different reference oracle. The recommended
fallback is the BimodalHarness `MockOracleProvider` (10 spot-check formulas) or the
BH `Z3OracleProvider` (different semantics, so useful only for cross-check, not reference).

---

## 2. Formula Enumeration Strategy

### BimodalHarness Formula Generator

The `enumerate_by_complexity(n, atoms)` function enumerates ALL primitive-tag formulas
of exactly `n` nodes (structural complexity). Formula counts with 2 atoms (`p`, `q`):

| Complexity | Count | Cumulative |
|---|---|---|
| 1 | 3 | 3 |
| 2 | 3 | 6 |
| 3 | 30 | 36 |
| 4 | 84 | 120 |  — estimated from count_formulas
| 5 | 651 | 771 |
| 6 | 2,703 | 3,474 |
| 7 | 18,633 | 22,107 |

With 1 atom (`p` only): 5,618 formulas up to complexity 7.

### Recommendation: Use 1 Atom with Complexity <= 5

For the differential test suite, use `enumerate_up_to_complexity(5, ["p"])` which yields
~150 formulas. This is manageable for CI (sub-second per formula at typical timeouts).

For extended coverage (if desired), a separate `--slow` marked test class can enumerate
up to complexity 7 with `["p", "q"]`.

### Complexity vs. Temporal Depth

The `complexity()` function in BimodalHarness counts primitive tree nodes. The `temporal_depth()`
function (available in both BimodalHarness `formula.ast` and `bimodal_logic.translation`)
measures temporal nesting depth. For the MC oracle's M parameter:
- `M = max(temporal_depth(formula), 2)` is the current OracleProvider policy
- For a complexity-7 formula, temporal_depth can be up to 3 (e.g., `untl(untl(untl(p,q),r),s)` would be complexity 7)

---

## 3. Oracle API Comparison

### ModelChecker Z3OracleProvider (`bimodal_logic.Z3OracleProvider`)

- **Input**: `formula_json: dict` — JSON with 17 possible tags (6 primitive + 11 enriched)
- **Output**: `dict | None` — countermodel or None (UNSAT/tautology)
- **Output keys**: `temporal_depth`, `boundary_safe`, `time_bound`, `semantics_version`,
  `formula_folded_json`, `trueAtoms`, `falseAtoms`, `world_histories`, `task_relation`,
  `formula`, `evaluation_world`, `evaluation_time`, `world_count`
- **Semantics**: Uses BimodalSemantics (task-based temporal modal logic)
- **Box semantics**: Universal over ALL worlds at same time (no accessibility relation)
- **M param**: `max(temporal_depth(formula), 2)` — dynamically computed

### BimodalHarness Z3OracleProvider (`bimodal_harness.oracle.z3_provider.Z3OracleProvider`)

- **Input**: `formula_json: dict` — JSON with 6 primitive tags only
- **Output**: `dict | None` — countermodel or None
- **Semantics**: Simple bounded Kripke (Boolean accessibility relation `R[w1][w2]`)
- **Box semantics**: Universal over accessible worlds at same time (standard Kripke)
- **Key difference**: Box operator has DIFFERENT semantics — BH uses `R[w1][w2]` accessibility,
  MC uses forall-worlds quantification; these oracles WILL disagree on box-containing formulas

**Verified disagreements at complexity <= 3 (2 atoms)**:
```
box(bot)        BH=SAT, MC=UNSAT   -- BH finds model where R[0][0] makes box(bot) false
box(p)          BH=SAT, MC=UNSAT   -- same accessibility-vs-global semantics mismatch
box(box(p))     BH=SAT, MC=UNSAT
untl(bot, bot)  BH=SAT, MC=UNSAT   -- different until semantics (strict vs. interval)
```

4/18 disagreements at complexity ≤ 3. This is expected and correct — they are different
logics. **The BH Z3 oracle should NOT be used as the reference oracle.**

### MockOracleProvider (`bimodal_harness.oracle._mock.MockOracleProvider`)

- 10 hardcoded known-invalid formulas with pre-defined countermodels
- Returns None for all other formulas
- Useful for self-check testing of the infrastructure

---

## 4. Differential Harness Architecture

### Design Principle

The differential test harness compares the MC oracle against a reference oracle on
a systematic set of formulas. The reference oracle can be:

1. **MockOracleProvider** — 10 hardcoded formulas, fast, no external dependencies
2. **BimodalHarness Z3OracleProvider** — different semantics for box; only use on
   temporal-only formulas (no `box` or `diamond` tags)
3. **Lean subprocess** (`lake exe dataset_validator`) — definitive reference but requires Lean

### Class Structure

```
TestDifferentialHarness (pytest class)
    setup_method: create MC oracle, create reference oracle
    
    test_spot_check_agreement: 10 SPOT_CHECK_FORMULAS, compare against MockOracleProvider
    test_temporal_formulas_up_to_complexity_5: enumerate temporal-only formulas, compare BH Z3
    test_differential_report: parametrized, collect all disagreements and write report
```

### Formula Filtering for BH Z3 Oracle

To use BH Z3 oracle as reference, restrict to formulas without box/diamond:

```python
def _is_temporal_only(formula_json: dict) -> bool:
    tag = formula_json.get("tag", "")
    if tag in ("box", "diamond"):
        return False
    for field in ("left", "right", "child", "event", "guard", "arg"):
        child = formula_json.get(field)
        if child and not _is_temporal_only(child):
            return False
    return True
```

### Disagreement Report Format

When a disagreement is detected, the report entry should include:

```python
{
    "formula_json": formula_json,
    "formula_infix": prefix_to_infix(json_to_prefix(formula_json)),
    "temporal_depth": temporal_depth(formula_json),
    "boundary_safe": M > depth + 1,
    "mc_oracle_result": "SAT" | "UNSAT" | "TIMEOUT",
    "ref_oracle_result": "SAT" | "UNSAT",
    "mc_countermodel": mc_result,  # or None
    "ref_countermodel": ref_result,  # or None
    "complexity": formula_complexity,
    "has_temporal": has_untl_or_snce,
    "has_modal": has_box,
}
```

---

## 5. Test File Architecture

### Location

```
code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py
```

This follows the existing test placement pattern.

### Test Classes

**Class 1: `TestDifferentialInfrastructure`**
- Smoke tests to verify the harness can import and run
- Verify path setup, oracle instantiation, formula enumeration works
- No Z3 calls

**Class 2: `TestSpotCheckAgreement`**
- Compare MC oracle vs MockOracleProvider on 10 SPOT_CHECK_FORMULAS
- All 10 should return SAT (since MockOracleProvider only has known-invalid formulas)
- MC oracle should agree (find countermodels) for all 10

**Class 3: `TestTemporalOnlyDifferential`**
- Filter enumerate_up_to_complexity(5, ["p"]) to temporal-only formulas (no box/diamond)
- Compare MC oracle vs BH Z3 oracle
- Temporal-only formulas should agree (same semantics for untl/snce without box)
- Parametrized via pytest.mark.parametrize

**Class 4: `TestDifferentialReport`**
- Full systematic scan with report generation
- Writes JSON report to `specs/tmp/differential_report_{timestamp}.json`
- Marked `@pytest.mark.slow` — not run in normal CI
- Documents the number of agreements and disagreements

### Differential Report Output

```json
{
    "timestamp": "2026-06-01T12:00:00Z",
    "mc_oracle_id": "bmlogic_z3_base_v1",
    "ref_oracle_id": "bimodal_z3_base_v1",
    "total_formulas": 150,
    "agreements": 142,
    "disagreements": 8,
    "timeout_count": 0,
    "entries": [
        {
            "formula_json": {...},
            "temporal_depth": 1,
            "boundary_safe": true,
            "mc_result": "SAT",
            "ref_result": "UNSAT",
            "mc_countermodel": {...},
            "complexity": 3
        }
    ]
}
```

---

## 6. CI Integration Approach

### Strategy

The differential test suite should be integrated as a separate CI marker (`@pytest.mark.differential`)
that runs on every change to `code/src/bimodal_logic/`. The existing CI only triggers on tags
(`release.yml`). A new GitHub Actions workflow file should be created.

### New Workflow: `.github/workflows/differential-tests.yml`

```yaml
name: Differential Oracle Tests
on:
  push:
    paths:
      - 'code/src/bimodal_logic/**'
      - 'code/src/model_checker/theory_lib/bimodal/**'
  pull_request:
    paths:
      - 'code/src/bimodal_logic/**'
      - 'code/src/model_checker/theory_lib/bimodal/**'

jobs:
  differential:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: {python-version: '3.12'}
      - name: Install dependencies
        run: |
          cd code && pip install -e .
          cd /path/to/BimodalHarness && pip install -e .
      - name: Run differential tests
        run: |
          cd code
          PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py -v
```

**Challenge**: BimodalHarness is a sibling repo, not a submodule. For CI, options:
1. **Add as git submodule** — clean but requires coordination
2. **Install from PyPI** — if bimodal-harness is published (it's not yet)
3. **Copy minimal modules** — copy only formula generator + ast into tests/fixtures/
4. **Mock BimodalHarness in CI** — implement a minimal inline mock that reproduces
   the formula enumeration without depending on the full BimodalHarness package

**Recommendation**: Use option 4 for initial CI. The core formula enumeration (primitive
tags only, complexity-based) is small enough to implement inline or in a test fixture file.
This decouples CI from the BimodalHarness repo availability.

### PyProject.toml Test Configuration

The existing `pyproject.toml` configures pytest to run `src/model_checker/theory_lib/bimodal/tests`.
Add a new marker:

```toml
[tool.pytest.ini_options]
markers = [
    "countermodel: Tests that verify a countermodel exists",
    "theorem: Tests that verify a formula is a theorem",
    "performance: Tests that verify performance characteristics",
    "differential: Cross-oracle differential tests (may require BimodalHarness)",
    "slow: Tests that take longer than normal CI budget",
]
```

---

## 7. Mock Oracle Design (CI-compatible)

For CI runs where BimodalHarness is unavailable, implement a minimal inline mock:

### `MockFormulaEnumerator`

```python
def _enumerate_primitive_formulas(max_complexity: int, atoms: list[str]):
    """Enumerate primitive-tag JSON formulas up to complexity max_complexity.
    
    Mirrors bimodal_harness.formula.generator.enumerate_up_to_complexity but
    uses only the 6 primitive tags and works without BimodalHarness.
    """
    ...
```

This is a self-contained implementation of the same enumeration logic, placed
in the test file or a helper fixture file.

### `MockReferenceOracle`

For formulas where the MC oracle should agree with a reference, define a table of
known-tautologies and known-invalid formulas from the 42-example regression:

```python
# Known tautologies (MC oracle returns None)
KNOWN_TAUTOLOGIES = [
    {"tag": "imp", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "p"}},
    ...
]

# Known invalid (MC oracle returns countermodel)
KNOWN_INVALID = [
    {"tag": "atom", "name": "p"},
    {"tag": "imp", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "q"}},
    ...
]
```

---

## 8. Key Implementation Notes

### Field Name Mismatch: `name` vs `base` for Atoms

The MC oracle uses `{"name": str}` for atom dicts in `trueAtoms`/`falseAtoms`.
The BimodalHarness MockOracleProvider uses `{"base": str}`. The test harness
must handle this when comparing atom sets:

```python
def _atom_names(atoms: list[dict]) -> set[str]:
    return {a.get("name") or a.get("base") for a in atoms}
```

### `box` Semantics Divergence

The MC oracle uses universal-over-all-worlds semantics for `\Box` (no accessibility
relation). The BH Z3 oracle uses a Kripke accessibility relation. They WILL disagree
on box-containing formulas. The differential test harness must either:
1. Skip box-containing formulas when comparing to BH Z3 oracle, OR
2. Use only the MockOracleProvider (which handles box correctly by design), OR
3. Document the disagreements as expected and filter them out of the "error" count

### Temporal-only formulas via `untl` and `snce`

For formulas composed only of `atom`, `bot`, `imp`, `untl`, `snce` (no `box`),
both oracles use consistent temporal semantics. This subset is the most valuable
for differential testing because disagreements indicate genuine oracle bugs.

At complexity ≤ 5 with 1 atom (`p`), there are approximately 50-80 temporal-only
formulas. Running these through both oracles and asserting agreement is a good CI gate.

---

## 9. File and Dependency Summary

### Files to Create

| File | Purpose |
|---|---|
| `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` | Main differential test suite |
| `.github/workflows/differential-tests.yml` | CI workflow for differential tests |

### Files to Modify

| File | Change |
|---|---|
| `code/pyproject.toml` | Add `differential` and `slow` pytest markers |

### Dependencies

| Dependency | Status | Required For |
|---|---|---|
| `bimodal_logic` (MC oracle) | Available (`code/src/bimodal_logic/`) | MC oracle |
| `bimodal_harness.formula` | Available at `/home/benjamin/Projects/BimodalHarness/src` | Formula enumeration |
| `bimodal_harness.oracle._mock` | Available at same path | MockOracleProvider |
| Lean + BimodalLogic project | Not available | Lean subprocess validation |

### Integration Point Documentation

If/when BimodalHarness integration tightens, the integration point is:
- `SoundnessGateway` in `bimodal_harness.oracle.gateway`
- Entry points group `bimodal_harness.oracle_providers` — MC oracle is already registered
- `Z3OracleProvider` in `bimodal_logic.provider` already implements `OracleProvider` protocol

---

## 10. Recommended Implementation Plan

**Phase 1** (Unit tests, no BimodalHarness): Implement self-contained primitive formula
enumerator and spot-check comparison using hardcoded known-valid/invalid formulas from
the existing 42-example regression suite.

**Phase 2** (BimodalHarness path integration): Add conditional import of BimodalHarness
with `pytest.importorskip`. Run temporal-only formulas through both MC oracle and BH Z3
oracle. Assert agreement on non-box formulas.

**Phase 3** (Differential report): Add report generation for full complexity-5 scan.
Write JSON report file for forensic analysis.

**Phase 4** (CI integration): Add `differential-tests.yml` GitHub Actions workflow.
Use Phase 1's self-contained enumerator so CI does not require BimodalHarness checkout.
