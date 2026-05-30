# Task 76: Research Report - comparison.py Refactor for Dual-Solver Timing Comparison

**Session**: sess_1775238291_6c3c4c
**Date**: 2026-04-03

## Executive Summary

This research analyzes the current comparison.py implementation and provides a comprehensive recommendation for refactoring it to run curated examples with dual-solver timing comparison. The key findings are:

1. **Current Implementation**: comparison.py already supports dual-solver comparison with full infrastructure for z3/cvc5 switching
2. **Example Source**: All 6 subtheories provide examples with `_TH_` (theorems) and `_CM_` (countermodels) naming conventions
3. **Recommended Approach**: Create a curated `COMPARISON_EXAMPLES` dictionary with explicit example selection
4. **Timing Infrastructure**: Current implementation already records per-solver timing; needs only minor adjustments

## 1. Current comparison.py Structure

### 1.1 Architecture Overview

The comparison module (`code/src/model_checker/theory_lib/logos/comparison.py`) implements:

```
comparison.py (wrapper) -> logos/comparison.py (main module)
                                |
                                v
                        run_benchmarks()
                                |
                        +-------+-------+
                        |               |
                    z3 solver     cvc5 solver
                        |               |
                        v               v
                   ExampleResult   ExampleResult
                        |               |
                        +-------+-------+
                                |
                                v
                        BenchmarkOutput (JSON)
```

### 1.2 Key Components

| Component | Location | Purpose |
|-----------|----------|---------|
| `switch_solver()` | Lines 131-156 | Full cache invalidation and backend switching |
| `flatten_examples()` | Lines 227-244 | Collects examples from all_subtheory_examples |
| `run_example_with_timing()` | Lines 247-316 | Runs single example with timing and timeout |
| `run_benchmarks()` | Lines 352-608 | Main benchmark loop with dual-solver execution |
| `BenchmarkOutput` | Lines 120-128 | Output structure with metadata, summary, results |

### 1.3 Current Example Source

The script imports from `all_subtheory_examples`:
```python
from model_checker.theory_lib.logos.examples import all_subtheory_examples
```

This dictionary contains ALL examples from all subtheories (100+ examples total).

### 1.4 Current Output Format

The current JSON output includes:
- `metadata`: timestamp, solver versions, platform info
- `summary`: per-solver statistics (passed, failed, errors, times)
- `by_subtheory`: breakdown by logos subtheory
- `results`: per-example results with timing
- `disagreements`: examples where solvers disagree

## 2. Catalog of Operators and Examples

### 2.1 Subtheory Overview

| Subtheory | Operators | Example Count | Prefix |
|-----------|-----------|---------------|--------|
| Extensional | neg, and, or, implies, iff, top, bot | 14 (2 CM, 12 TH) | EXT_ |
| Modal | Box, Diamond, CFBox, CFDiamond | 21+ (4 CM, 14 TH, 6 DEF, 3 COMP) | MOD_ |
| Constitutive | equiv, leq (ground), sqsubseteq (essence), Rightarrow (reduction) | 34 (14 CM, 20 TH) | CL_/CON_ |
| Counterfactual | boxright, diamondright | 25+ (21 CM, 7+ TH) | CF_ |
| Relevance | preceq | 20 (11 CM, 9 TH) | REL_ |
| First-Order | forall, exists, identity (=) | 12 (4 CM, 8 TH) | FO_ |

### 2.2 Recommended Example Selection

For a curated comparison test, recommend 2-3 examples per operator class (1-2 theorems + 1-2 countermodels):

#### Extensional (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| EXT_TH_1 | Theorem | Modus Ponens | rightarrow |
| EXT_TH_7 | Theorem | De Morgan's Law 1 | neg, and, or |
| EXT_CM_1 | Countermodel | Contradiction (A not-entails not-A) | neg |
| EXT_CM_2 | Countermodel | Affirming the Consequent | rightarrow |

#### Modal (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| MOD_TH_5 | Theorem | Modal K Axiom | Box |
| MOD_TH_3 | Theorem | Modal Duality | Box, Diamond |
| MOD_CM_1 | Countermodel | Possibility does not entail Necessity | Diamond, Box |
| MOD_CM_3 | Countermodel | Counterfactual to Strict Implication | boxright, Box |

#### Constitutive (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| CL_TH_1 | Theorem | Ground to Essence | leq, sqsubseteq |
| CL_TH_16 | Theorem | Grounding Anti-Symmetry | leq, equiv |
| CL_CM_1 | Countermodel | Equivalence of Tautologies | equiv |
| CL_CM_7 | Countermodel | Identity Distribution | equiv, and, or |

#### Counterfactual (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| CF_TH_1 | Theorem | Counterfactual Identity | boxright |
| CF_TH_2 | Theorem | Counterfactual Modus Ponens | boxright |
| CF_CM_1 | Countermodel | Antecedent Strengthening | boxright |
| CF_CM_7 | Countermodel | Counterfactual Contraposition | boxright |

#### Relevance (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| REL_TH_1 | Theorem | Relevance to Conjunction | preceq, leq |
| REL_TH_7 | Theorem | Grounding Relevance | preceq, leq |
| REL_CM_1 | Countermodel | Antecedent Strengthening | preceq |
| REL_CM_3 | Countermodel | Relevance Transitivity | preceq |

#### First-Order (4 examples)
| Example | Type | Description | Operator Focus |
|---------|------|-------------|----------------|
| FO_TH_1 | Theorem | Universal Distribution | forall |
| FO_TH_5 | Theorem | Reflexivity of Identity | forall, = |
| FO_CM_1 | Countermodel | Existential to Universal | exists, forall |
| FO_CM_3 | Countermodel | Quantifier Scope Ambiguity | forall, exists |

**Total: 24 curated examples** (12 theorems + 12 countermodels)

## 3. Dual-Solver Comparison Architecture

### 3.1 Current Infrastructure (Already Implemented)

The existing comparison.py already implements dual-solver comparison with:

1. **Solver Switching**: `switch_solver()` handles full cache invalidation
2. **Timing**: `time.perf_counter()` for high-resolution timing
3. **Result Comparison**: Detects disagreements between z3 and cvc5
4. **Timeout Handling**: SIGALRM-based timeout per example

### 3.2 Required Modifications

| Area | Current | Proposed |
|------|---------|----------|
| Example Source | `all_subtheory_examples` | New `COMPARISON_EXAMPLES` constant |
| Output Verbosity | Prints progress, errors | Skip countermodel printing |
| Result Focus | Pass/fail vs expectation | Result agreement + timing |
| Output Format | JSON with full results | JSON focused on timing comparison |

### 3.3 Skip Countermodel Printing

The current implementation does NOT print countermodels during comparison (it only records SAT/UNSAT status). This is because:

1. `BuildExample` is created with a mock module that has `print_constraints: False`
2. The comparison only checks `z3_model_status` (True/False), not full model output

No changes needed for countermodel printing suppression.

## 4. Data Structure Design for Results

### 4.1 Simplified Output Structure

```json
{
  "metadata": {
    "timestamp": "ISO8601",
    "z3_version": "4.x.x",
    "cvc5_version": "1.x.x",
    "curated_example_count": 24,
    "total_runtime_seconds": 45.67
  },
  "timing_summary": {
    "z3": {
      "total_time_seconds": 12.34,
      "avg_time_seconds": 0.514,
      "fastest_example": "EXT_TH_1",
      "slowest_example": "CF_CM_1"
    },
    "cvc5": {
      "total_time_seconds": 18.56,
      "avg_time_seconds": 0.773,
      "fastest_example": "EXT_TH_1",
      "slowest_example": "CF_CM_7"
    }
  },
  "results": [
    {
      "subtheory": "extensional",
      "example": "EXT_TH_1",
      "type": "theorem",
      "z3": {"result": "unsat", "time_seconds": 0.023},
      "cvc5": {"result": "unsat", "time_seconds": 0.045},
      "agreement": true,
      "faster_solver": "z3",
      "time_ratio": 1.96
    }
  ],
  "comparison_stats": {
    "agreements": 24,
    "disagreements": 0,
    "z3_faster_count": 15,
    "cvc5_faster_count": 9,
    "avg_time_ratio": 1.54
  }
}
```

### 4.2 Result Interpretation

| Field | Meaning |
|-------|---------|
| `result` | "sat" (countermodel found), "unsat" (theorem), "timeout", "error" |
| `agreement` | Whether z3 and cvc5 returned same result |
| `faster_solver` | Which solver was faster for this example |
| `time_ratio` | slower_time / faster_time (>1 means significant difference) |

## 5. Recommended Refactoring Approach

### 5.1 Clean-Break Approach (Recommended)

Create a new function that uses curated examples:

```python
# New constant at module level
COMPARISON_EXAMPLES = {
    "extensional": ["EXT_TH_1", "EXT_TH_7", "EXT_CM_1", "EXT_CM_2"],
    "modal": ["MOD_TH_5", "MOD_TH_3", "MOD_CM_1", "MOD_CM_3"],
    "constitutive": ["CL_TH_1", "CL_TH_16", "CL_CM_1", "CL_CM_7"],
    "counterfactual": ["CF_TH_1", "CF_TH_2", "CF_CM_1", "CF_CM_7"],
    "relevance": ["REL_TH_1", "REL_TH_7", "REL_CM_1", "REL_CM_3"],
    "first_order": ["FO_TH_1", "FO_TH_5", "FO_CM_1", "FO_CM_3"],
}

def get_curated_examples():
    """Get curated examples for comparison testing."""
    examples = []
    for subtheory, example_names in COMPARISON_EXAMPLES.items():
        subtheory_examples = all_subtheory_examples.get(subtheory, {})
        for name in example_names:
            if name in subtheory_examples:
                examples.append((subtheory, name, subtheory_examples[name]))
    return examples
```

### 5.2 Implementation Phases

**Phase 1: Add Curated Example Selection**
- Add `COMPARISON_EXAMPLES` constant
- Add `get_curated_examples()` function
- Add `--curated` CLI flag to use curated examples

**Phase 2: Simplify Output Format**
- Create `SimplifiedOutput` dataclass
- Focus on timing comparison metrics
- Add `faster_solver` and `time_ratio` fields

**Phase 3: Enhance CLI**
- Add `--format {full|timing}` flag
- Add `--table` flag for ASCII table output
- Keep JSON output as default

### 5.3 Backward Compatibility

Preserve existing behavior when no flags are passed:
- `./comparison.py` - runs all examples (current behavior)
- `./comparison.py --curated` - runs curated 24 examples
- `./comparison.py --curated --format timing` - focused timing output

## 6. Implementation Recommendations

### 6.1 Files to Modify

| File | Changes |
|------|---------|
| `code/src/model_checker/theory_lib/logos/comparison.py` | Add curated examples, simplified output |
| `code/comparison.py` | Add `--curated` flag |

### 6.2 Estimated Effort

| Phase | Effort | Risk |
|-------|--------|------|
| Phase 1: Curated Selection | 30 min | Low |
| Phase 2: Simplified Output | 45 min | Low |
| Phase 3: CLI Enhancements | 30 min | Low |
| **Total** | ~2 hours | Low |

### 6.3 Testing Strategy

1. Run curated examples with both solvers
2. Verify all 24 examples complete without errors
3. Compare timing results between solvers
4. Validate JSON output structure

## 7. Conclusion

The refactoring is straightforward because:

1. **Infrastructure exists**: Dual-solver comparison already works
2. **Clean separation**: Example selection is easily customizable
3. **No model printing**: Current implementation already skips countermodel output
4. **Timing accurate**: `time.perf_counter()` provides high-resolution timing

The recommended approach adds a curated example selection while preserving the existing full-benchmark capability.
