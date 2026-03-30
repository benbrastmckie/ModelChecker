# Implementation Plan: Task 56

- **Task**: 56 - Fix comparison.py warnings: add 'M' to DEFAULT_EXAMPLE_SETTINGS and gitignore output.json
- **Status**: [NOT STARTED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: None (simple fix based on investigation)
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md
- **Type**: python
- **Lean Intent**: false

## Overview

Fix two minor issues discovered during comparison.py benchmarking:
1. Add 'M' to DEFAULT_EXAMPLE_SETTINGS in LogosSemantics to suppress warnings
2. Add output.json to .gitignore since it's a generated benchmark file

### Problem Analysis

**Issue 1: 'M' setting warnings**
- 4 constitutive examples (CL_TH_16-19) use `'M': 2` setting
- The base `SemanticDefaults` class in `models/semantic.py` handles 'M' (lines 79-81)
- But `LogosSemantics.DEFAULT_EXAMPLE_SETTINGS` doesn't declare it
- Results in 8 warnings (4 examples x 2 solvers)

**Issue 2: output.json not gitignored**
- comparison.py writes benchmark results to output.json
- This generated file is untracked and should be ignored

## Goals & Non-Goals

**Goals**:
- Suppress the "Unknown example setting 'M'" warnings
- Prevent output.json from appearing in git status

**Non-Goals**:
- Not changing the semantics of 'M' handling (already works correctly)
- Not changing comparison.py behavior

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Default value for 'M' affects other examples | L | L | Use None as default (no change to existing behavior) |

## Implementation Phases

### Phase 1: Add 'M' to DEFAULT_EXAMPLE_SETTINGS [NOT STARTED]

**Goal**: Add 'M' setting declaration to suppress warnings

**Tasks**:
- [ ] Add `'M': None` to DEFAULT_EXAMPLE_SETTINGS dict in LogosSemantics

**Timing**: 5 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Add 'M' to DEFAULT_EXAMPLE_SETTINGS (around line 116-125)

**Verification**:
- Run `./comparison.py --subtheory constitutive` - no 'M' warnings should appear

---

### Phase 2: Add output.json to .gitignore [NOT STARTED]

**Goal**: Prevent generated benchmark file from appearing in git status

**Tasks**:
- [ ] Add `code/output.json` to .gitignore

**Timing**: 2 minutes

**Files to modify**:
- `.gitignore` - Add entry for code/output.json

**Verification**:
- `git status` should not show code/output.json as untracked

## Testing & Validation

- [ ] Run `./comparison.py --subtheory constitutive` - no 'M' warnings
- [ ] Run full `./comparison.py` - no warnings about unknown settings
- [ ] `git check-ignore code/output.json` returns the file (exit 0)

## Artifacts & Outputs

- Modified: `code/src/model_checker/theory_lib/logos/semantic.py`
- Modified: `.gitignore`

## Rollback/Contingency

Simple changes - revert if any issues:
- Remove 'M' from DEFAULT_EXAMPLE_SETTINGS
- Remove output.json entry from .gitignore
