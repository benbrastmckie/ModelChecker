# Implementation Plan: Remove Vestigial ISemantics Protocol (Revised)

- **Task**: 44 - Remove vestigial ISemantics Protocol and use concrete SemanticDefaults type in Operator base class
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_isemantics-refactor.md
- **Artifacts**: plans/02_isemantics-refactor-revised.md (this file)
- **Supersedes**: plans/01_isemantics-refactor.md (had contradiction)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: true

## Overview

**Revision Reason**: The previous plan had a contradiction - it said to delete `ISemantics` but also to not change `Operator.__init__`. These are incompatible since `Operator.__init__` imports and uses `ISemantics`.

**Corrected Approach (Hybrid A+B)**:
1. Delete all 3 vestigial Protocol definitions
2. Change `Operator.__init__` type from `ISemantics` to `SemanticDefaults`
3. Add `semantics: LogosSemantics` class-level annotations to each Logos operator class

**Result**: Zero trace of `ISemantics` remains. The name disappears entirely.

### Research Integration

From the research report:
- 3 vestigial Protocol definitions exist: `syntactic/types.py:17` (ISemantics), `models/types.py:44` (ISemantics), `theory_lib/types.py:42` (Semantics)
- `Operator.__init__` at `syntactic/operators.py:51` declares `semantics: ISemantics`
- Logos operators call methods that exist on `LogosSemantics` but not `ISemantics`
- `SemanticDefaults` is the actual base class all semantics extend

## Goals & Non-Goals

**Goals**:
- Delete 3 vestigial Protocol definitions (ISemantics in syntactic/types.py, ISemantics in models/types.py, Semantics in theory_lib/types.py)
- Change `Operator.__init__(self, semantics: ISemantics)` to `Operator.__init__(self, semantics: SemanticDefaults)`
- Add `semantics: LogosSemantics` class annotation to all Logos operator classes
- Achieve zero pyright errors related to `ISemantics` attribute access
- Maintain all existing runtime behavior

**Non-Goals**:
- Creating a new `LogosOperator` base class (not needed - class annotations suffice)
- Modifying `SemanticsProtocol` in `logos/protocols.py` (keep as documentation)
- Changing any non-type-annotation code beyond the base class

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Circular import when Operator imports SemanticDefaults | H | L | SemanticDefaults is in models/, Operator is in syntactic/ - no cycle |
| Missing import in an operator file | M | L | Use grep to verify all TYPE_CHECKING imports are consistent |
| Some operator classes missed | M | L | Run pyright after each phase to verify |

## Implementation Phases

### Phase 1: Update Operator Base Class [NOT STARTED]

**Goal**: Replace `ISemantics` with `SemanticDefaults` in `Operator.__init__`.

**Tasks**:
- [ ] Edit `syntactic/operators.py`:
  - Change import: `from model_checker.models.semantic import SemanticDefaults`
  - Change line 51: `def __init__(self, semantics: SemanticDefaults) -> None:`
  - Remove import of `ISemantics` from `.types`
- [ ] Edit `syntactic/operators.py` line 303 (DefinedOperator):
  - Change: `def __init__(self, semantics: SemanticDefaults) -> None:`
- [ ] Run pyright on `syntactic/operators.py` to verify no errors from this change

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/operators.py` - Update imports and type annotations

**Verification**:
- `pyright code/src/model_checker/syntactic/operators.py` shows no ISemantics errors

---

### Phase 2: Delete Vestigial Protocol Definitions [NOT STARTED]

**Goal**: Remove the 3 unused Protocol definitions.

**Tasks**:
- [ ] Delete `ISemantics` class from `syntactic/types.py` (lines 17-33)
- [ ] Update `syntactic/types.py` to remove `Protocol` from imports if no longer needed
- [ ] Delete `ISemantics` class from `models/types.py` (lines 44-57)
- [ ] Delete `Semantics` class from `theory_lib/types.py` (lines 41-54)
- [ ] Run grep to confirm no remaining references: `grep -r "from.*types import.*ISemantics" code/src/`

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/types.py` - Remove ISemantics Protocol
- `code/src/model_checker/models/types.py` - Remove ISemantics Protocol
- `code/src/model_checker/theory_lib/types.py` - Remove Semantics Protocol

**Verification**:
- `grep -r "class ISemantics\|class Semantics" code/src/model_checker/` returns only `logos/protocols.py` (the well-specified SemanticsProtocol we keep)
- No import errors when loading modules

---

### Phase 3: Add LogosSemantics Annotations to Operator Files [NOT STARTED]

**Goal**: Add `semantics: LogosSemantics` class annotation to all Logos operator classes.

**Tasks**:
- [ ] Add TYPE_CHECKING import block and class annotation to `subtheories/extensional/operators.py`:
  ```python
  from typing import TYPE_CHECKING

  if TYPE_CHECKING:
      from model_checker.theory_lib.logos.semantic import LogosSemantics

  class NegationOperator(syntactic.Operator):
      semantics: "LogosSemantics"
      name = "\\neg"
      ...
  ```
- [ ] Apply same pattern to all 7 classes in extensional/operators.py
- [ ] Apply same pattern to all 4 classes in modal/operators.py
- [ ] Apply same pattern to all 2 classes in counterfactual/operators.py
- [ ] Apply same pattern to all 5 classes in constitutive/operators.py
- [ ] Apply same pattern to all 4+ classes in first-order/operators.py

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/operators.py`

**Verification**:
- Run pyright after each file to track progress
- Each file should show reduced error count

---

### Phase 4: Verification and Cleanup [NOT STARTED]

**Goal**: Confirm all pyright errors are resolved and tests pass.

**Tasks**:
- [ ] Run `pyright code/src/model_checker/theory_lib/logos/subtheories/*/operators.py` and confirm 0 ISemantics-related errors
- [ ] Run `pyright code/src/model_checker/` for full codebase check
- [ ] Run `pytest code/` to verify all tests pass
- [ ] Remove any now-unused imports from the 3 types.py files

**Timing**: 30 minutes

**Verification**:
- `pyright` shows 0 errors related to semantics attribute access
- `pytest code/` passes all tests
- No runtime import errors

## Testing & Validation

- [ ] All pyright ISemantics/Semantics attribute errors resolved
- [ ] `pytest code/` passes all tests
- [ ] No runtime errors when importing operator modules
- [ ] `grep -r "ISemantics" code/src/` returns zero matches (complete removal)

## Artifacts & Outputs

- `specs/044_remove_vestigial_isemantics_protocol/plans/02_isemantics-refactor-revised.md` (this file)
- Modified files: 9 total (1 base class + 3 types.py files + 5 operators.py files)

## Rollback/Contingency

If issues arise:
1. Revert all changes with `git checkout -- code/src/model_checker/`
2. The changes are purely type annotations and Protocol deletions - no runtime behavior changes
3. If partial progress is made, individual file changes can be reverted independently
