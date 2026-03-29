# Implementation Plan: Remove Vestigial ISemantics Protocol

- **Task**: 44 - Remove vestigial ISemantics Protocol and use concrete SemanticDefaults type in Operator base class
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_isemantics-refactor.md
- **Artifacts**: plans/01_isemantics-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: true

## Overview

Remove the 3 unused/underspecified ISemantics/Semantics Protocol definitions that cause pyright errors across all Logos operator files. Apply **pure Option B**: add `semantics: LogosSemantics` class-level annotations directly to each Logos operator class that pyright complains about. Do NOT change the `Operator.__init__` type parameter from `ISemantics`. Delete the vestigial Protocol definitions.

### Research Integration

From the research report:
- 3 vestigial Protocol definitions exist: `syntactic/types.py:17` (ISemantics), `models/types.py:44` (ISemantics), `theory_lib/types.py:42` (Semantics)
- 349 pyright errors across 5 operator files caused by missing attributes on `ISemantics`
- Pure Option B is cleanest: add `semantics: LogosSemantics` annotation to each operator class that pyright complains about
- Use `TYPE_CHECKING` conditional import pattern for runtime efficiency

## Goals & Non-Goals

**Goals**:
- Delete 3 vestigial Protocol definitions (ISemantics in syntactic/types.py, ISemantics in models/types.py, Semantics in theory_lib/types.py)
- Add `semantics: LogosSemantics` class annotation to all Logos operator classes with pyright errors
- Achieve zero pyright errors related to `ISemantics` attribute access
- Maintain all existing runtime behavior

**Non-Goals**:
- Changing `Operator.__init__` signature (leave as `ISemantics`)
- Creating a new `LogosOperator` base class
- Modifying `SemanticsProtocol` in `logos/protocols.py` (keep as documentation)
- Changing any non-type-annotation code

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missing import in an operator file | M | L | Use grep to verify all TYPE_CHECKING imports are consistent |
| Deleting Protocol breaks runtime check somewhere | H | L | Search for runtime uses of ISemantics before deletion |
| Some operator classes missed | M | L | Run pyright after each phase to verify |

## Implementation Phases

### Phase 1: Verify Protocol Usage and Delete Vestigial Definitions [NOT STARTED]

**Goal**: Confirm no runtime usage of the 3 vestigial Protocols, then delete them.

**Tasks**:
- [ ] Search codebase for any runtime uses of `ISemantics` from `syntactic/types.py` or `models/types.py`
- [ ] Search codebase for any runtime uses of `Semantics` from `theory_lib/types.py`
- [ ] Delete `ISemantics` class from `syntactic/types.py` (lines 17-33)
- [ ] Update `syntactic/types.py` imports to remove `Protocol` if no longer needed
- [ ] Delete `ISemantics` class from `models/types.py` (lines 44-57)
- [ ] Delete `Semantics` class from `theory_lib/types.py` (lines 41-54)
- [ ] Run pyright to confirm deletion does not break type checking elsewhere

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/types.py` - Remove ISemantics Protocol
- `code/src/model_checker/models/types.py` - Remove ISemantics Protocol
- `code/src/model_checker/theory_lib/types.py` - Remove Semantics Protocol

**Verification**:
- `grep -r "ISemantics" code/src/` shows only `syntactic/operators.py` import remains
- No runtime errors when importing affected modules

---

### Phase 2: Add LogosSemantics Annotations to Operator Files [NOT STARTED]

**Goal**: Add `semantics: LogosSemantics` class annotation to all Logos operator classes with pyright errors.

**Tasks**:
- [ ] Add TYPE_CHECKING import block to `subtheories/extensional/operators.py`
- [ ] Add `semantics: "LogosSemantics"` to all operator classes in extensional/operators.py (7 classes: NegationOperator, AndOperator, OrOperator, TopOperator, BotOperator, ConditionalOperator, BiconditionalOperator)
- [ ] Add TYPE_CHECKING import block to `subtheories/modal/operators.py`
- [ ] Add `semantics: "LogosSemantics"` to all operator classes in modal/operators.py (4 classes: NecessityOperator, PossibilityOperator, CFNecessityOperator, CFPossibilityOperator)
- [ ] Add TYPE_CHECKING import block to `subtheories/counterfactual/operators.py`
- [ ] Add `semantics: "LogosSemantics"` to all operator classes in counterfactual/operators.py (2 classes: CounterfactualOperator, MightCounterfactualOperator)
- [ ] Add TYPE_CHECKING import block to `subtheories/constitutive/operators.py`
- [ ] Add `semantics: "LogosSemantics"` to all operator classes in constitutive/operators.py (5 classes: IdentityOperator, GroundOperator, EssenceOperator, RelevanceOperator, ReductionOperator)
- [ ] Add TYPE_CHECKING import block to `subtheories/first-order/operators.py`
- [ ] Add `semantics: "LogosSemantics"` to all operator classes in first-order/operators.py (4 classes: LambdaOperator, ForAllOperator, ExistsOperator, IdentityOperator)

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py` - Add annotations to 7 classes
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` - Add annotations to 4 classes
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` - Add annotations to 2 classes
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py` - Add annotations to 5 classes
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/operators.py` - Add annotations to 4 classes

**Code pattern to apply**:
```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker.theory_lib.logos.semantic import LogosSemantics

class SomeOperator(syntactic.Operator):
    semantics: "LogosSemantics"  # Type narrowing for pyright
    name = "..."
    arity = N
```

**Verification**:
- Run pyright after each file modification to track progress
- Each file should show reduced error count

---

### Phase 3: Verification and Cleanup [NOT STARTED]

**Goal**: Confirm all pyright errors are resolved and tests pass.

**Tasks**:
- [ ] Run `pyright code/src/model_checker/theory_lib/logos/subtheories/*/operators.py` and confirm 0 ISemantics-related errors
- [ ] Run `pyright code/src/model_checker/` for full codebase check
- [ ] Run `pytest code/` to verify all tests pass
- [ ] Remove any now-unused imports from the 3 types.py files

**Timing**: 30 minutes

**Verification**:
- `pyright code/src/model_checker/theory_lib/logos/subtheories/*/operators.py` shows 0 errors (or only unrelated errors)
- `pytest code/` passes all tests
- No runtime import errors

## Testing & Validation

- [ ] All pyright ISemantics/Semantics attribute errors resolved (349 -> 0)
- [ ] `pytest code/` passes all tests
- [ ] No runtime errors when importing operator modules
- [ ] `grep -r "ISemantics\|class Semantics" code/src/` only shows legitimate remaining uses

## Artifacts & Outputs

- `specs/044_remove_vestigial_isemantics_protocol/plans/01_isemantics-refactor.md` (this file)
- Modified files: 8 total (3 types.py files + 5 operators.py files)

## Rollback/Contingency

If issues arise:
1. Revert all changes with `git checkout -- code/src/model_checker/`
2. The original ISemantics Protocols, while causing pyright noise, do not affect runtime behavior
3. If partial progress is made, individual operator file changes can be reverted independently
