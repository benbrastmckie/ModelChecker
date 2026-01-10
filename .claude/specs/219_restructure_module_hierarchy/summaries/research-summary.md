# Research Summary: Module Hierarchy Restructuring

**Task**: 219  
**Date**: 2025-12-28  
**Status**: Complete

---

## Key Findings

- **Root Cause**: `Truth.lean` mixes pure semantic theorems with metatheoretic bridge theorems, creating circular dependency with `Soundness.lean`
- **Solution**: Extract bridge theorems to new `Metalogic/SoundnessLemmas.lean` module
- **Effort**: 12-14 hours for Phase 1 (immediate fix), 34-40 hours for complete restructuring (phased)
- **Risk**: Medium (manageable with proper testing and validation)

---

## Recommended Module Structure

### New Module: `Logos/Core/Metalogic/SoundnessLemmas.lean`

**Purpose**: Bridge module connecting proof system to semantics

**Contents**:
- `axiom_swap_valid`: All axioms remain valid after swap
- `derivable_implies_swap_valid`: Derivable formulas have valid swaps
- All `swap_axiom_*_valid` lemmas (MT, M4, MB, T4, TA, TL, MF, TF)
- All `*_preserves_swap_valid` lemmas (mp, modal_k, temporal_k, weakening)

**Imports**:
- `Logos.Core.Semantics.Truth` (for `truth_at`, `is_valid`)
- `Logos.Core.ProofSystem.Derivation` (for `DerivationTree`)
- `Logos.Core.ProofSystem.Axioms` (for `Axiom`)

**Size**: ~680 lines

### Modified Module: `Logos/Core/Semantics/Truth.lean`

**Changes**:
- **Remove**: `TemporalDuality` namespace (moved to `SoundnessLemmas.lean`)
- **Remove**: Imports of `Derivation.lean` and `Axioms.lean`
- **Keep**: All pure semantic theorems (`truth_at`, `TimeShift` lemmas)

**New Size**: ~600 lines (reduced from 1278)

### Modified Module: `Logos/Core/Metalogic/Soundness.lean`

**Changes**:
- **Add**: Import `SoundnessLemmas.lean`
- **Update**: `temporal_duality` case to use `SoundnessLemmas.derivable_implies_swap_valid`
- **Complete**: Remove `sorry` from temporal_duality case

**New Size**: ~690 lines (minimal increase)

---

## Dependency Resolution

### Current (Problematic)

```
Truth.lean (wants soundness)
   ↑
Validity.lean
   ↑
Soundness.lean (defines soundness)
   ↓ (circular!)
```

### Proposed (Resolved)

```
Soundness.lean
   ↓
SoundnessLemmas.lean (NEW)
   ↓
Truth.lean (pure semantics)
```

**No cycle!** Truth.lean doesn't import Soundness or SoundnessLemmas.

---

## Phased Implementation Plan

### Phase 1: Extract Bridge Theorems (Immediate - 12-14 hours)

**Goal**: Resolve circular dependency

**Tasks**:
1. Create `SoundnessLemmas.lean` (2-3 hours)
2. Move `TemporalDuality` namespace from `Truth.lean` (1 hour)
3. Update `Truth.lean` imports (1 hour)
4. Update `Soundness.lean` to use `SoundnessLemmas` (1 hour)
5. Create tests for `SoundnessLemmas` (2-3 hours)
6. Update existing tests (2 hours)
7. Update documentation (2 hours)
8. Build and verify (1 hour)

**Deliverables**:
- `SoundnessLemmas.lean` (new file)
- `Truth.lean` (modified, pure semantics)
- `Soundness.lean` (modified, uses SoundnessLemmas)
- `SoundnessLemmasTest.lean` (new test file)
- Updated documentation

### Phase 2: Further Separation (Future - 10-12 hours)

**Goal**: Split `Truth.lean` into definitions and properties

**Tasks**:
1. Create `TruthProperties.lean` (2 hours)
2. Move property theorems (1 hour)
3. Update imports (2 hours)
4. Update tests (2 hours)
5. Update documentation (1 hour)
6. Build and verify (1 hour)

**Deliverables**:
- `TruthProperties.lean` (new file)
- `Truth.lean` (modified, definitions only)
- Updated imports in ~10 files

### Phase 3: Establish Layering Policy (Future - 12-14 hours)

**Goal**: Formalize and enforce module layering

**Tasks**:
1. Document layering policy (2 hours)
2. Add layer annotations (2 hours)
3. Create automated dependency checker (4-6 hours)
4. Integrate into CI/CD (1 hour)
5. Update contributing guidelines (1 hour)
6. Train team (1 hour)

**Deliverables**:
- Updated `MODULE_ORGANIZATION.md`
- Layer annotations in all modules
- `scripts/CheckDependencies.py`
- CI/CD integration

---

## Mathlib Patterns Applied

### 1. Separation of Concerns

**Pattern**: Separate definitions, basic properties, and advanced properties

**Application**:
- `Truth.lean`: Pure semantic definitions and basic properties
- `SoundnessLemmas.lean`: Bridge lemmas connecting layers
- `Soundness.lean`: Main metatheoretic results

### 2. Bridge Modules

**Pattern**: Use intermediate modules for cross-layer connections

**Application**:
- `SoundnessLemmas.lean` bridges Semantics (Layer 2) and Metalogic (Layer 3)
- Prevents circular dependencies by design

### 3. Layered Dependency Hierarchy

**Pattern**: Higher layers import lower layers, never reverse

**Application**:
```
Layer 3: Metalogic (Soundness, Completeness)
   ↑
Layer 2.5: Metalogic Bridges (SoundnessLemmas) ← NEW
   ↑
Layer 2: Semantics (Truth, Validity)
   ↑
Layer 1: Syntax + ProofSystem (Formula, Derivation)
```

### 4. Module Size Guidelines

**Pattern**: Keep files under 1200 lines, prefer 500-800

**Application**:
- `Truth.lean`: 1278 → 600 lines (within guidelines)
- `SoundnessLemmas.lean`: 680 lines (within guidelines)
- All modules within target after Phase 1

---

## Risk Mitigation

### Technical Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Import Cycle Reintroduction | Medium | High | Automated dependency checker |
| Test Breakage | High | Medium | Update tests in same PR |
| Performance Regression | Low | Low | Measure compilation time |

### Process Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Incomplete Migration | Medium | Medium | Comprehensive audit checklist |
| Documentation Drift | Medium | Low | Update docs in same PR |
| Team Confusion | Medium | Medium | Clear documentation + training |

**Overall Risk**: Medium (manageable with proper planning)

---

## Validation Strategy

### Automated Checks

- [ ] All files compile without errors
- [ ] No circular dependencies detected
- [ ] All tests pass
- [ ] No new linting warnings
- [ ] Module sizes within guidelines

### Manual Checks

- [ ] All bridge theorems moved to SoundnessLemmas
- [ ] All pure semantic theorems kept in Truth
- [ ] No theorems lost or duplicated
- [ ] Imports follow layering rules
- [ ] Documentation updated

### Acceptance Criteria

- [ ] Circular dependency resolved
- [ ] Soundness theorem complete (no `sorry`)
- [ ] All tests pass
- [ ] Compilation time not significantly increased
- [ ] Code review approved

---

## Next Steps

1. **Immediate**: Implement Phase 1 (extract bridge theorems)
   - Create task branch
   - Implement changes
   - Update tests
   - Update documentation
   - Code review and merge

2. **Short-term**: Monitor for issues
   - Track compilation time
   - Monitor for new circular dependencies
   - Gather team feedback

3. **Medium-term**: Consider Phase 2 (further separation)
   - Evaluate need based on Phase 1 results
   - Plan if module sizes still problematic

4. **Long-term**: Implement Phase 3 (layering policy)
   - Formalize layering rules
   - Create automated enforcement
   - Train team on best practices

---

## References

- **Detailed Research**: [research-001.md](../reports/research-001.md)
- **Task 213 Analysis**: [circular-dependency-analysis.md](../../213_resolve_is_valid_swap_involution_blocker/reports/circular-dependency-analysis.md)
- **Module Organization**: [MODULE_ORGANIZATION.md](../../../Documentation/Development/MODULE_ORGANIZATION.md)
- **Mathlib Patterns**: [Mathlib4 Naming Conventions](https://leanprover-community.github.io/contribute/naming.html)

---

**Recommendation**: Proceed with Phase 1 immediately to resolve circular dependency. Defer Phase 2 and 3 to future iterations based on need and team capacity.
