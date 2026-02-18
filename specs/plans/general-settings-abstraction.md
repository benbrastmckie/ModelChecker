# General Settings Abstraction Implementation Plan

**Document Type**: Implementation Specification  
**Created**: 2025-09-16  
**Project**: ModelChecker Framework  
**Component**: Settings Package Refactoring  
**Spec Reference**: `specs/plans/general-settings-abstraction.md`

## Executive Summary

This specification outlines a simple, maintainable refactoring to centralize general settings in the `SemanticDefaults` base class while allowing theories to optionally augment them. The approach prioritizes **simplicity, intelligibility, and maintainability** over complex architectural patterns.

**Core Principle**: General settings belong in the base `SemanticDefaults` class that all theories inherit from. Theories define their example settings and can optionally augment general settings without duplication.

### Primary Objectives

1. **Centralize General Settings**: Move common settings to `SemanticDefaults` base class
2. **Eliminate Duplication**: Remove redundant `DEFAULT_GENERAL_SETTINGS` from all theories
3. **Allow Optional Augmentation**: Theories can add theory-specific general settings if needed
4. **Maintain Simplicity**: Keep the architecture straightforward and easy to understand
5. **Preserve Functionality**: No changes to existing behavior, just cleaner organization

## Current vs Proposed Architecture

### Current Structure (Duplicated)

Each theory redundantly defines the same general settings:

```python
# In EACH theory (bimodal, exclusion, imposition, logos)
class TheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'contingent': False,
        # ... theory-specific settings
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        # DUPLICATED in every theory
        "print_impossible": False,
        "print_constraints": False, 
        "print_z3": False,
        "save_output": False,
        "sequential": False,
        "maximize": False
    }
```

### Proposed Structure (Centralized)

```python
# In models/semantic.py - SemanticDefaults base class
class SemanticDefaults:
    """Base class for all semantic theories."""
    
    # General settings for ALL theories (defined once)
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "sequential": False,
        "maximize": False
    }
    
    # Base class continues as before...

# In each theory - ONLY theory-specific settings
class BimodalSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 2,
        'M': 2,  # Bimodal-specific
        'contingent': False,
        'max_time': 1,
        # ... other example settings
    }
    
    # OPTIONAL: Augment general settings if needed
    ADDITIONAL_GENERAL_SETTINGS = {
        "align_vertically": False  # Bimodal-specific display option
    }
```

### How Settings Merge

The `SettingsManager` will combine settings in priority order:

1. **SemanticDefaults.DEFAULT_GENERAL_SETTINGS** - Base general settings
2. **Theory.ADDITIONAL_GENERAL_SETTINGS** - Theory-specific additions (if defined)
3. **User-provided general settings** - From configuration
4. **Theory.DEFAULT_EXAMPLE_SETTINGS** - Theory example defaults
5. **User-provided example settings** - From BuildExample
6. **Command-line flags** - Highest priority

## Implementation Plan - Simple 3-Phase Approach

### Phase 1: Centralize General Settings (1 hour)

#### Task 1.1: Add General Settings to SemanticDefaults
**File**: `/src/model_checker/models/semantic.py`

```python
class SemanticDefaults:
    """Base class providing fundamental semantic operations."""
    
    # General settings used by all theories
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "sequential": False,
        "maximize": False
    }
    
    # Rest of class unchanged...
```

#### Task 1.2: Update SettingsManager to Use Base Settings
**File**: `/src/model_checker/settings/settings.py`

Update the initialization to check base class first:

```python
def __init__(self, semantic_theory: Dict[str, Any], ...):
    # Get semantics class
    semantics_class = semantic_theory.get("semantics")
    
    # Start with base class general settings
    self.DEFAULT_GENERAL_SETTINGS = SemanticDefaults.DEFAULT_GENERAL_SETTINGS.copy()
    
    # Augment with any theory-specific general settings
    if hasattr(semantics_class, 'ADDITIONAL_GENERAL_SETTINGS'):
        self.DEFAULT_GENERAL_SETTINGS.update(
            semantics_class.ADDITIONAL_GENERAL_SETTINGS
        )
    
    # Get example settings from theory
    self.DEFAULT_EXAMPLE_SETTINGS = semantics_class.DEFAULT_EXAMPLE_SETTINGS
```

### Phase 2: Remove Duplication from Theories (30 minutes)

#### Task 2.1: Update Each Theory

Remove `DEFAULT_GENERAL_SETTINGS` from each theory, optionally add `ADDITIONAL_GENERAL_SETTINGS` if needed:

**Bimodal** (`/src/model_checker/theory_lib/bimodal/semantic.py`):
```python
class BimodalSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 1,
        'expectation': True,
        'iterate': 1,
    }
    
    # Optional: Add bimodal-specific general settings
    ADDITIONAL_GENERAL_SETTINGS = {
        "align_vertically": False  # Display option for temporal models
    }
    
    # Remove DEFAULT_GENERAL_SETTINGS entirely
```

**Exclusion** (`/src/model_checker/theory_lib/exclusion/semantic.py`):
```python
class ExclusionSemantics(LogosSemantics):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'max_time': 1,
        'iterate': 1,
        'expectation': None,
    }
    
    # No additional general settings needed
    # Remove DEFAULT_GENERAL_SETTINGS entirely
```

**Imposition** (`/src/model_checker/theory_lib/imposition/semantic.py`):
```python
class ImpositionSemantics(LogosSemantics):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'max_time': 1,
        'iterate': 1,
        'expectation': None,
    }
    
    # No additional general settings needed
    # Remove DEFAULT_GENERAL_SETTINGS entirely
```

**Logos** (`/src/model_checker/theory_lib/logos/semantic.py`):
```python
class LogosSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10,
        'iterate': False,
        'expectation': None,
    }
    
    # No additional general settings needed for base logos
    # Remove DEFAULT_GENERAL_SETTINGS entirely
```

### Phase 3: Testing and Documentation (1.5 hours)

#### Task 3.1: Test with Dual Testing Protocol

1. **Test Runner Validation**:
```bash
# Run existing tests to ensure no regressions
./run_tests.py --all

# Specifically test settings functionality
./run_tests.py --package settings -v
```

2. **CLI Validation** (critical for detecting issues):
```bash
# Test each theory multiple times
for theory in logos bimodal exclusion imposition; do
    echo "Testing $theory..."
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
done

# Test with various flags to ensure settings work
./dev_cli.py --print-z3 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py --sequential src/model_checker/theory_lib/bimodal/examples.py
```

#### Task 3.2: Update Documentation

**Settings Package README** (`/src/model_checker/settings/README.md`):
- Document that general settings live in SemanticDefaults
- Explain optional ADDITIONAL_GENERAL_SETTINGS pattern
- Update examples to show the simpler architecture

**Architecture Documentation** (`/Code/docs/ARCHITECTURE.md`):
- Update settings flow to show base class inheritance
- Simplify the settings priority diagram

## Testing Strategy

### Unit Tests

Create simple tests that verify the new structure:

```python
# test_settings_inheritance.py
def test_general_settings_from_base_class():
    """Verify general settings come from SemanticDefaults."""
    from model_checker.models.semantic import SemanticDefaults
    
    assert hasattr(SemanticDefaults, 'DEFAULT_GENERAL_SETTINGS')
    assert 'print_z3' in SemanticDefaults.DEFAULT_GENERAL_SETTINGS
    assert 'sequential' in SemanticDefaults.DEFAULT_GENERAL_SETTINGS

def test_theory_can_augment_general_settings():
    """Verify theories can add to general settings."""
    from model_checker.theory_lib.bimodal import BimodalSemantics
    from model_checker.settings import SettingsManager
    
    # BimodalSemantics should have ADDITIONAL_GENERAL_SETTINGS
    if hasattr(BimodalSemantics, 'ADDITIONAL_GENERAL_SETTINGS'):
        assert 'align_vertically' in BimodalSemantics.ADDITIONAL_GENERAL_SETTINGS

def test_no_duplicate_general_settings():
    """Verify theories don't duplicate general settings."""
    theories = ['bimodal', 'exclusion', 'imposition', 'logos']
    
    for theory_name in theories:
        theory = get_theory(theory_name)
        semantics = theory['semantics']
        # Should NOT have DEFAULT_GENERAL_SETTINGS
        assert not hasattr(semantics, 'DEFAULT_GENERAL_SETTINGS') or \
               semantics.DEFAULT_GENERAL_SETTINGS is SemanticDefaults.DEFAULT_GENERAL_SETTINGS
```

### Integration Tests

Ensure the complete pipeline works:

```python
def test_settings_flow_with_inheritance():
    """Test settings flow from base class through to execution."""
    from model_checker import BuildExample
    
    # Test with different theories
    for theory_name in ['logos', 'bimodal', 'exclusion', 'imposition']:
        theory = get_theory(theory_name)
        example = BuildExample("TEST", theory, settings={'N': 3})
        
        # Should have access to general settings
        assert hasattr(example, 'general_settings')
        assert 'print_z3' in example.general_settings
```

## Benefits of This Approach

### Simplicity
- **Single Source of Truth**: General settings defined in one place (SemanticDefaults)
- **Clear Inheritance**: Natural Python class inheritance, no complex patterns
- **Easy to Understand**: New developers can immediately see where settings come from

### Intelligibility  
- **Obvious Structure**: Base class has base settings, theories add their own
- **No Magic**: Direct attribute access, no hidden behavior
- **Clear Augmentation**: ADDITIONAL_GENERAL_SETTINGS clearly shows theory additions

### Maintainability
- **Zero Duplication**: General settings defined once
- **Easy Updates**: Change general settings in one place
- **Flexible Extension**: Theories can easily add settings without modifying base
- **Backward Compatible**: Existing code continues to work

## Migration Path

This refactoring requires minimal changes:

1. **Add DEFAULT_GENERAL_SETTINGS to SemanticDefaults** (new addition)
2. **Remove DEFAULT_GENERAL_SETTINGS from each theory** (simple deletion)
3. **Optionally add ADDITIONAL_GENERAL_SETTINGS where needed** (only bimodal)
4. **Update SettingsManager to check base class first** (small logic change)

No API changes, no breaking changes, just cleaner organization.

## Success Criteria

### Phase 1 Complete When:
- [ ] SemanticDefaults has DEFAULT_GENERAL_SETTINGS defined
- [ ] SettingsManager correctly loads from base class
- [ ] All existing tests pass

### Phase 2 Complete When:
- [ ] All theories have DEFAULT_GENERAL_SETTINGS removed
- [ ] Bimodal has ADDITIONAL_GENERAL_SETTINGS for align_vertically
- [ ] No duplicate general settings remain

### Phase 3 Complete When:
- [ ] All tests pass (./run_tests.py --all)
- [ ] CLI validation successful for all theories
- [ ] Documentation updated to reflect new structure
- [ ] No performance regressions

## Risk Assessment

### Low Risk
- **Simple Changes**: Mostly deletions and one addition
- **Natural Pattern**: Uses standard Python inheritance
- **Easy Rollback**: Can revert if issues arise
- **Well Tested**: Comprehensive test coverage

### Mitigation
- **Incremental Implementation**: Do one theory at a time
- **Continuous Testing**: Run tests after each change
- **Keep It Simple**: Resist adding complexity

## Conclusion

This approach achieves the goal of abstracting general settings with:
- **Minimal Code Changes**: ~250 lines removed, ~20 lines added
- **Maximum Simplicity**: Uses basic Python inheritance
- **Clear Architecture**: Anyone can understand where settings come from
- **Future Flexibility**: Easy to extend without breaking existing code

The result is a cleaner, more maintainable codebase that follows the principle of "make the easy things easy and the hard things possible."

---

**Document Status**: Final  
**Review Required**: Yes  
**Implementation Ready**: Upon approval  
**Estimated Effort**: 3 hours total  
**Risk Level**: Low (simple changes, comprehensive testing)