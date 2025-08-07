# Builder Module Theory-Agnostic Refactoring Plan

**Plan ID**: 016  
**Created**: 2025-08-07  
**Status**: Active
**Priority**: High - Architectural Violation
**Author**: AI Assistant

## Problem Statement

The `builder/module.py` file violates the Theory Agnostic Principle by containing hardcoded mappings between theory display names and module names:

```python
theory_display_to_module = {
    "Brast-McKie": "logos",
    "Exclusion": "exclusion", 
    "unilateral_theory": "exclusion",
    "BernardChampollion": "exclusion",
    "Imposition": "imposition",
    "Fine": "imposition",
    "Bimodal": "bimodal",
    "Logos": "logos"
}
```

This creates several problems:
1. **Maintenance Burden**: New theory names require code changes to builder
2. **Theory Coupling**: Framework component knows about specific theories
3. **Scalability**: Hardcoded list doesn't scale as theories evolve
4. **Inconsistency**: Theory names scattered across codebase

## Root Cause Analysis

The issue arises because:
- Theory modules use display names (e.g., "Brast-McKie", "BernardChampollion") in their `semantic_theories` dictionaries
- The iterator functionality needs to import the correct theory module
- No standardized way for theories to declare their module identity

## Proposed Solution

### Option 1: Theory Self-Registration (Recommended)

Each theory module provides a `THEORY_MODULE_NAME` constant and `get_theory_module_name()` function:

```python
# In exclusion/__init__.py or exclusion/meta.py
THEORY_MODULE_NAME = "exclusion"

def get_theory_module_name():
    """Return the module name for dynamic imports."""
    return THEORY_MODULE_NAME

# Register display name mappings within the theory
DISPLAY_NAME_MAPPINGS = {
    "BernardChampollion": "exclusion",
    "unilateral_theory": "exclusion",
    "Exclusion": "exclusion"
}
```

### Option 2: Theory Metadata API

Extend the existing `get_theory()` API to include module metadata:

```python
def get_theory():
    """Return theory components including module metadata."""
    return {
        "module_name": "exclusion",
        "display_names": ["BernardChampollion", "unilateral_theory", "Exclusion"],
        "semantics": ExclusionSemantics,
        "proposition": ExclusionProposition,
        "model": ExclusionModelStructure,
        "operators": exclusion_operators
    }
```

### Option 3: Dynamic Discovery

Use the theory name from the semantic_theories dictionary to find the module:

```python
def find_theory_module(theory_name, semantic_theories):
    """Dynamically find the theory module for a given theory name."""
    # Get the theory definition
    theory_def = semantic_theories.get(theory_name)
    if not theory_def:
        return None
    
    # Extract module from semantics class
    semantics_class = theory_def.get("semantics")
    if semantics_class:
        module_name = semantics_class.__module__
        # Extract theory name from full module path
        # e.g., "model_checker.theory_lib.exclusion.semantic" -> "exclusion"
        parts = module_name.split('.')
        if len(parts) >= 3 and parts[1] == "theory_lib":
            return parts[2]
    
    return None
```

## Implementation Plan

### Phase 1: Add Theory Module Metadata (Day 1)

1. **Update theory modules** to include module name metadata:
   - `exclusion/__init__.py` or `exclusion/meta.py`
   - `imposition/__init__.py` or `imposition/meta.py`
   - `logos/__init__.py` or `logos/meta.py`
   - `bimodal/__init__.py` or `bimodal/meta.py`

2. **Create standard API** for module name retrieval

3. **Test each theory** can report its module name

### Phase 2: Refactor Builder Module (Day 2)

1. **Replace hardcoded mapping** with dynamic discovery:
   ```python
   # OLD
   module_name = theory_display_to_module.get(theory_name, theory_name.lower())
   
   # NEW
   module_name = self._discover_theory_module(theory_name, semantic_theories)
   ```

2. **Implement discovery method** that:
   - First checks if theory_name is already a module name
   - Then tries dynamic discovery from semantic_theories
   - Falls back to theory_name.lower() as last resort

3. **Add comprehensive error handling** with helpful messages

### Phase 3: Validation and Testing (Day 3)

1. **Test all theory examples** still work:
   ```bash
   ./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
   ./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
   ```

2. **Test iterate functionality** for all theories

3. **Add unit tests** for theory module discovery

## Migration Strategy

1. **Implement new system** alongside old mapping
2. **Deprecation warnings** when old mapping is used
3. **Remove old mapping** after validation

## Success Criteria

1. ✅ No hardcoded theory names in builder/module.py
2. ✅ All theory examples run successfully
3. ✅ Iterate functionality works for all theories
4. ✅ New theories can be added without modifying builder
5. ✅ Clear error messages for missing/invalid theories

## Risk Assessment

**Low Risk**: Changes are localized and can be tested incrementally

**Mitigation**: Keep fallback logic during transition period

## Follow-up Tasks

1. Document the theory module API in theory architecture docs
2. Update theory creation templates to include module metadata
3. Consider similar refactoring for other theory-specific code