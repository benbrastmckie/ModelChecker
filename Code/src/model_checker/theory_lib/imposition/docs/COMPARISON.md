# Imposition Theory Modernization & Comparison Implementation Plan

## Executive Summary

This document outlines a comprehensive plan to modernize the imposition theory to follow the conventions established by the logos theory, making it a minimal offshoot that reuses logos infrastructure while maintaining its unique semantic features. The goal is to enable theory comparison between Kit Fine's imposition semantics and the Brast-McKie hyperintensional semantics implemented in logos.

## Current State Analysis

### Imposition Theory Status
- **Dependencies**: Currently depends on the deprecated `default/` theory for basic classes
- **Structure**: Uses older ModelChecker patterns and conventions
- **Classes**: Missing its own Proposition and ModelStructure implementations
- **Operators**: Has its own operators (`\imposition`, `\could`) but no modular structure

### Logos Theory Architecture (Target Pattern)
- **Modular Design**: Subtheory-based architecture with dynamic operator loading
- **Classes**: Defines LogosSemantics, LogosProposition, LogosModelStructure
- **Registry**: Uses LogosOperatorRegistry for dynamic operator management
- **Reusability**: Designed for extension and composition

### Comparison Functionality
- **Status**: Fully implemented in `builder/module.py`
- **Issue**: Pickle errors due to module references in operator dictionaries
- **Requirements**: Theories must provide picklable operator dictionaries

## Modernization Goals

### 1. Independent Inheriting Theory Philosophy
The imposition theory should:
- **Remain a separate, independent theory** (not a logos subtheory)
- **Inherit from logos base classes** for code reuse and consistency
- **Maintain its own identity** as Kit Fine's imposition semantics
- **Be developed primarily for comparison** with logos/Brast-McKie semantics
- Only override/extend what's necessary for imposition-specific semantics
- Follow logos patterns for consistency while remaining distinct

### 2. Specific Objectives
- Replace dependency on `default/` with `logos/`
- **Keep imposition as a standalone theory** that inherits logos infrastructure
- Enable seamless theory comparison between two independent theories
- Maintain clear separation between the theories while sharing base functionality
- Follow modern ModelChecker patterns
- Preserve the ability to develop and evolve imposition theory independently

## Implementation Plan

### Phase 1: Refactor as Independent Inheriting Theory

#### 1.1 Create ImpositionSemantics Inheriting from Logos
```python
# semantic.py
from model_checker.theory_lib.logos import LogosSemantics

class ImpositionSemantics(LogosSemantics):
    """
    Kit Fine's imposition semantics as an independent theory.
    
    Inherits logos base functionality for consistency and code reuse,
    while implementing Fine's distinctive counterfactual semantics
    through the imposition operation. Developed as a separate theory
    for comparison with Brast-McKie hyperintensional semantics.
    """
    
    def __init__(self, settings):
        super().__init__(settings)
        # Add imposition-specific initialization
        self._define_imposition_operation()
    
    def _define_imposition_operation(self):
        """Define the imposition operation as a Z3 function."""
        # Implementation of Fine's imposition operation
        pass
```

#### 1.2 Use Logos Classes Directly
```python
# __init__.py
from model_checker.theory_lib.logos import (
    LogosProposition as Proposition,
    LogosModelStructure as ModelStructure,
)
from .semantic import ImpositionSemantics
from .operators import imposition_operators

# Export with imposition-specific names
__all__ = [
    'ImpositionSemantics',
    'Proposition',  # Direct reuse of logos
    'ModelStructure',  # Direct reuse of logos
    'imposition_operators',
]
```

### Phase 2: Integrate with Logos Operator System

#### 2.1 Create Imposition Subtheory Structure
```
imposition/
├── __init__.py
├── semantic.py
├── operators.py          # Refactor to follow logos pattern
├── subtheories/         # Optional: for future extensions
│   └── counterfactual/
│       ├── __init__.py
│       └── operators.py  # Imposition-specific operators
└── examples.py
```

#### 2.2 Refactor Operators to Logos Pattern
```python
# operators.py
from model_checker.theory_lib.logos.subtheories.extensional.operators import (
    get_extensional_operators
)
from model_checker.theory_lib.logos.subtheories.modal.operators import (
    get_modal_operators
)

def get_imposition_operators():
    """Get imposition-specific operators."""
    return {
        '\\imposition': ImpositionOperator,
        '\\could': CouldOperator,
    }

def get_all_operators():
    """Get all operators including inherited ones."""
    operators = {}
    operators.update(get_extensional_operators())  # Inherit basic operators
    operators.update(get_modal_operators())        # Inherit modal operators
    operators.update(get_imposition_operators())   # Add imposition-specific
    return operators

# For backward compatibility
imposition_operators = get_all_operators()
```

### Phase 3: Fix Theory Comparison

#### 3.1 Update examples.py
```python
# Import components
from .semantic import ImpositionSemantics
from .operators import get_all_operators
from model_checker.theory_lib.logos import (
    LogosSemantics,
    LogosProposition as Proposition,
    LogosModelStructure as ModelStructure,
    LogosOperatorRegistry,
)

# Create operator registry for logos theory
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

# Define theories with static operator dictionaries
imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": get_all_operators(),  # Returns static dict
    "dictionary": {}  # No translation needed
}

logos_theory = {
    "semantics": LogosSemantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": logos_registry.get_operators(),  # Returns static dict
    "dictionary": {}  # No translation needed
}

semantic_theories = {
    "Fine": imposition_theory,
    "Brast-McKie": logos_theory,
}
```

### Phase 4: Theory Comparison Features

#### 4.1 Maintain Theory Independence
Keep imposition as a separate theory while ensuring compatibility:
```python
# Imposition remains its own theory
from model_checker.theory_lib.imposition import ImpositionSemantics

# Not loaded as a subtheory, but as an independent comparison target
```

#### 4.2 Create Operator Translation Mappings
If operator names differ between theories:
```python
imposition_to_logos = {
    '\\imposition': '\\boxright',  # If mapping needed
    '\\could': '\\diamondright',    # If mapping needed
}
```

#### 4.3 Future Comparison Extensions
- Add more theories for multi-way comparison
- Develop theory-specific benchmarks
- Create comparison visualizations

## Benefits of This Approach

### 1. Code Reuse
- Leverages all logos infrastructure
- No duplication of Proposition/ModelStructure classes
- Inherits logos improvements automatically

### 2. Maintainability
- Single source of truth for base functionality
- Clear separation of imposition-specific features
- Easier to update and debug

### 3. Extensibility
- Can easily add new imposition-specific features
- Compatible with logos subtheory system
- Future-proof architecture

### 4. Theory Comparison
- Clean implementation without pickle issues
- Standardized operator dictionaries
- Easy to add more theories for comparison

## Implementation Steps

1. **Update imports** in imposition to use logos instead of default
2. **Refactor ImpositionSemantics** to extend LogosSemantics
3. **Reorganize operators** to follow logos patterns
4. **Update examples.py** with proper theory definitions
5. **Test theory comparison** functionality
6. **Document changes** and update docstrings

## Testing Strategy

### Unit Tests
- Verify imposition operations work correctly
- Check inheritance from logos works properly
- Test operator compatibility

### Integration Tests
- Run all imposition examples
- Test theory comparison with various examples
- Verify no regression in functionality

### Comparison Tests
```bash
# Test individual theories
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py

# Test comparison mode
./dev_cli.py -m src/model_checker/theory_lib/imposition/examples.py

# Verify both theories handle examples correctly
```

## Migration Checklist

- [ ] Remove dependency on default theory
- [ ] Update ImpositionSemantics to extend LogosSemantics
- [ ] Import Proposition and ModelStructure from logos
- [ ] Refactor operators to return static dictionaries
- [ ] Update examples.py with both theory definitions
- [ ] Test basic functionality
- [ ] Test comparison mode
- [ ] Update documentation
- [ ] Clean up unused imports

## Conclusion

This modernization plan transforms the imposition theory into a modern, independent theory that inherits from logos for consistency and code reuse, while maintaining its distinct identity as Kit Fine's imposition semantics. By following logos conventions and reusing its infrastructure, we achieve a more maintainable and comparison-ready implementation that:

1. **Preserves theoretical independence** - Imposition remains a separate theory, not a logos subtheory
2. **Enables meaningful comparison** - Two independent theories can be compared side-by-side
3. **Maximizes code reuse** - Inherits logos infrastructure without sacrificing autonomy
4. **Maintains Fine's unique semantics** - The distinctive features of imposition theory are preserved

This approach provides the best of both worlds: modern implementation practices with theoretical independence, perfect for comparative analysis between Kit Fine's imposition semantics and the Brast-McKie hyperintensional semantics.