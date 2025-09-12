# Plan 092: Settings Package Refactor

**Status:** Pending  
**Priority:** P2 (High - Core Configuration Management)  
**Timeline:** 3 days  
**Compliance Score:** 65/100 → 90/100

## Executive Summary

The settings package manages configuration and validation for all ModelChecker theories and components. Currently at 65% compliance with only 16% type hint coverage (no decorators present), this refactor will bring it to 90% compliance through comprehensive type hints, enhanced validation, and improved error handling.

## Current State Analysis

### Package Structure
```
settings/
├── __init__.py              # Package exports
├── base.py                  # Base settings classes
├── defaults.py              # Default configuration values
├── manager.py               # Settings management and validation
├── registry.py              # Theory settings registry
├── validators.py            # Setting validation functions
├── utils.py                 # Utility functions
└── tests/                   # Test suite (5 test files)
```

### Compliance Metrics
- **Files:** 8 Python files
- **Functions/Classes:** 61 total
- **Type Hints:** 10/61 (16%) ❌
- **Decorators:** 0 ✅
- **Test Coverage:** 5 test files (moderate)
- **Documentation:** Basic README
- **TODO/FIXME:** Check needed

### Positive Aspects
- No decorators (already compliant)
- Clean module structure
- Good separation of concerns
- Validation logic in place

### Critical Issues
1. **Very low type coverage** - Only 16% of functions typed
2. **No types.py module** - Missing type definitions
3. **Limited error handling** - Need custom exceptions
4. **Validation complexity** - Complex validation logic needs typing

## Implementation Strategy

### Phase 1: Type System Foundation (Day 1 Morning)

#### Create settings/types.py
```python
"""Type definitions for settings package."""

from typing import (
    TYPE_CHECKING, Any, Dict, List, Optional, Set, Tuple, Union,
    Protocol, TypeVar, Callable, Literal, TypedDict
)
from enum import Enum

if TYPE_CHECKING:
    from ..models import ModelStructure

# Type variables
T = TypeVar('T')
V = TypeVar('V')  # Value type

# Core types
SettingName = str
SettingValue = Any
SettingsDict = Dict[SettingName, SettingValue]
ValidationResult = Tuple[bool, Optional[str]]

# Setting types
class SettingType(Enum):
    """Types of settings."""
    INTEGER = "integer"
    FLOAT = "float"
    BOOLEAN = "boolean"
    STRING = "string"
    LIST = "list"
    DICT = "dict"
    ENUM = "enum"

class SettingScope(Enum):
    """Scope of setting application."""
    GLOBAL = "global"
    THEORY = "theory"
    EXAMPLE = "example"
    SESSION = "session"

# Setting definition
class SettingDefinition:
    """Definition of a setting."""
    
    def __init__(
        self,
        name: SettingName,
        setting_type: SettingType,
        default: SettingValue,
        description: str,
        scope: SettingScope = SettingScope.THEORY,
        validator: Optional[Callable[[Any], ValidationResult]] = None,
        choices: Optional[List[Any]] = None,
        min_value: Optional[Union[int, float]] = None,
        max_value: Optional[Union[int, float]] = None
    ) -> None:
        """Initialize setting definition.
        
        Args:
            name: Setting name
            setting_type: Type of setting
            default: Default value
            description: Human-readable description
            scope: Application scope
            validator: Optional validation function
            choices: Valid choices for enum type
            min_value: Minimum value for numeric types
            max_value: Maximum value for numeric types
        """
        self.name = name
        self.setting_type = setting_type
        self.default = default
        self.description = description
        self.scope = scope
        self.validator = validator
        self.choices = choices
        self.min_value = min_value
        self.max_value = max_value

# Configuration schema
class TheoryConfig(TypedDict, total=False):
    """Configuration for a theory."""
    N: int  # Number of atomic states
    max_models: int
    timeout: int
    enable_reasoning: bool
    contingent: List[str]
    non_contingent: List[str]
    verification_conditions: Dict[str, Any]

# Validation types
Validator = Callable[[SettingValue], ValidationResult]
Transformer = Callable[[SettingValue], SettingValue]
SettingConstraint = Callable[[SettingValue, SettingsDict], bool]

# Registry types
TheoryName = str
SettingsRegistry = Dict[TheoryName, Dict[SettingName, SettingDefinition]]

# Protocol definitions
class SettingsManager(Protocol):
    """Protocol for settings managers."""
    
    def get_setting(self, name: SettingName) -> SettingValue:
        """Get setting value."""
        ...
    
    def set_setting(
        self,
        name: SettingName,
        value: SettingValue
    ) -> None:
        """Set setting value."""
        ...
    
    def validate_settings(
        self,
        settings: SettingsDict
    ) -> ValidationResult:
        """Validate settings dictionary."""
        ...

class SettingsValidator(Protocol):
    """Protocol for settings validators."""
    
    def validate(
        self,
        value: SettingValue,
        definition: SettingDefinition
    ) -> ValidationResult:
        """Validate setting value."""
        ...

# Result types
LoadResult = Tuple[bool, Optional[SettingsDict], Optional[str]]
SaveResult = Tuple[bool, Optional[str]]
MergeResult = Tuple[SettingsDict, List[str]]  # Merged dict, conflicts

# Callback types
SettingChangeCallback = Callable[[SettingName, SettingValue, SettingValue], None]
ValidationCallback = Callable[[SettingName, bool, Optional[str]], None]
```

### Phase 2: Add Type Hints to Core Modules (Day 1 Afternoon)

#### Update base.py
```python
# base.py with type hints
from typing import Optional, Dict, Any, List, Set
from .types import (
    SettingName, SettingValue, SettingsDict,
    SettingDefinition, ValidationResult, SettingScope
)

class BaseSettings:
    """Base class for settings management."""
    
    def __init__(
        self,
        defaults: Optional[SettingsDict] = None
    ) -> None:
        """Initialize with optional defaults.
        
        Args:
            defaults: Default settings values
        """
        self._settings: SettingsDict = defaults or {}
        self._definitions: Dict[SettingName, SettingDefinition] = {}
        self._validators: Dict[SettingName, List[Validator]] = {}
    
    def register_setting(
        self,
        definition: SettingDefinition
    ) -> None:
        """Register a setting definition.
        
        Args:
            definition: Setting definition to register
        """
        self._definitions[definition.name] = definition
        if definition.default is not None:
            self._settings.setdefault(definition.name, definition.default)
    
    def get(
        self,
        name: SettingName,
        default: Optional[SettingValue] = None
    ) -> SettingValue:
        """Get setting value.
        
        Args:
            name: Setting name
            default: Default if not found
            
        Returns:
            Setting value or default
        """
        return self._settings.get(name, default)
    
    def set(
        self,
        name: SettingName,
        value: SettingValue
    ) -> None:
        """Set setting value.
        
        Args:
            name: Setting name
            value: Setting value
            
        Raises:
            SettingsError: If validation fails
        """
        # Validate before setting
        is_valid, error = self._validate_setting(name, value)
        if not is_valid:
            raise SettingsError(f"Invalid value for {name}: {error}")
        
        self._settings[name] = value
```

#### Update manager.py
```python
# manager.py with type hints
from typing import Dict, List, Optional, Any, Tuple
from .types import (
    TheoryName, SettingsDict, SettingName, SettingValue,
    ValidationResult, TheoryConfig, SettingsRegistry
)
from .base import BaseSettings

class SettingsManager:
    """Manages settings for all theories."""
    
    def __init__(self) -> None:
        """Initialize settings manager."""
        self._theory_settings: Dict[TheoryName, BaseSettings] = {}
        self._global_settings: BaseSettings = BaseSettings()
        self._registry: SettingsRegistry = {}
    
    def register_theory(
        self,
        theory_name: TheoryName,
        settings_definitions: List[SettingDefinition]
    ) -> None:
        """Register theory with its settings.
        
        Args:
            theory_name: Name of theory
            settings_definitions: List of setting definitions
        """
        theory_settings = BaseSettings()
        for definition in settings_definitions:
            theory_settings.register_setting(definition)
        
        self._theory_settings[theory_name] = theory_settings
        self._registry[theory_name] = {
            d.name: d for d in settings_definitions
        }
    
    def get_theory_settings(
        self,
        theory_name: TheoryName
    ) -> Optional[SettingsDict]:
        """Get all settings for a theory.
        
        Args:
            theory_name: Name of theory
            
        Returns:
            Settings dictionary or None
        """
        if theory_name in self._theory_settings:
            return self._theory_settings[theory_name]._settings.copy()
        return None
    
    def validate_theory_config(
        self,
        theory_name: TheoryName,
        config: TheoryConfig
    ) -> ValidationResult:
        """Validate theory configuration.
        
        Args:
            theory_name: Name of theory
            config: Configuration to validate
            
        Returns:
            Tuple of (is_valid, error_message)
        """
        # Implementation
        pass
```

### Phase 3: Add Type Hints to Remaining Modules (Day 2)

#### Update validators.py
```python
# validators.py with type hints
from typing import Any, List, Optional, Union
from .types import ValidationResult, SettingValue, SettingType

def validate_integer(
    value: Any,
    min_value: Optional[int] = None,
    max_value: Optional[int] = None
) -> ValidationResult:
    """Validate integer value.
    
    Args:
        value: Value to validate
        min_value: Optional minimum
        max_value: Optional maximum
        
    Returns:
        Validation result tuple
    """
    if not isinstance(value, int):
        return False, f"Expected integer, got {type(value).__name__}"
    
    if min_value is not None and value < min_value:
        return False, f"Value {value} below minimum {min_value}"
    
    if max_value is not None and value > max_value:
        return False, f"Value {value} above maximum {max_value}"
    
    return True, None

def validate_enum(
    value: Any,
    choices: List[Any]
) -> ValidationResult:
    """Validate enum value.
    
    Args:
        value: Value to validate
        choices: Valid choices
        
    Returns:
        Validation result tuple
    """
    if value not in choices:
        return False, f"Value must be one of {choices}"
    return True, None

def validate_list(
    value: Any,
    item_validator: Optional[Validator] = None,
    min_length: Optional[int] = None,
    max_length: Optional[int] = None
) -> ValidationResult:
    """Validate list value.
    
    Args:
        value: Value to validate
        item_validator: Optional validator for items
        min_length: Minimum list length
        max_length: Maximum list length
        
    Returns:
        Validation result tuple
    """
    if not isinstance(value, list):
        return False, f"Expected list, got {type(value).__name__}"
    
    # Length validation
    if min_length and len(value) < min_length:
        return False, f"List too short (min {min_length})"
    
    if max_length and len(value) > max_length:
        return False, f"List too long (max {max_length})"
    
    # Item validation
    if item_validator:
        for i, item in enumerate(value):
            valid, error = item_validator(item)
            if not valid:
                return False, f"Item {i}: {error}"
    
    return True, None
```

### Phase 4: Error Handling Enhancement (Day 2 Afternoon)

#### Create settings/errors.py
```python
"""Error definitions for settings package."""

from typing import Optional, Dict, Any
from .types import SettingName, SettingValue

class SettingsError(Exception):
    """Base exception for settings package."""
    
    def __init__(
        self,
        message: str,
        setting_name: Optional[SettingName] = None,
        value: Optional[SettingValue] = None
    ) -> None:
        super().__init__(message)
        self.setting_name = setting_name
        self.value = value

class ValidationError(SettingsError):
    """Setting validation error."""
    pass

class RegistrationError(SettingsError):
    """Setting registration error."""
    pass

class TheoryNotFoundError(SettingsError):
    """Theory not found in registry."""
    pass

class SettingNotFoundError(SettingsError):
    """Setting not found."""
    pass
```

### Phase 5: Testing and Documentation (Day 3)

#### Add Missing Tests
```python
# tests/test_types.py
def test_setting_definition_creation():
    """Test SettingDefinition initialization."""

def test_theory_config_structure():
    """Test TheoryConfig TypedDict."""

# tests/test_validation.py
def test_integer_validation_bounds():
    """Test integer validation with bounds."""

def test_enum_validation():
    """Test enum choice validation."""

def test_list_validation_with_items():
    """Test list validation with item validator."""

# tests/test_error_handling.py
def test_validation_error_context():
    """Test error context preservation."""

def test_setting_not_found_error():
    """Test handling of missing settings."""
```

## Success Criteria

### Required Outcomes
- ✅ Type hints: 10/61 → 60/61 functions (98%+)
- ✅ types.py created with comprehensive definitions
- ✅ Error handling enhanced with custom exceptions
- ✅ All tests passing (existing + new)
- ✅ Compliance score: 65/100 → 90/100

### Quality Metrics
- No decorators (maintain current state)
- Protocol-based design where applicable
- Type-safe validation system
- Comprehensive error messages

## Risk Management

### Potential Issues
1. **Complex validation logic** - May be hard to type
2. **Dynamic settings** - Runtime-determined types
3. **Theory-specific settings** - Varying schemas

### Mitigation Strategies
1. Use Union types for complex validators
2. Use Any with runtime validation
3. Create theory-specific TypedDicts

## Implementation Checklist

### Per-Module Tasks
- [ ] Create types.py module
- [ ] Add type hints to base.py
- [ ] Add type hints to manager.py
- [ ] Add type hints to validators.py
- [ ] Add type hints to registry.py
- [ ] Add type hints to defaults.py
- [ ] Add type hints to utils.py
- [ ] Create errors.py module
- [ ] Add missing tests
- [ ] Update documentation

### Final Validation
- [ ] 98%+ type coverage
- [ ] All tests pass
- [ ] Error handling comprehensive
- [ ] Documentation updated
- [ ] mypy compatibility

## Timeline

### Day 1: Foundation
- Morning: Create types.py
- Afternoon: Type core modules (base.py, manager.py)

### Day 2: Implementation
- Morning: Type remaining modules
- Afternoon: Add error handling

### Day 3: Testing and Polish
- Morning: Add missing tests
- Afternoon: Documentation updates

## Definition of Done

1. **98%+ type hint coverage** across all modules
2. **types.py module** created and utilized
3. **Error handling** with custom exceptions
4. **All tests passing** (existing + new)
5. **Documentation** updated with examples
6. **Compliance score** ≥ 90/100
7. **No regressions** in functionality

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Code Standards](../../../maintenance/CODE_STANDARDS.md)
- [Testing Standards](../../../maintenance/TESTING_STANDARDS.md)