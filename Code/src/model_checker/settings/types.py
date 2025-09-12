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

# Common settings schemas
class GeneralSettings(TypedDict, total=False):
    """General settings schema."""
    print_impossible: bool
    print_constraints: bool
    print_z3: bool
    save_output: bool
    maximize: bool
    align_vertically: bool

class ExampleSettings(TypedDict, total=False):
    """Example settings schema."""
    N: int
    max_time: int
    model: bool
    expectation: bool
    contingent: List[str]
    non_contingent: List[str]

# Validation types
Validator = Callable[[SettingValue], ValidationResult]
Transformer = Callable[[SettingValue], SettingValue]
SettingConstraint = Callable[[SettingValue, SettingsDict], bool]

# Registry types
TheoryName = str
SettingsRegistry = Dict[TheoryName, Dict[SettingName, Any]]

# Protocol definitions
class SettingsManagerProtocol(Protocol):
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

class SettingsValidatorProtocol(Protocol):
    """Protocol for settings validators."""
    
    def validate(
        self,
        value: SettingValue,
        expected_type: type
    ) -> ValidationResult:
        """Validate setting value."""
        ...

# Module flags protocol
class ModuleFlagsProtocol(Protocol):
    """Protocol for module flags objects."""
    
    def __init__(self) -> None: ...
    
    # Common attributes that might exist
    print_impossible: Optional[bool]
    print_constraints: Optional[bool] 
    print_z3: Optional[bool]
    save_output: Optional[bool]
    maximize: Optional[bool]
    align_vertically: Optional[bool]
    
    # Internal argparse attributes
    _parsed_args: Optional[List[str]]
    _short_to_long: Optional[Dict[str, str]]

# Semantic theory protocol
class SemanticTheoryProtocol(Protocol):
    """Protocol for semantic theory dictionaries."""
    
    semantics: type
    
    def get(self, key: str) -> Any: ...

# Result types
LoadResult = Tuple[bool, Optional[SettingsDict], Optional[str]]
SaveResult = Tuple[bool, Optional[str]]
MergeResult = Tuple[SettingsDict, List[str]]  # Merged dict, conflicts

# Callback types
SettingChangeCallback = Callable[[SettingName, SettingValue, SettingValue], None]
ValidationCallback = Callable[[SettingName, bool, Optional[str]], None]

# Flag extraction types
FlagName = str
FlagValue = Any
FlagsDict = Dict[FlagName, FlagValue]
UserProvidedFlags = Set[FlagName]

# Environment variable types
EnvironmentVariable = str
EnvironmentValue = str
EnvironmentDict = Dict[EnvironmentVariable, EnvironmentValue]