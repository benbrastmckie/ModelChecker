"""
Type definitions for the builder package.

This module provides type aliases and protocol definitions used throughout
the builder package to ensure type safety and clear interfaces.
"""

from typing import (
    TypeVar, Dict, List, Optional, Union, Any, Tuple,
    Callable, Protocol, TypedDict, TYPE_CHECKING
)
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

if TYPE_CHECKING:
    import z3
    from model_checker.syntactic import Syntax
    from model_checker.models import ModelDefaults
    from model_checker.output import OutputManager

# Type variables
T = TypeVar('T')
R = TypeVar('R')  # Result type

# Enums
class BuildStatus(Enum):
    """Build execution status."""
    PENDING = "pending"
    RUNNING = "running"
    SUCCESS = "success"
    FAILED = "failed"
    TIMEOUT = "timeout"

class ValidationLevel(Enum):
    """Validation strictness levels."""
    NONE = "none"
    BASIC = "basic"
    STRICT = "strict"
    PARANOID = "paranoid"

# Type aliases
ModulePath = Union[str, Path]
ExampleName = str
TheoryName = str
OperatorName = str
FormulaString = str

# Build-related types
BuildResult = Union['SuccessResult', 'FailureResult']
BuildCallback = Callable[[BuildStatus, str], None]
ValidationResult = Tuple[bool, Optional[str]]

# Collections
ExampleDict = Dict[ExampleName, List[Any]]
TheoryDict = Dict[TheoryName, Any]
OperatorDict = Dict[OperatorName, Any]
SettingsDict = Dict[str, Any]

# Typed dictionaries
class BuildConfig(TypedDict, total=False):
    """Configuration for build process."""
    module_path: str
    theory: str
    timeout: int
    parallel: bool
    cache_enabled: bool
    validation_level: str
    output_format: str
    debug: bool

class ExampleSpec(TypedDict):
    """Specification for an example."""
    premises: List[FormulaString]
    conclusions: List[FormulaString]
    settings: SettingsDict

@dataclass
class SuccessResult:
    """Successful build result."""
    status: BuildStatus
    model: Any
    stats: Dict[str, Any]
    output: str

@dataclass
class FailureResult:
    """Failed build result."""
    status: BuildStatus
    error: Exception
    traceback: str
    context: Dict[str, Any]

# Protocol definitions
class BuilderProtocol(Protocol):
    """Protocol for builder implementations."""
    
    def build(self, config: BuildConfig) -> BuildResult:
        """Build with given configuration."""
        ...
    
    def validate(self) -> ValidationResult:
        """Validate the build configuration."""
        ...

class LoaderProtocol(Protocol):
    """Protocol for module loaders."""
    
    def load_module(self, path: ModulePath) -> Any:
        """Load a module from path."""
        ...
    
    def get_examples(self, module: Any) -> ExampleDict:
        """Extract examples from module."""
        ...

class RunnerProtocol(Protocol):
    """Protocol for execution runners."""
    
    def run(self, example: ExampleSpec) -> BuildResult:
        """Run an example."""
        ...
    
    def run_batch(self, examples: List[ExampleSpec]) -> List[BuildResult]:
        """Run multiple examples."""
        ...