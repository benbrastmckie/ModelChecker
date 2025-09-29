# Settings Management Architecture

[← Back to Architecture](README.md) | [Pipeline →](PIPELINE.md) | [Builder →](BUILDER.md) | [Technical Implementation →](../../Code/src/model_checker/settings/README.md)

## Overview

The settings management system provides a sophisticated configuration hierarchy that allows fine-grained control over ModelChecker behavior while maintaining sensible defaults. Settings can be specified at multiple levels with clear precedence rules, enabling both simple usage and advanced customization.

## Settings Hierarchy

The ModelChecker uses a five-level settings hierarchy with clear precedence:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              SETTINGS PRECEDENCE HIERARCHY (High to Low Priority)           │
└─────────────────────────────────────────────────────────────────────────────┘

┌──────────────────────┐
│   CLI Arguments      │  [1] HIGHEST PRIORITY
│ • --verbose          │  Overrides all other settings
│ • --contingent       │
│ • --save             │
└──────────┬───────────┘
           │
           ▼
┌──────────────────────┐
│   Example File       │  [2] Problem-specific settings
│ • Problem settings   │  Override user/theory/system
│ • Test requirements  │
└──────────┬───────────┘
           │
           ▼
┌──────────────────────┐
│   User Config        │  [3] Personal preferences
│ • ~/.modelchecker    │  Override theory/system
│ • Personal defaults  │
└──────────┬───────────┘
           │
           ▼
┌──────────────────────┐
│   Theory Defaults    │  [4] Theory-specific
│ • Logos: N=16        │  Override system only
│ • Theory constraints │
└──────────┬───────────┘
           │
           ▼
┌──────────────────────┐
│   System Defaults    │  [5] LOWEST PRIORITY  
│ • Baseline values    │  Base configuration
│ • Fallback settings  │
└──────────┬───────────┘
           │
           │  All settings flow to:
           ▼
   ┌──────────────────────────────────────────────────┐
   │                 Settings Merger                  │
   │  • Combines all sources by priority              │
   │  • Resolves conflicts (higher priority wins)     │
   │  • Validates final configuration                 │
   └───────────────────────────┬──────────────────────┘
                               │
                               ▼
                    ┌──────────────────────┐
                    │   Final Settings     │
                    │  • Validated         │
                    │  • Ready to use      │
                    └──────────────────────┘
```

### 1. CLI Arguments (Highest Priority)
Command-line flags override all other settings:
```bash
model-checker example.py --contingent --save json
```
Note: Settings like N and iterate must be set in example files, not via CLI.

### 2. Example File Settings
Settings defined in the example file:
```python
# example.py
settings = {
    'N': 4,
    'max_time': 60,
    'verbose': False
}
```

### 3. User Configuration
Personal preferences in `~/.model-checker/config.json`:
```json
{
    "default_theory": "logos",
    "verbose": true,
    "save_output": false,
    "output_format": "text"
}
```

### 4. Theory Defaults
Theory-specific example settings and optional general settings:
```python
# theory_lib/logos/semantic.py
class LogosSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10,
        'iterate': False,
    }
    # No additional general settings needed

# theory_lib/bimodal/semantic.py  
class BimodalSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 2,
        'M': 2,  # Time points
        'contingent': False,
        'max_time': 1,
    }
    
    ADDITIONAL_GENERAL_SETTINGS = {
        'align_vertically': True,  # Display option for temporal models
    }
```

### 5. System Defaults (Lowest Priority)
Framework-wide general settings defined in base class:
```python
# models/semantic.py - SemanticDefaults base class
class SemanticDefaults:
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "sequential": False,
        "maximize": False
    }
```

## Settings Architecture

### Inheritance-Based Design

The settings system uses Python class inheritance to eliminate duplication:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      SETTINGS INHERITANCE ARCHITECTURE                       │
└─────────────────────────────────────────────────────────────────────────────┘

                    ┌──────────────────────────┐
                    │    SemanticDefaults      │
                    │                          │
                    │ DEFAULT_GENERAL_SETTINGS │  ◀── Framework-wide settings
                    │ • print_impossible       │      (defined once)
                    │ • print_constraints      │
                    │ • print_z3               │
                    │ • save_output            │
                    │ • sequential             │
                    │ • maximize               │
                    └─────────────┬────────────┘
                                  │ Inherits
                    ┌─────────────┴────────────────────────┐
                    ▼                                      ▼
        ┌───────────────────────┐               ┌────────────────────┐
        │   LogosSemantics      │               │  BimodalSemantics  │
        │                       │               │                    │
        │ DEFAULT_EXAMPLE_      │               │ DEFAULT_EXAMPLE_   │
        │   SETTINGS            │               │   SETTINGS         │
        │ • N: 16               │               │ • N: 2             │
        │ • contingent: True    │               │ • M: 2             │
        │ • non_empty: True     │               │ • max_time: 1      │
        │                       │               │                    │
        │ (No additional        │               │ ADDITIONAL_GENERAL_│
        │  general settings)    │               │   SETTINGS         │
        └───────────┬───────────┘               │ • align_vertically │
                    │                           └────────────────────┘
                    │ Inherits
           ┌────────┴─────────────────────┐
           ▼                              ▼
   ┌───────────────┐            ┌────────────────────┐
   │ Exclusion     │            │ Imposition         │
   │  Semantics    │            │  Semantics         │
   │               │            │                    │
   │ DEFAULT_      │            │ DEFAULT_EXAMPLE_   │
   │  EXAMPLE_     │            │   SETTINGS         │
   │  SETTINGS     │            │                    │
   │               │            │ ADDITIONAL_        │
   │ (No additional│            │  GENERAL_SETTINGS  │
   │  general)     │            │ • derive_imposition│
   └───────────────┘            └────────────────────┘
```

### Settings Merging

The SettingsManager combines settings in this priority order:

1. **SemanticDefaults.DEFAULT_GENERAL_SETTINGS** - Base framework settings
2. **Theory.ADDITIONAL_GENERAL_SETTINGS** - Theory-specific general settings (if defined)
3. **Theory.DEFAULT_EXAMPLE_SETTINGS** - Theory-specific example defaults
4. **User settings** - From example files or configuration
5. **CLI flags** - Command-line arguments (highest priority)

## Settings Categories

### Core Settings
Essential parameters that control model checking:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          CORE SETTINGS RELATIONSHIPS                        │
└─────────────────────────────────────────────────────────────────────────────┘

                        MODEL STRUCTURE SETTINGS
┌──────────────────────────────────────────────────────────────────────────────┐
│  ┌────────────────┐        ┌────────────────┐        ┌────────────────┐      │
│  │ N: Bit-width   │        │ M: Time points │        │ theory_name    │      │
│  │ • States: 2^N  │        │ • Bimodal only │        │ • Semantics    │      │
│  │ • Required     │        │ • Optional     │        │ • Operators    │      │
│  └────────┬───────┘        └────────┬───────┘        └────────┬───────┘      │
│           └─────────────────────────┼─────────────────────────┘              │
│                                     │                                        │
│                           Affects model structure                            │
│                                     │                                        │
│                                     ▼                                        │
│                         ┌────────────────────────┐                           │
│                         │ Model Complexity       │                           │
│                         │ • Memory: O(2^N)       │                           │
│                         │ • States: 2^N × M      │                           │
│                         └────────────────────────┘                           │
└──────────────────────────────────────────────────────────────────────────────┘

                        SOLVER CONTROL SETTINGS
┌──────────────────────────────────────────────────────────────────────────────┐
│  ┌────────────────┐        ┌────────────────┐        ┌────────────────┐      │
│  │ max_time       │        │ max_models     │        │ iterate        │      │
│  │ • Z3 timeout   │        │ • Stop at N    │        │ • Find all     │      │
│  │ • Per solve    │        │ • Default: 10  │        │ • Override max │      │
│  └────────┬───────┘        └────────┬───────┘        └────────┬───────┘      │
│           └─────────────────────────┼─────────────────────────┘              │
│                                     │                                        │
│                         Controls solver behavior                             │
│                                     │                                        │
│                                     ▼                                        │
│                         ┌────────────────────────┐                           │
│                         │ Solving Strategy       │                           │
│                         │ • Timeout protection   │                           │
│                         │ • Result limits        │                           │
│                         └────────────────────────┘                           │
└──────────────────────────────────────────────────────────────────────────────┘

                    SEMANTIC CONSTRAINT SETTINGS
┌──────────────────────────────────────────────────────────────────────────────┐
│  ┌────────────────┐        ┌────────────────────┐     ┌────────────────┐     │
│  │ contingent     │        │ non_empty          │     │ disjoint       │     │
│  │ • No tautology │        │ • V⁺/V⁻ ≠ ∅        │     │ • Atoms unique │     │
│  │ • Hyperintense │        │ • Hyperintensional │     │ • Hyperintense │     │
│  └────────┬───────┘        └─────────┬──────────┘     └────────┬───────┘     │
│           └──────────────────────────┼─────────────────────────┘             │
│                                      │                                       │
│                         Semantic constraints on models                       │
│                                      │                                       │
│                                      ▼                                       │
│                         ┌────────────────────────┐                           │
│                         │ Frame Conditions       │                           │
│                         │ • Theory-specific      │                           │
│                         │ • Affects SAT/UNSAT    │                           │
│                         └────────────────────────┘                           │
└──────────────────────────────────────────────────────────────────────────────┘
```

| Setting | Type | Default | Description | Applies To |
|---------|------|---------|-------------|------------|
| **Model Structure** | | | | |
| `N` | int | Theory-specific | Bit-width for state representation (2^N states) | All |
| `M` | int | 2 | Number of time points | Bimodal |
| `theory_name` | str | "logos" | Semantic theory to use | All |
| **Solver Control** | | | | |
| `max_time` | int | Theory-specific | Z3 solver timeout in seconds | All |
| `max_models` | int | 10 | Maximum models to find | All |
| `iterate` | bool | False | Find all models (overrides max_models) | All |
| **Semantic Constraints** | | | | |
| `contingent` | bool | False | Require contingent propositions | Hyperintensional |
| `non_empty` | bool | False | Require non-empty verifier/falsifier sets | Hyperintensional |
| `non_null` | bool | False | Prevent null state as verifier/falsifier | Hyperintensional |
| `disjoint` | bool | False | Require disjoint atomic propositions | Hyperintensional |

### Output Settings
Control how results are displayed and saved:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         OUTPUT CONTROL SETTINGS                             │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────┐    ┌────────────────────┐
│   verbose           │    │  output_format     │
│ • Detail level      │    │ • text/json/md     │
│ • true/false        │    │ • jupyter (.ipynb) │
└─────────┬───────────┘    └─────────┬──────────┘
          │                          │
          ▼                          ▼
┌─────────────────────┐    ┌────────────────────┐
│  Terminal Display   │    │  Output Formatter  │
│ • Console output    │    │ • Format results   │
│ • Progress bars     │    │ • Apply styles     │
└─────────────────────┘    └────────────────────┘

┌─────────────────────┐    ┌────────────────────┐
│   save_output       │    │   output_dir       │
│ • Auto-save         │    │ • Save location    │
│ • true/false        │    │ • Default: output/ │
└──────────┬──────────┘    └─────────┬──────────┘
           │                         │
           └─────────┬───────────────┘
                     │
                     ▼
          ┌────────────────────┐
          │    File System     │
          │ • Write files      │
          │ • Create dirs      │
          └────────────────────┘
```

| Setting | Type | Default | Description |
|---------|------|---------|-------------|
| `verbose` | bool | False | Show detailed output |
| `output_format` | str | "text" | Output format type |
| `save_output` | bool | False | Automatically save results |
| `output_dir` | str | "output/" | Directory for saved files |

### Theory-Specific Settings
Settings that only apply to certain theories:

```python
# Bimodal-specific example settings
{
    'M': 2,                      # Number of time points
    'align_vertically': True,    # Display world histories vertically
}

# Imposition-specific settings  
{
    'derive_imposition': False,  # Whether to derive imposition operations
}

# Settings common to hyperintensional theories (logos, exclusion, imposition)
{
    'contingent': False,         # Make atomic propositions contingent
    'non_empty': False,          # Require non-empty verifier/falsifier sets
    'non_null': False,           # Prevent null states as verifiers/falsifiers
    'disjoint': False,           # Require disjoint subject-matters
}
```

## Settings Validation

### Validation Flow

The validation system performs multi-stage checking with comprehensive error handling and recovery:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     MULTI-STAGE VALIDATION PIPELINE                         │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────┐      ┌──────────────────┐      ┌──────────────────┐
│ Input Settings  │─────▶│ 1. Type Check    │─────▶│ 2. Range Check   │
│ • CLI args      │      │ • Convert types  │      │ • Boundaries     │
│ • Example       │      │ • TypeConvError  │      │ • RangeError     │
│ • User config   │      └──────────────────┘      └────────┬─────────┘
└─────────────────┘                                         │
                                                            ▼
┌─────────────────┐      ┌──────────────────┐      ┌──────────────────┐
│ 5. System Check │◀─────│ 4. Theory Check  │◀─────│ 3. Dependencies  │
│ • Memory limits │      │ • Compatibility  │      │ • Requirements   │
│ • Performance   │      │ • TheoryError    │      │ • Exclusions     │
└────────┬────────┘      └──────────────────┘      └──────────────────┘
         │
         ▼
┌──────────────────────────────────────────────────────────────────────┐
│                         Validation Complete?                         │
├────────────────┬──────────────────┬──────────────────────────────────┤
│    ✓ Valid     │    ✗ Error       │    ↻ Recovery                    │
│    • Ready     │    • Details     │    • Auto-fix                    │
│    • Normal    │    • Suggest     │    • Retry                       │
└────────────────┴──────────────────┴──────────────────────────────────┘
```

#### Validation Error Hierarchy

The system uses a comprehensive error hierarchy across multiple packages:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         COMPLETE ERROR HIERARCHY                            │
└─────────────────────────────────────────────────────────────────────────────┘

                              ┌─────────────┐
                              │  Exception  │
                              └──────┬──────┘
                                     │
        ┌────────────────────────────┼──────────────────────┐
        ▼                            ▼                      ▼
┌───────────────┐           ┌───────────────┐       ┌───────────────┐
│ SettingsError │           │ BuilderError  │       │  ModelError   │
│ • message     │           │ • component   │       │ • constraints │
│ • setting     │           │ • operation   │       │ • solver      │
│ • suggestion  │           │ • traceback   │       │ • structure   │
└───┬───────────┘           └───┬───────────┘       └───┬───────────┘
    │                           │                       │
    ├──ValidationError          ├──ModuleLoadError      ├──ConstraintError
    ├──TypeConversionError      ├──ValidationError      ├──SolverError
    ├──RangeError               ├──ModelCheckError      └──StructureError
    ├──MissingRequiredError     ├──ConfigurationError
    ├──UnknownSettingError      ├──TheoryNotFoundError
    └──TheoryCompatibilityError ├──ExampleNotFoundError
                                ├──IterationError
                                └──OutputError

┌─────────────────────────────────────────────────────────────────────────────┐
│                    SETTINGS ERROR DETAIL BREAKDOWN                          │
└─────────────────────────────────────────────────────────────────────────────┘

┌──────────────────┬────────────────────────┬──────────────────────────────┐
│ Error Type       │ Trigger Condition      │ Recovery Strategy            │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ ValidationError  │ General validation     │ Check constraints            │
│                  │ Dependency conflicts   │ Resolve dependencies         │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ TypeConversion   │ Invalid type           │ Auto-convert if possible     │
│                  │ Cannot cast            │ Use default value            │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ RangeError       │ Value < min            │ Clamp to min                 │
│                  │ Value > max            │ Clamp to max                 │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ MissingRequired  │ Required not provided  │ Add with default             │
│                  │ Theory requirement     │ Prompt for value             │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ UnknownSetting   │ Typo in setting name   │ Suggest similar names        │
│                  │ Deprecated setting     │ Map to new setting           │
├──────────────────┼────────────────────────┼──────────────────────────────┤
│ TheoryCompat     │ Setting not supported  │ Remove or switch theory      │
│                  │ Invalid combination    │ Adjust for compatibility     │
└──────────────────┴────────────────────────┴──────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                        ERROR ATTRIBUTES MAP                                 │
└─────────────────────────────────────────────────────────────────────────────┘

SettingsError (Base):           TypeConversionError:
├─ message: str                 ├─ value: Any
├─ setting: Optional[str]       ├─ expected_type: type
├─ suggestion: Optional[str]    └─ [inherits base attrs]
└─ context: Dict[str, Any]      
                                RangeError:
ValidationError:                ├─ value: Any  
└─ [inherits all base attrs]   ├─ min_value: Optional[Any]
                                ├─ max_value: Optional[Any]
MissingRequiredError:           └─ [inherits base attrs]
└─ [inherits all base attrs]   
                                TheoryCompatibilityError:
UnknownSettingError:            ├─ theory_name: str
├─ available_settings: List     ├─ reason: str
└─ [inherits base attrs]       └─ [inherits base attrs]
```

### Validation Rules

#### 1. Type Checking with Automatic Conversion

The validator attempts type conversion before failing:

```python
# Type checking with conversion attempt
def validate_type(setting_name, value, expected_type):
    """Validate and convert setting type."""
    if isinstance(value, expected_type):
        return value
    
    # Attempt conversion
    try:
        if expected_type == int:
            return int(value)
        elif expected_type == float:
            return float(value)
        elif expected_type == bool:
            if isinstance(value, str):
                return value.lower() in ('true', '1', 'yes')
            return bool(value)
    except (ValueError, TypeError):
        pass
    
    # Conversion failed - provide helpful error
    raise TypeConversionError(
        setting=setting_name,
        value=value,
        expected_type=expected_type,
        suggestion=f"Provide a {expected_type.__name__} value (got {type(value).__name__})"
    )

# Example usage
settings['N'] = validate_type('N', '5', int)  # Converts string '5' to int 5
```

#### 2. Range Validation with Bounds

Range validation provides specific feedback on acceptable values:

```python
# Range validation with detailed errors
def validate_range(setting_name, value, min_val=None, max_val=None):
    """Validate numeric value is within acceptable range."""
    if min_val is not None and value < min_val:
        raise RangeError(
            setting=setting_name,
            value=value,
            min_value=min_val,
            max_value=max_val
        )
    if max_val is not None and value > max_val:
        raise RangeError(
            setting=setting_name,
            value=value,
            min_value=min_val,
            max_value=max_val
        )
    return value

# Common validation patterns
validation_rules = {
    'N': {'min': 1, 'max': 10, 'type': int},
    'max_time': {'min': 1, 'max': 3600, 'type': float},
    'max_models': {'min': 1, 'max': 10000, 'type': int},
    'M': {'min': 1, 'max': 20, 'type': int}  # Bimodal time points
}

# Apply validation
for setting, rule in validation_rules.items():
    if setting in settings:
        value = validate_type(setting, settings[setting], rule['type'])
        settings[setting] = validate_range(
            setting, value, 
            rule.get('min'), 
            rule.get('max')
        )
```

#### 3. Dependency and Compatibility Checking

Complex interdependencies between settings are validated:

```python
# Dependency validation
def validate_dependencies(settings, theory_name):
    """Check setting dependencies and mutual exclusions."""
    errors = []
    
    # Required dependencies
    dependencies = [
        # (setting, requires, message)
        ('use_counterfactual', 'use_modal', 
         "Counterfactual operators require modal operators"),
        ('derive_imposition', 'theory_name=imposition',
         "Deriving imposition only available in imposition theory"),
        ('M', 'theory_name=bimodal',
         "Time points (M) only apply to bimodal theory")
    ]
    
    for setting, requirement, message in dependencies:
        if setting in settings and settings.get(setting):
            if '=' in requirement:
                req_key, req_val = requirement.split('=')
                if settings.get(req_key) != req_val:
                    errors.append(ValidationError(
                        setting=setting,
                        message=message,
                        suggestion=f"Set {req_key} to {req_val} or disable {setting}"
                    ))
            elif not settings.get(requirement):
                errors.append(ValidationError(
                    setting=setting,
                    message=message,
                    suggestion=f"Enable {requirement} or disable {setting}"
                ))
    
    # Mutual exclusions
    exclusions = [
        (['contingent', 'non_contingent'], 
         "Cannot have both contingent and non_contingent"),
        (['sequential', 'parallel'], 
         "Cannot use both sequential and parallel processing")
    ]
    
    for exclusive_group, message in exclusions:
        active = [s for s in exclusive_group if settings.get(s)]
        if len(active) > 1:
            errors.append(ValidationError(
                setting=" and ".join(active),
                message=message,
                suggestion=f"Choose only one of: {', '.join(exclusive_group)}"
            ))
    
    return errors
```

#### 4. Theory-Specific Validation

Each theory can define its own validation constraints:

```python
# Theory-specific validation
class TheoryValidator:
    """Validate settings against theory constraints."""
    
    def __init__(self, theory_name, semantics_class):
        self.theory_name = theory_name
        self.semantics = semantics_class
        
    def validate(self, settings):
        """Validate settings for theory compatibility."""
        errors = []
        
        # Check theory-specific settings
        if self.theory_name == 'logos':
            errors.extend(self._validate_logos(settings))
        elif self.theory_name == 'bimodal':
            errors.extend(self._validate_bimodal(settings))
        elif self.theory_name == 'imposition':
            errors.extend(self._validate_imposition(settings))
            
        # Validate against semantic constraints
        errors.extend(self._validate_semantic_constraints(settings))
        
        return errors
    
    def _validate_logos(self, settings):
        """Logos-specific validation."""
        errors = []
        
        # Logos requires hyperintensional settings
        if settings.get('N', 0) > 8:
            errors.append(TheoryCompatibilityError(
                setting='N',
                theory_name='logos',
                reason='Logos complexity grows exponentially with N',
                suggestion='Use N ≤ 8 for logos theory'
            ))
            
        return errors
    
    def _validate_bimodal(self, settings):
        """Bimodal-specific validation."""
        errors = []
        
        # Bimodal requires both N and M
        if 'M' not in settings:
            errors.append(MissingRequiredError(
                setting='M',
                suggestion='Bimodal theory requires M (time points)'
            ))
            
        # Check temporal settings
        if settings.get('M', 0) * (2 ** settings.get('N', 0)) > 1024:
            errors.append(RangeError(
                setting='N×M',
                value=settings.get('M', 0) * (2 ** settings.get('N', 0)),
                max_value=1024
            ))
            
        return errors
    
    def _validate_semantic_constraints(self, settings):
        """Validate against semantic theory constraints."""
        errors = []
        
        # Check settings against semantic defaults
        required = self.semantics.REQUIRED_SETTINGS
        for setting in required:
            if setting not in settings:
                errors.append(MissingRequiredError(
                    setting=setting,
                    suggestion=f"{self.theory_name} requires {setting}"
                ))
                
        return errors
```

### Validation Examples

#### Example 1: Successful Validation Flow

```python
# Input settings from user
user_settings = {
    'N': '4',           # String will be converted to int
    'max_time': 30.0,   # Already correct type
    'verbose': 'true',  # String will be converted to bool
    'theory_name': 'logos',
    'contingent': True
}

# Validation process
validator = SettingsValidator(theory_name='logos')
result = validator.validate(user_settings)

# Result: Success
# {
#     'N': 4,             # Converted to int
#     'max_time': 30.0,   # Unchanged
#     'verbose': True,    # Converted from string
#     'theory_name': 'logos',
#     'contingent': True,
#     # ... merged with defaults ...
# }
```

#### Example 2: Type Conversion Error with Recovery

```python
# Invalid type that cannot be converted
user_settings = {'N': 'invalid'}

try:
    validator.validate(user_settings)
except TypeConversionError as e:
    print(f"Error: {e}")
    # Output: Setting 'N': Cannot convert value 'invalid' to int
    # Suggestion: Provide a value of type int
    
    # Recovery: Use default value
    user_settings['N'] = theory_defaults['N']
    # Retry validation
    result = validator.validate(user_settings)
```

#### Example 3: Range Error with Helpful Feedback

```python
# Value out of acceptable range
user_settings = {'N': 15}

try:
    validator.validate(user_settings)
except RangeError as e:
    print(f"Error: {e}")
    # Output: Setting 'N': Value 15 is above maximum 10
    # Suggestion: Provide a value <= 10
    
    # Recovery: Clamp to maximum
    user_settings['N'] = min(user_settings['N'], 10)
```

#### Example 4: Dependency Error Resolution

```python
# Conflicting settings
user_settings = {
    'use_counterfactual': True,
    'use_modal': False  # Problem: counterfactual requires modal
}

errors = validate_dependencies(user_settings, 'logos')
for error in errors:
    print(f"Error: {error.message}")
    print(f"Fix: {error.suggestion}")
    # Output: Counterfactual operators require modal operators
    # Fix: Enable use_modal or disable use_counterfactual
    
    # Resolution strategies:
    # Option 1: Enable required setting
    user_settings['use_modal'] = True
    
    # Option 2: Disable dependent setting
    # user_settings['use_counterfactual'] = False
```

#### Example 5: Theory Compatibility Check

```python
# Settings incompatible with theory
user_settings = {
    'theory_name': 'logos',
    'M': 5  # M only applies to bimodal theory
}

try:
    validator = TheoryValidator('logos', LogosSemantics)
    errors = validator.validate(user_settings)
    
    if errors:
        for error in errors:
            if isinstance(error, TheoryCompatibilityError):
                print(f"Incompatibility: {error.reason}")
                print(f"Solution: {error.suggestion}")
                # Output: Setting 'M' is incompatible with logos: 
                #         M (time points) only apply to bimodal theory
                # Solution: Remove M or switch to bimodal theory
                
                # Resolution: Remove incompatible setting
                del user_settings['M']
except ValidationError as e:
    # Handle validation failure
    pass
```

### Error Recovery Strategies

#### Automatic Recovery Patterns

```python
class SmartValidator:
    """Validator with automatic error recovery."""
    
    def validate_with_recovery(self, settings, theory_name):
        """Attempt validation with automatic recovery."""
        errors = []
        recovered_settings = settings.copy()
        
        # Phase 1: Type conversion with fallback
        for key, value in settings.items():
            try:
                recovered_settings[key] = self.convert_type(key, value)
            except TypeConversionError as e:
                errors.append(e)
                # Fallback to default if available
                if key in self.defaults:
                    recovered_settings[key] = self.defaults[key]
                    e.recovery_applied = f"Used default value: {self.defaults[key]}"
        
        # Phase 2: Range validation with clamping
        for key, value in recovered_settings.items():
            if key in self.ranges:
                min_val, max_val = self.ranges[key]
                if value < min_val:
                    recovered_settings[key] = min_val
                    errors.append(RangeError(
                        key, value, min_val, max_val,
                        recovery_applied=f"Clamped to minimum: {min_val}"
                    ))
                elif value > max_val:
                    recovered_settings[key] = max_val
                    errors.append(RangeError(
                        key, value, min_val, max_val,
                        recovery_applied=f"Clamped to maximum: {max_val}"
                    ))
        
        # Phase 3: Dependency resolution
        dep_errors = self.check_dependencies(recovered_settings)
        for error in dep_errors:
            # Try to auto-resolve simple dependencies
            if error.can_auto_resolve:
                recovered_settings[error.required_setting] = True
                error.recovery_applied = f"Auto-enabled {error.required_setting}"
            errors.append(error)
        
        return recovered_settings, errors
    
    def suggest_fixes(self, errors):
        """Generate fix suggestions for validation errors."""
        suggestions = []
        
        for error in errors:
            if hasattr(error, 'recovery_applied'):
                suggestions.append(f"✓ {error.recovery_applied}")
            elif isinstance(error, MissingRequiredError):
                suggestions.append(
                    f"Add to settings: {error.setting} = "
                    f"{self.defaults.get(error.setting, '...')}"
                )
            elif isinstance(error, UnknownSettingError):
                if error.available_settings:
                    similar = self.find_similar(error.setting, error.available_settings)
                    if similar:
                        suggestions.append(f"Did you mean '{similar}'?")
        
        return suggestions
```

#### User-Interactive Recovery

```python
class InteractiveValidator:
    """Validator with user interaction for error recovery."""
    
    def validate_interactive(self, settings):
        """Validate with user prompts for fixes."""
        while True:
            try:
                return self.validate(settings)
            except SettingsError as e:
                print(f"\n❌ Validation Error: {e}")
                
                if e.suggestion:
                    print(f"Suggestion: {e.suggestion}")
                
                # Offer recovery options
                print("\nOptions:")
                print("1. Use default value")
                print("2. Enter new value")
                print("3. Skip this setting")
                print("4. Abort")
                
                choice = input("Choose option (1-4): ")
                
                if choice == '1':
                    settings[e.setting] = self.get_default(e.setting)
                elif choice == '2':
                    new_value = input(f"Enter value for {e.setting}: ")
                    settings[e.setting] = self.parse_value(new_value)
                elif choice == '3':
                    if e.setting in settings:
                        del settings[e.setting]
                else:
                    raise e
```

### Validation Best Practices

1. **Fail Fast with Clear Messages**: Validate early and provide specific error information
2. **Suggest Fixes**: Always include actionable suggestions in error messages
3. **Attempt Recovery**: Try automatic type conversion and value clamping when safe
4. **Batch Validation**: Collect all errors before reporting to avoid multiple retry cycles
5. **Provide Defaults**: Have sensible defaults for all non-required settings
6. **Document Constraints**: Clearly document valid ranges and dependencies
7. **Test Edge Cases**: Validate boundary values and conflicting combinations

## Settings Merge Process

### Merge Algorithm

The settings system implements a sophisticated multi-layer merge process:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    SETTINGS MERGE ALGORITHM (get_complete_settings)         │
└─────────────────────────────────────────────────────────────────────────────┘

LAYER 1: BASE DEFAULTS                    PRIORITY: ████░░ (Lowest)
┌──────────────────────────────────────────────────────────────────┐
│ SemanticDefaults.DEFAULT_GENERAL_SETTINGS                        │
│ • print_impossible: False   • print_constraints: False           │
│ • print_z3: False          • save_output: False                  │
│ • sequential: False        • maximize: False                     │
└────────────────────────────────────┬─────────────────────────────┘
                                     │ copy()
                                     ▼
LAYER 2: THEORY ADDITIONS                 PRIORITY: ████░░
┌──────────────────────────────────────────────────────────────────┐
│ Theory.ADDITIONAL_GENERAL_SETTINGS (if exists)                  │
│ • align_vertically: True    (bimodal)                          │
│ • derive_imposition: False  (imposition)                       │
└────────────────────────────────────┬─────────────────────────────┘
                                     │ update()
                                     ▼
LAYER 3: USER GENERAL                     PRIORITY: █████░
┌──────────────────────────────────────────────────────────────────┐
│ validate_general_settings(user_general_settings)                │
│ • Warns unknown settings    • Validates types                   │
│ • Merges valid keys         • Returns merged dict               │
└────────────────────────────────────┬─────────────────────────────┘
                                     │
                                     ▼
LAYER 4: THEORY EXAMPLE DEFAULTS          PRIORITY: █████░
┌──────────────────────────────────────────────────────────────────┐
│ Theory.DEFAULT_EXAMPLE_SETTINGS                                 │
│ • N: 16 (logos)            • M: 2 (bimodal)                    │
│ • max_time: 10             • contingent: True                  │
└────────────────────────────────────┬─────────────────────────────┘
                                     │ copy()
                                     ▼
LAYER 5: USER EXAMPLE                     PRIORITY: ██████
┌──────────────────────────────────────────────────────────────────┐
│ validate_example_settings(user_example_settings)                │
│ • Warns unknown settings    • Validates against theory          │
│ • Merges valid keys         • Returns merged dict               │
└────────────────────────────────────┬─────────────────────────────┘
                                     │ combine
                                     ▼
LAYER 6: CLI FLAGS                        PRIORITY: ██████ (Highest)
┌──────────────────────────────────────────────────────────────────┐
│ apply_flag_overrides(combined_settings, module_flags)           │
│ • Extracts user-provided flags from _parsed_args               │
│ • Skips standard args (load_theory, version, etc)              │
│ • Only applies explicitly provided flags                        │
└────────────────────────────────────┬─────────────────────────────┘
                                     │
                                     ▼
                        ┌─────────────────────────┐
                        │   FINAL VALIDATION      │
                        │ • Type checking         │
                        │ • Range validation     │
                        │ • Theory compatibility │
                        └────────────┬────────────┘
                                     │
                        ┌────────────┼────────────┐
                        ▼            ▼            ▼
                ┌──────────┐  ┌──────────┐  ┌──────────┐
                │  VALID   │  │  WARNING │  │  ERROR   │
                │ Settings │  │  Unknown │  │  Invalid │
                │  Ready   │  │  Ignored │  │  Abort   │
                └──────────┘  └──────────┘  └──────────┘
```

### Merge Implementation Details

#### Actual Code Flow

```python
# From SettingsManager.get_complete_settings()

def get_complete_settings(self, user_general_settings, user_example_settings, module_flags):
    """Merge settings in priority order."""
    
    # 1. Start with base + theory general settings
    general_settings = self.validate_general_settings(user_general_settings)
    # This internally does:
    # - Start with SemanticDefaults.DEFAULT_GENERAL_SETTINGS
    # - Add Theory.ADDITIONAL_GENERAL_SETTINGS (if exists)
    # - Apply user_general_settings (with validation)
    
    # 2. Get example settings with defaults
    example_settings = self.validate_example_settings(user_example_settings)
    # This internally does:
    # - Start with Theory.DEFAULT_EXAMPLE_SETTINGS
    # - Apply user_example_settings (with validation)
    
    # 3. Combine general and example (example takes precedence)
    combined_settings = general_settings.copy()
    combined_settings.update(example_settings)
    
    # 4. Apply CLI flags (highest priority)
    final_settings = self.apply_flag_overrides(combined_settings, module_flags)
    # This internally:
    # - Extracts user-provided flags from _parsed_args
    # - Only overrides explicitly provided flags
    # - Warns about unknown flags
    
    return final_settings
```

#### Practical Merge Example

```python
# LAYER 1: Base defaults (SemanticDefaults)
settings = {
    'print_impossible': False,
    'print_constraints': False,
    'save_output': False,
    'sequential': False
}

# LAYER 2: Theory additions (LogosSemantics.ADDITIONAL_GENERAL_SETTINGS)
# (logos has none, but bimodal would add align_vertically: True)

# LAYER 3: User general settings from module
user_general = {'verbose': True, 'save_output': True}
settings.update(user_general)
# Now: {..., 'verbose': True, 'save_output': True}

# LAYER 4: Theory example defaults (LogosSemantics.DEFAULT_EXAMPLE_SETTINGS)
theory_defaults = {'N': 16, 'max_time': 10, 'contingent': True}
settings.update(theory_defaults)
# Now: {..., 'N': 16, 'max_time': 10, 'contingent': True, ...}

# LAYER 5: User example settings
user_example = {'N': 4, 'contingent': False}
settings.update(user_example)
# Now: {..., 'N': 4, 'max_time': 10, 'contingent': False, ...}

# LAYER 6: CLI flags (highest priority)
cli_flags = {'N': 6, 'verbose': False, 'iterate': True}
settings.update(cli_flags)
# Final: {'N': 6, 'verbose': False, 'iterate': True, 'save_output': True, ...}
```

#### Warning System

```python
# Unknown settings generate warnings but don't fail:
user_settings = {'unknown_setting': 42, 'N': 4}

# Output:
# Warning: Unknown setting 'unknown_setting' in general settings
# (setting ignored but execution continues)

# In comparison mode, warnings are suppressed to reduce noise
```

## Dynamic Settings Management

### Interactive Settings Updates (Jupyter)

The system supports real-time settings modification through interactive widgets:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   INTERACTIVE SETTINGS UPDATE FLOW                          │
└─────────────────────────────────────────────────────────────────────────────┘

USER INTERACTION                    SYSTEM RESPONSE
┌──────────────┐                    ┌──────────────────────────┐
│ Widget Input │───────────────────▶│ _update_setting(key,val) │
│ • Slider     │                    │ • Update settings dict   │
│ • Checkbox   │                    │ • Trigger UI refresh     │
│ • Dropdown   │                    └────────────┬─────────────┘
└──────────────┘                                 │
                                                 ▼
┌──────────────┐                    ┌──────────────────────────┐
│ Check Button │───────────────────▶│ build_example()          │
│ • User click │                    │ • Use current settings   │
└──────────────┘                    │ • Create new model       │
                                    └────────────┬─────────────┘
                                                 │
┌──────────────┐                                ▼
│ Next Model   │                    ┌──────────────────────────┐
│ • Find alt.  │───────────────────▶│ find_next_model()        │
└──────────────┘                    │ • Keep current settings  │
                                    │ • Add exclusion const.   │
                                    └──────────────────────────┘

WIDGET BINDINGS (from ui_builders.py):
┌────────────────────────────────────────────────────────────────────┐
│ n_slider.observe(λ: parent._update_setting('N', value))            │
│ max_time_slider.observe(λ: parent._update_setting('max_time', v))  │
│ contingent_checkbox.observe(λ: parent._update_setting(...))        │
│ non_empty_checkbox.observe(λ: parent._update_setting(...))         │
│ expectation_selector.observe(λ: parent._update_setting(...))       │
└────────────────────────────────────────────────────────────────────┘
```

### Model Checking State Machine

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    MODEL CHECKING EXECUTION STATES                          │
└─────────────────────────────────────────────────────────────────────────────┘

    INIT                    CHECK                  ITERATE
┌─────────────┐        ┌─────────────┐         ┌─────────────┐
│ BuildModule │───────▶│ BuildExample│────────▶│ModelIterator│
│             │        │             │         │             │
│ • Load theo │        │ • Apply set │         │ • Use set   │
│ • Init set  │        │ • Build mod │         │ • Find next │
│ • Validate  │        │ • Check SAT │         │ • Exclude   │
└─────────────┘        └──────┬──────┘         └──────┬──────┘
                              │                       │
                              ▼                       ▼
                        ┌─────────────┐         ┌─────────────┐
                        │   RESULT    │         │  MULTIPLE   │
                        │             │         │   MODELS    │
                        │ • SAT/UNSAT │         │ • Model 1   │
                        │ • Model data│         │ • Model 2   │
                        │ • Runtime   │         │ • ...       │
                        └─────────────┘         └─────────────┘

STATE TRANSITIONS WITH SETTINGS:
┌──────────────────────────────────────────────────────────────┐
│ State      │ Settings Used           │ Can Modify?           │
├────────────┼─────────────────────────┼───────────────────────┤
│ INIT       │ All layers merged       │ Yes (before build)    │
│ CHECK      │ Final merged settings   │ No (immutable)        │
│ ITERATE    │ Copy from CHECK         │ Only max_iterations   │
│ RESULT     │ Read-only reference     │ No                    │
└──────────────────────────────────────────────────────────────┘
```

### Settings Lifecycle During Execution

```python
# 1. INITIALIZATION PHASE
build_module = BuildModule(theories, settings, flags)
# Settings are merged and validated

# 2. EXAMPLE CREATION PHASE
example = BuildExample(module, theory, case)
# Settings are finalized via get_complete_settings()
# example.settings is now immutable for this check

# 3. MODEL CHECKING PHASE
model_structure = ModelStructure(constraints, settings)
# Settings are used to configure Z3 solver:
solver.set("timeout", int(settings["max_time"] * 1000))

# 4. ITERATION PHASE (if requested)
if settings.get("iterate") or user_requests_next:
    iterator = ModelIterator(example)
    # Iterator creates new models with same settings
    # But adds exclusion constraints for each found model
    
# 5. INTERACTIVE UPDATES (Jupyter only)
def _update_setting(self, key, value):
    self.settings[key] = value  # Update local copy
    # Next check will use updated settings
```

### Runtime Modifiable Settings

#### Safely Modifiable Between Checks:
- `N` - Number of atomic propositions (requires rebuild)
- `max_time` - Solver timeout (applied per solve)
- `max_models` - Iteration limit
- `contingent`, `non_empty`, `disjoint` - Semantic constraints
- `verbose`, `print_constraints` - Output control
- `expectation` - Valid/invalid expectation

#### Not Modifiable During Check:
- `theory_name` - Would require complete rebuild
- Settings already applied to solver
- Constraints already generated

#### Special Handling:
- `iterate`: Triggers ModelIterator after initial check
- `save_output`: Can be decided after seeing results
- `output_format`: Applied during output generation

## Settings Persistence

### Configuration File Structure
```json
{
    "version": "1.0.0",
    "global": {
        "default_theory": "logos",
        "verbose": true,
        "output_format": "text"
    },
    "theories": {
        "logos": {
            "N": 4,
            "use_modal": true
        },
        "bimodal": {
            "N": 3,
            "max_time_points": 5
        }
    },
    "projects": {
        "research": {
            "output_dir": "~/research/output",
            "save_output": true
        }
    }
}
```

### Loading Order
1. Check for project-specific config
2. Load theory-specific settings
3. Apply global settings
4. Override with command-line arguments

## Best Practices

### For Users
1. **Start Simple**: Use defaults, adjust only as needed
2. **Profile First**: Understand performance before increasing N
3. **Save Configs**: Store frequently-used settings in config file
4. **Use Projects**: Organize settings by project/context

### For Developers
1. **Validate Early**: Check settings before processing
2. **Document Settings**: Clear descriptions and examples
3. **Provide Defaults**: Sensible defaults for all settings
4. **Report Issues**: Clear error messages with suggestions

## Common Patterns

### Research Configuration
```python
# High exploration, save everything
settings = {
    'N': 6,
    'max_models': 100,
    'max_time': 300,
    'save_output': True,
    'verbose': True
}
```

### Teaching Configuration
```python
# Simple, clear output
settings = {
    'N': 3,
    'max_models': 3,
    'output_format': 'text',
    'verbose': False
}
```

### Debugging Configuration
```python
# Maximum information
settings = {
    'verbose': True,
    'debug': True,
    'show_constraints': True,
    'trace_solving': True
}
```

## See Also

### Related Components
- **[Pipeline Overview](PIPELINE.md)** - How settings flow through the system
- **[Builder Architecture](BUILDER.md)** - Settings usage in orchestration
- **[Output System](OUTPUT.md)** - Output-related settings

### Technical Documentation
- **[Settings Implementation](../../Code/src/model_checker/settings/README.md)** - Code details
- **[Configuration API](../../Code/src/model_checker/settings/config.py)** - Settings API
- **[Validation System](../../Code/src/model_checker/settings/validator.py)** - Validation logic

### Usage Guides
- **[Settings Reference](../usage/SETTINGS_REFERENCE.md)** - Complete settings list
- **[Configuration Guide](../usage/CONFIGURATION.md)** - Configuration tutorials
- **[Performance Tuning](../usage/PERFORMANCE.md)** - Optimization settings
