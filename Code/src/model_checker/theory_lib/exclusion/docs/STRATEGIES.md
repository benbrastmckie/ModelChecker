# ModelChecker Settings Architecture Analysis

## Executive Summary

This document provides a comprehensive analysis of the ModelChecker settings architecture, revealing how settings flow through the system and identifying key patterns for future development.

## Table of Contents

1. [Current Architecture Overview](#current-architecture-overview)
2. [Key Architectural Patterns](#key-architectural-patterns)
3. [Integration Points for New Features](#integration-points-for-new-features)
4. [Design Principles](#design-principles)
5. [Common Patterns for Extending Settings](#common-patterns-for-extending-settings)
6. [Best Practices](#best-practices)
7. [Future Considerations](#future-considerations)
8. [Exclusion Theory Implementation Strategies](#exclusion-theory-implementation-strategies)

---

## Current Architecture Overview

### 1. Settings Definition Points

Settings are defined at two levels within each semantic theory:

1. **DEFAULT_EXAMPLE_SETTINGS**: Settings specific to individual examples
   - Controls model generation parameters (N, max_time, etc.)
   - Includes semantic constraints (contingent, disjoint, etc.)
   - Theory-specific parameters (iterate, iteration_timeout, etc.)

2. **DEFAULT_GENERAL_SETTINGS**: Module-wide settings
   - Output control (print_impossible, print_constraints, etc.)
   - Debugging options (print_z3, save_output)
   - Theory-specific display options (align_vertically for bimodal)

### 2. Settings Management via SettingsManager

The `SettingsManager` class in `settings/settings.py` provides centralized management:

```python
class SettingsManager:
    def __init__(self, semantic_theory, global_defaults=None)
    def validate_general_settings(self, user_general_settings)
    def validate_example_settings(self, user_example_settings)
    def apply_flag_overrides(self, settings, module_flags)
    def get_complete_settings(self, user_general_settings, user_example_settings, module_flags)
```

**Key Features:**
- Validates settings against theory-specific defaults
- Warns about unknown settings without failing
- Merges settings according to priority rules
- Applies command-line flag overrides as final step

### 3. Settings Flow Through the System

The settings flow follows this path:

1. **BuildModule initialization** (`builder/module.py`):
   - Creates SettingsManager with first semantic theory
   - Validates and stores general_settings
   - Applies flag overrides to general settings

2. **BuildExample creation** (`builder/example.py`):
   - Creates its own SettingsManager for the specific theory
   - Merges: defaults → general → example → flags
   - Passes final settings to model components

3. **Model Components**:
   - `SemanticDefaults.__init__(combined_settings)`: Extracts N, M, etc.
   - `ModelDefaults.__init__(model_constraints, settings)`: Uses for solver config
   - Theory-specific classes access via `self.settings`

### 4. Priority Order

Settings follow a clear priority order (lowest to highest):

1. Theory DEFAULT_EXAMPLE_SETTINGS
2. Theory DEFAULT_GENERAL_SETTINGS (if applicable)
3. User-defined general_settings in module
4. User-defined settings in specific example
5. Command-line flags (highest priority)

## Key Architectural Patterns

### 1. Theory-Specific Settings

Each theory defines only the settings relevant to it:

```python
# Logos theory includes hyperintensional settings
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,
    'iterate': False,
    # ...
}

# Exclusion theory has different defaults
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'iterate': 1,
    # ...
}
```

### 2. Settings Validation Pattern

The system validates settings but doesn't fail on unknown settings:

```python
# In validate_example_settings
for key in user_example_settings:
    if key not in self.DEFAULT_EXAMPLE_SETTINGS:
        print(f"Warning: Unknown example setting '{key}'...")
```

This allows theories to be flexible while warning about potential typos.

### 3. Flag Override Implementation

Command-line flags are carefully handled to only override when explicitly provided:

```python
# Detects which flags were actually provided by user
user_provided_flags = set()
for arg in module_flags._parsed_args:
    if arg.startswith('--'):
        flag_name = arg[2:].split('=')[0]
        user_provided_flags.add(flag_name)
```

### 4. Settings Access Pattern

Components access settings through a consistent pattern:

```python
# In semantic classes
def __init__(self, combined_settings):
    self.N = combined_settings['N']
    self.settings = combined_settings  # Store for later use

# In model classes  
def __init__(self, model_constraints, settings):
    self.settings = settings
    self.max_time = self.settings["max_time"]
```

## Integration Points for New Features

### 1. Theory Registration

When adding a new theory, settings are automatically handled if you:

1. Define DEFAULT_EXAMPLE_SETTINGS in your semantic class
2. Optionally define DEFAULT_GENERAL_SETTINGS
3. Access settings via self.settings in your implementation

### 2. Iterator Integration

The iteration system integrates through settings:

```python
# Check if iteration is requested
iterate_count = example.settings.get('iterate', 1)

# Access iteration-specific settings
iteration_timeout = example.settings.get('iteration_timeout', 1.0)
iteration_attempts = example.settings.get('iteration_attempts', 5)
```

### 3. Display and Output Control

Output behavior is controlled through general settings:

```python
if self.settings.get('print_impossible', False):
    # Include impossible states in output

if self.settings.get('print_constraints', False):
    # Show constraints when no model found
```

## Design Principles

### 1. Fail-Fast Philosophy

The settings system follows ModelChecker's fail-fast philosophy:
- Invalid settings trigger warnings, not silent failures
- Type mismatches cause immediate errors
- Missing required settings fail at point of use

### 2. Explicit Over Implicit

- All defaults are explicitly defined in theory classes
- Settings flow is explicit through method calls
- No hidden global configuration

### 3. Theory Independence

- Each theory defines its own settings namespace
- No requirement to support all possible settings
- Theories can add custom settings as needed

### 4. Backwards Compatibility

The system maintains compatibility by:
- Supporting both old attribute access and new settings dict
- Providing sensible defaults for all settings
- Warning rather than failing on unknown settings

## Common Patterns for Extending Settings

### 1. Adding a New Setting to a Theory

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        # ... existing settings ...
        'your_new_setting': default_value,
    }
    
    def your_method(self):
        if self.settings['your_new_setting']:
            # Implement behavior
```

### 2. Adding a Command-Line Flag

In `cli.py`:
```python
parser.add_argument(
    '--your-flag', '-y',
    dest='your_new_setting',
    action='store_true',
    help='Description of flag'
)
```

### 3. Creating Theory-Specific General Settings

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_GENERAL_SETTINGS = {
        'print_impossible': False,
        'your_display_option': True,  # Theory-specific
    }
```

### 4. Accessing Settings in Model Components

```python
class YourModel(ModelDefaults):
    def custom_method(self):
        # Access through self.settings
        if self.settings.get('your_setting', default):
            # Handle setting
```

## Best Practices

### 1. Setting Naming Conventions

- Use lowercase with underscores: `iteration_timeout`
- Be descriptive: `print_impossible` not `pi`
- Group related settings: `iteration_*` for iteration features

### 2. Default Values

- Choose defaults that work without user intervention
- Make defaults conservative (smaller N, shorter timeouts)
- Document why specific defaults were chosen

### 3. Setting Documentation

- Document each setting in DEFAULT_*_SETTINGS
- Include type, purpose, and impact
- Provide examples in theory documentation

### 4. Setting Validation

- Validate at point of use, not just at input
- Provide helpful error messages
- Consider setting interdependencies

## Future Considerations

### 1. Type System

Consider adding type annotations:
```python
from typing import TypedDict

class ExampleSettings(TypedDict):
    N: int
    max_time: float
    contingent: bool
    # ...
```

### 2. Setting Schemas

Could add JSON Schema validation:
```python
EXAMPLE_SETTINGS_SCHEMA = {
    "type": "object",
    "properties": {
        "N": {"type": "integer", "minimum": 1},
        "max_time": {"type": "number", "minimum": 0},
        # ...
    }
}
```

### 3. Setting Groups

Could organize settings into logical groups:
```python
SOLVER_SETTINGS = ['max_time', 'iteration_timeout']
SEMANTIC_SETTINGS = ['contingent', 'disjoint', 'non_empty']
OUTPUT_SETTINGS = ['print_impossible', 'print_constraints']
```

### 4. Dynamic Setting Discovery

Could implement automatic flag generation from settings:
```python
def generate_cli_flags(settings_dict):
    for key, default in settings_dict.items():
        if isinstance(default, bool):
            add_boolean_flag(key)
        else:
            add_value_flag(key, type(default))
```

---

# Exclusion Theory Implementation Strategies

## Overview

This section comprehensively describes the various implementation strategies for the exclusion operator in the unilateral semantics framework. Each strategy represents a different approach to solving the **False Premise Problem** - the fundamental challenge of preserving witness function information across the two-phase model checking architecture.

## The Core Problem

All strategies implement the same three-condition semantics for exclusion:

**A state s verifies the exclusion of φ iff there exist functions h, y such that:**
1. **Exclusion Condition**: ∀x ∈ Ver(φ): ∃y ⊑ x where h(x) excludes y
2. **Upper Bound**: ∀x ∈ Ver(φ): h(x) ⊑ s  
3. **Minimality**: s is minimal satisfying conditions 1-2

The challenge is implementing these existentially quantified functions in a way that preserves their values for later evaluation.

## Strategy Categories

### 1. Original Strategies (Strategy1)
These strategies attempt various encodings within Z3's constraint system but ultimately fail to solve the False Premise Problem.

### 2. Witness Predicate Solution (Strategy2)
The successful approach that makes witness functions first-class model citizens through Z3 predicates.

---

## Original Strategies (Strategy1)

### QA: Quantify Arrays
**File**: `strategy1_multi/operators.py` (lines 221-267)

**Approach**: Uses Z3 Arrays to represent the exclusion function, with existential quantification over the array.

```python
h = z3.Array(f"h", z3.BitVecSort(N), z3.BitVecSort(N))
return z3.Exists(h, z3.And(...))
```

**Implementation Details**:
- Creates a Z3 Array `h` mapping states to states
- Existentially quantifies over the entire array
- Uses consistent naming ('h') for potential extraction

**Advantages**:
- Clean representation of functions as arrays
- Theoretically allows function extraction

**Disadvantages**:
- Existential quantification causes witness loss
- Z3 discards array values after solving
- Cannot access h values during evaluation phase

**Status**: ❌ Fails due to False Premise Problem

---

### QI: Quantify Indices
**File**: `strategy1_multi/operators.py` (lines 269-302)

**Approach**: Quantifies over indices into a global array of functions, attempting to preserve function references.

```python
ix = z3.Int(f"ix_{semantics.counter}")
H = semantics.H  # Global array of functions
return z3.Exists(ix, z3.And(...H(ix)[x]...))
```

**Implementation Details**:
- Uses integer index to select from pre-defined function array
- Attempts to avoid direct function quantification
- References functions indirectly through indices

**Advantages**:
- Indirect function reference might preserve values
- Avoids quantifying over functions directly

**Disadvantages**:
- Infinite integer domain for indices
- Still uses existential quantification
- Complex indirection doesn't solve core problem

**Status**: ❌ Fails due to False Premise Problem

---

### QI2: Quantify Indices (Variant 2)
**File**: `strategy1_multi/operators.py` (lines 304-337)

**Approach**: Alternative indexing scheme with different function storage structure.

```python
H = semantics.H2  # Different global structure
return z3.Exists(ix, z3.And(...H(ix, x)...))
```

**Implementation Details**:
- Uses two-parameter function access H(ix, x)
- Attempts different organization of witness functions
- Variation on QI strategy

**Advantages**:
- Explores alternative function organization

**Disadvantages**:
- Same fundamental issues as QI
- Existential quantification still causes witness loss

**Status**: ❌ Fails due to False Premise Problem

---

### BQI: Bounded Quantify Indices
**File**: `strategy1_multi/operators.py` (lines 339-375)

**Approach**: Bounds the quantification domain to avoid Z3's infinite domain issues.

```python
ix = semantics.B_h_ix  # Bounded index (BitVec of size N+5)
H = semantics.BH      # Bounded function array
return Exists(ix, z3.And(...))
```

**Implementation Details**:
- Limits indices to 2^(N+5) based on complexity estimates
- Uses BitVector for bounded domain
- Attempts to make search space finite and predictable

**Calculation**: 2^(N+3+2) where:
- 2 negations per sentence (estimated)
- 4 sentences maximum
- O(n) verifiers
- +2 safety margin

**Advantages**:
- Avoids infinite domain issues
- More predictable Z3 behavior
- "Slow and steady" approach

**Disadvantages**:
- Very slow due to large search space
- May still miss required indices
- Doesn't solve witness preservation

**Status**: ❌ Fails due to False Premise Problem

---

### NF: Name Functions
**File**: `strategy1_multi/operators.py` (lines 377-425)

**Approach**: Creates uniquely named functions for each exclusion instance.

```python
h = z3.Function(f"h_{semantics.counter}", z3.BitVecSort(N), z3.BitVecSort(N))
# No existential quantification over h!
```

**Implementation Details**:
- Each exclusion gets unique function name
- Uses counter to ensure uniqueness
- Attempts to make functions persistent

**Advantages**:
- Functions have unique names in model
- No existential quantification over functions
- Closer to solving the problem

**Disadvantages**:
- Still uses existential quantification for witnesses (y)
- Incomplete solution to witness preservation
- Functions created but not properly tracked

**Status**: ❌ Fails - better but still incomplete

---

### NA: Name Arrays
**File**: `strategy1_multi/operators.py` (lines 427-458)

**Approach**: Similar to NF but uses Arrays instead of Functions.

```python
h = z3.Array(f"h_{semantics.counter}", z3.BitVecSort(N), z3.BitVecSort(N))
```

**Implementation Details**:
- Named arrays with unique identifiers
- Explores Z3's array vs function handling differences

**Advantages**:
- Same benefits as NF
- Tests different Z3 data structures

**Disadvantages**:
- Same fundamental issues as NF
- Array vs Function distinction doesn't solve core problem

**Status**: ❌ Fails due to False Premise Problem

---

## Advanced Strategies (Strategy1 Phase 3)

### SK: Skolemized Functions
**File**: `strategy1_multi/operators.py` (lines 460-542)

**Approach**: Eliminates existential quantifiers using Skolemization.

```python
h_sk = z3.Function(f"h_sk_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
y_sk = z3.Function(f"y_sk_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
# No Exists! Direct function constraints
```

**Implementation Details**:
- Replaces ∃y with Skolem function y_sk(x)
- Creates both h and y as persistent functions
- Most sophisticated Strategy1 approach

**Key Innovation**: 
```python
# Instead of: ∃y: P(x,y)
# Uses: P(x, y_sk(x))
```

**Advantages**:
- No existential quantifiers at all
- Functions are first-class objects
- Very close to Strategy2 approach

**Disadvantages**:
- Still lacks proper witness registry
- No systematic way to query witnesses
- Missing evaluation infrastructure

**Status**: ❌ Fails - closest Strategy1 attempt

---

### CD: Constraint-Based Definition
**File**: `strategy1_multi/operators.py` (lines 544-641)

**Approach**: Explicitly enumerates constraints rather than using quantifiers.

```python
# Enumerate possible y values explicitly
z3.Or([
    z3.And(is_part_of(y, x), excludes(h_cd(x), y))
    for y_val in range(min(2**N, 16))
    for y in [z3.BitVecVal(y_val, N)]
])
```

**Implementation Details**:
- Avoids existential quantification through enumeration
- Limits enumeration for efficiency
- Creates explicit constraints for each possibility

**Advantages**:
- No existential quantifiers
- Completely explicit constraints
- Deterministic behavior

**Disadvantages**:
- Doesn't scale to large state spaces
- Arbitrary enumeration limits
- Still missing witness preservation

**Status**: ❌ Fails due to incomplete enumeration

---

### MS: Multi-Sort (Production Default)
**File**: `strategy1_multi/operators.py` (lines 643-781)

**Approach**: Uses Z3's sort system for type safety and organization.

```python
StateSort = z3.BitVecSort(N)
ExclusionFunctionSort = z3.BitVecSort(N)
h_ms = z3.Function(f"h_ms_{counter}", StateSort, ExclusionFunctionSort)
```

**Implementation Details**:
- Production-ready implementation
- Enhanced error handling and validation
- Clear type separation
- Comprehensive debugging support

**Performance** (from testing):
- Success Rate: 50.0% (17/34 examples)
- Reliability: 52.9% (9 valid models out of 17)
- Speed: 0.387s average

**Advantages**:
- Best performance among Strategy1 approaches
- Production-ready code quality
- Type safety through sorts

**Disadvantages**:
- Still has 50% failure rate
- Existential quantification for y remains
- Cannot fully solve False Premise Problem

**Status**: ⚠️ Partial success - best Strategy1 option

---

### UF: Uninterpreted Functions with Axioms
**File**: `strategy1_multi/operators.py` (lines 783-877)

**Approach**: Defines semantics through axioms on uninterpreted functions.

```python
h_uf = z3.Function(f"h_uf_{counter}", ...)
witness_uf = z3.Function(f"witness_uf_{counter}", ...)
# Axioms constrain behavior
axiom1 = ForAll(x, z3.Implies(...))
```

**Implementation Details**:
- Separates function declaration from semantics
- Uses axioms to define behavior
- Leverages Z3's UF reasoning

**Advantages**:
- Clean axiomatization
- Leverages Z3 optimization for UF
- Modular design

**Disadvantages**:
- Axioms alone don't preserve witnesses
- Same fundamental evaluation problem
- Added complexity without solving core issue

**Status**: ❌ Fails due to False Premise Problem

---

### WD: Witness-Driven
**File**: `strategy1_multi/operators.py` (lines 879-1004)

**Approach**: Pre-computes witness mappings for small domains.

```python
# Pre-compute for small domain
for verifier_val in range(max_domain):
    for witness_val in range(max_domain):
        # Build explicit constraints
```

**Implementation Details**:
- Enumerates possible witnesses for small domains
- Creates explicit constraints for known values
- Falls back to general constraints for large values

**Advantages**:
- Deterministic for small domains
- Explicit witness control
- Partially avoids quantifier issues

**Disadvantages**:
- Doesn't scale beyond small domains
- Hybrid approach adds complexity
- Still can't preserve witnesses for evaluation

**Status**: ❌ Fails for non-trivial examples

---

## The Witness Predicate Solution (Strategy2)

### UniNegationOperator
**File**: `strategy2_witness/operators.py` (lines 17-241)

**Approach**: Makes witness functions first-class model citizens through predicates.

```python
# In semantic.py - witnesses are registered
h_pred = sem.witness_registry.predicates[f"{formula_str}_h"]
y_pred = sem.witness_registry.predicates[f"{formula_str}_y"]

# In operators.py - witnesses are used directly
return z3.And(
    ForAll([x], z3.Implies(
        extended_verify(x, argument, eval_point), 
        z3.And(
            is_part_of(y_pred(x), x), 
            excludes(h_pred(x), y_pred(x))
        )
    )),
    # ... conditions 2 and 3
)
```

**Key Innovations**:
1. **Witness Registry**: Central storage for witness predicates
2. **Formula-based Keys**: Each formula gets its own witnesses
3. **Persistent Functions**: Witnesses exist throughout model lifecycle
4. **Direct Access**: No existential quantification needed

**Implementation Details**:
- Witnesses created during formula construction
- Stored in model for later access
- Retrieved during evaluation phase
- Enables correct verifier computation

**Advantages**:
- ✅ Completely solves False Premise Problem
- ✅ Witnesses persist across phases
- ✅ Direct access during evaluation
- ✅ Clean theoretical correspondence

**Status**: ✅ **SUCCESS** - Production implementation

---

## Performance Comparison

Based on testing with 34 examples:

| Strategy | Success Rate | Avg Time | Notes |
|----------|-------------|----------|-------|
| QA | 41.2% | 0.241s | Original default |
| QI | 35.3% | 0.188s | Index approach |
| QI2 | 35.3% | 0.195s | Index variant |
| BQI | 29.4% | 20.373s | Very slow |
| NF | 44.1% | 0.302s | Better but incomplete |
| NA | 41.2% | 0.195s | Array variant |
| SK | 44.1% | 0.329s | Closest attempt |
| CD | 38.2% | 0.317s | Enumeration approach |
| MS | **50.0%** | 0.387s | Best Strategy1 |
| UF | 41.2% | 0.319s | Axiom approach |
| WD | 35.3% | 0.473s | Pre-computation |
| **Witness** | **100%** | ~0.3s | Complete solution |

## Key Lessons

1. **Existential Quantification is Fatal**: Any strategy using `Exists` for witnesses fails
2. **Naming Helps but Isn't Enough**: NF/NA/SK get closer but lack infrastructure
3. **Enumeration Doesn't Scale**: CD/WD work for toys but fail on real examples
4. **Type Safety Helps**: MS achieves 50% through better engineering
5. **Only Witness Predicates Solve It**: Making witnesses first-class is essential

## Recommendation

Use the **Witness Predicate** (Strategy2) implementation. It's the only approach that:
- Correctly implements the theoretical semantics
- Preserves witness information across phases
- Achieves 100% success rate
- Scales to arbitrary formula complexity

The Strategy1 approaches, while educational, fundamentally cannot solve the False Premise Problem due to the two-phase architecture constraint.