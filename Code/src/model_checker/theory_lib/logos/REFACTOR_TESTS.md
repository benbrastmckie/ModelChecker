# Logos Theory Testing Refactor Implementation Plan

## Request Context

**Original Request**: I'm looking to refactor the unit testing that takes place throughout the logos/ theory. I want there to be two types of tests: those to do with running the model-checker on examples; and those to do with the software (the implementation itself). I ultimately want to be able to test the entire model-checker for all examples in each theory, and separately, for all software tests. I want to design a systematic testing harness which can be broken down to test subpackages, theories, and even subtheories separately when it is convenient to do so by using flags. For instance, I want --logos --counterfactual will specify to only run example tests for the counterfactual subtheory of the logos, whereas adding another --package flag will specify instead to only run the other software-package tests which make sure the implementation is working.

## Current State Analysis

### Existing Test Structure Problems

1. **Test Duplication**: Examples are tested in both unified (`test_logos_examples.py`) and individual subtheory test files
2. **Inconsistent Organization**: Tests scattered across 14 files with overlapping responsibilities  
3. **Missing Unit Tests**: No tests for individual semantic methods, operator implementations, or error conditions
4. **Brittle Assertions**: Hard-coded operator counts and expectations that break with changes
5. **Complex Dependencies**: Each test file manages its own operator registry creation
6. **No Systematic CLI**: Limited granular testing options compared to desired functionality
7. **Maintenance Burden**: Changes require updates in multiple locations

### Current Test Files

**Main Test Directory** (`src/model_checker/theory_lib/logos/tests/`):
- `test_logos.py` - Theory loading and basic functionality tests
- `test_logos_examples.py` - Unified example testing (main entry point)
- `test_subtheories.py` - Subtheory isolation tests

**Subtheory Test Directories** (5 files in `subtheories/*/tests/`):
- `test_extensional_examples.py`
- `test_modal_examples.py` 
- `test_constitutive_examples.py`
- `test_counterfactual_examples.py`
- `test_relevance_examples.py`

## Refactor Goals

### Primary Objectives

1. **Clear Separation**: Distinct example tests vs. unit tests
2. **Granular Control**: Flexible CLI for testing specific components
3. **Eliminate Duplication**: Single source of truth for each test type
4. **Systematic Coverage**: Comprehensive testing of all components
5. **Maintainable Structure**: Easy to understand and modify
6. **Foundation for Extension**: Template for other theories

### Design Principles (from CLAUDE.md)

- **Fail Fast**: Let errors occur naturally with clear tracebacks
- **Deterministic Behavior**: No fallbacks or implicit conversions
- **Required Parameters**: Explicit parameter passing
- **Clear Data Flow**: Transparent execution paths  
- **Root Cause Analysis**: Address underlying issues, not symptoms

## Implementation Plan

### Phase 1: Restructure Test Organization ✓

#### 1.1 Create New Directory Structure ✓

**Status**: COMPLETED
- Created `tests/test_examples/` directory for example tests
- Created `tests/test_unit/` directory for unit tests  
- Created `conftest.py` with common fixtures
- Copied `test_logos_examples.py` to new location

```
logos/
├── tests/
│   ├── __init__.py
│   ├── conftest.py                      # Pytest fixtures and configuration
│   ├── test_examples/
│   │   ├── __init__.py
│   │   ├── test_logos_examples.py       # Unified example testing (entry point)
│   │   ├── test_extensional_examples.py # Extensional subtheory examples
│   │   ├── test_modal_examples.py       # Modal subtheory examples
│   │   ├── test_constitutive_examples.py # Constitutive subtheory examples  
│   │   ├── test_counterfactual_examples.py # Counterfactual subtheory examples
│   │   └── test_relevance_examples.py   # Relevance subtheory examples
│   └── test_unit/
│       ├── __init__.py
│       ├── test_semantic_methods.py     # Test LogosSemantics methods
│       ├── test_operators.py            # Test operator implementations
│       ├── test_registry.py             # Test LogosOperatorRegistry
│       ├── test_proposition.py          # Test LogosProposition  
│       ├── test_model_structure.py      # Test LogosModelStructure
│       └── test_error_conditions.py     # Test error handling
```

#### 1.2 Remove Duplicate Test Files

**Files to Remove**:
- `subtheories/extensional/tests/test_extensional_examples.py`
- `subtheories/modal/tests/test_modal_examples.py`
- `subtheories/constitutive/tests/test_constitutive_examples.py`
- `subtheories/counterfactual/tests/test_counterfactual_examples.py`
- `subtheories/relevance/tests/test_relevance_examples.py`

**Files to Consolidate**:
- Merge relevant parts of `test_logos.py` and `test_subtheories.py` into new unit test files

### Phase 2: Implement Example Tests ✓

#### 2.1 Update Example Variable Names ✓

**Status**: COMPLETED
- Updated all subtheory examples.py files to use `unit_tests` variable name
- Updated main logos examples.py to import from `unit_tests`
- Removed all legacy variable references
- Verified imports work correctly (129 total examples)

#### 2.2 Create Unified Example Test Entry Point ✓

**Status**: COMPLETED  
- Moved existing test_logos_examples.py to new location
- Updated imports to use `unit_tests` variable

**File**: `tests/test_examples/test_logos_examples.py`

Key features:
- Single entry point for `test_theories.py`
- Parametrized testing across all subtheory examples
- Dynamic operator registry loading based on example prefixes
- Clear expectation handling from settings

#### 2.3 Create Subtheory-Specific Example Tests ✓

**Status**: COMPLETED
- Created individual test files for each subtheory
- Each file tests only examples from its specific subtheory
- Load minimal required operators for efficiency
- Use same test pattern as unified tests

**Files Created**:
- `test_extensional_examples.py` - 14 tests (extensional only)
- `test_modal_examples.py` - 23 tests (extensional + modal)  
- `test_constitutive_examples.py` - 33 tests (extensional + modal + constitutive)
- `test_counterfactual_examples.py` - 33 tests (extensional + modal + counterfactual)
- `test_relevance_examples.py` - 20 tests (extensional + modal + constitutive + relevance)

**Note**: Currently running 408 tests total due to duplication between unified and individual files. This will be resolved in Phase 5 cleanup.

#### 2.4 Implement Example Test Fixtures ✓

**Status**: COMPLETED
- Created `tests/conftest.py` with common fixtures
- Fixtures for each theory configuration (extensional, modal, constitutive, etc.)
- Settings fixtures for different test complexity levels
- Ready for use by both example and unit tests

### Phase 3: Implement Unit Tests

#### 3.1 Semantic Method Tests

**File**: `tests/test_unit/test_semantic_methods.py`

Test coverage:
```python
class TestLogosSemantics:
    def test_initialization(self):
        """Test semantics initialization with various settings."""
    
    def test_world_creation(self):
        """Test world generation and structure."""
    
    def test_fusion_operations(self):
        """Test semantic fusion methods."""
    
    def test_proposition_evaluation(self):
        """Test formula evaluation methods."""
    
    def test_constraint_generation(self):
        """Test model constraint creation."""
```

#### 3.2 Operator Implementation Tests

**File**: `tests/test_unit/test_operators.py`

Test coverage:
```python
class TestOperatorImplementations:
    def test_extensional_operators(self):
        """Test truth-functional operator semantics."""
    
    def test_modal_operators(self):
        """Test necessity and possibility operator semantics."""
    
    def test_constitutive_operators(self):
        """Test ground and essence operator semantics."""
    
    def test_counterfactual_operators(self):
        """Test counterfactual conditional semantics."""
    
    def test_relevance_operators(self):
        """Test relevance-sensitive operator semantics."""
```

#### 3.3 Registry Tests

**File**: `tests/test_unit/test_registry.py`

Test coverage:
```python
class TestLogosOperatorRegistry:
    def test_selective_loading(self):
        """Test loading specific subtheories."""
    
    def test_dependency_resolution(self):
        """Test automatic dependency loading."""
    
    def test_operator_counts(self):
        """Test expected operator counts per subtheory."""
    
    def test_operator_conflicts(self):
        """Test handling of operator name conflicts."""
```

#### 3.4 Error Condition Tests

**File**: `tests/test_unit/test_error_conditions.py`

Test coverage:
```python
class TestErrorConditions:
    def test_invalid_operator_combinations(self):
        """Test error handling for invalid operator usage."""
    
    def test_malformed_examples(self):
        """Test error handling for malformed example data."""
    
    def test_timeout_conditions(self):
        """Test behavior under timeout conditions."""
    
    def test_memory_limits(self):
        """Test behavior at memory limits."""
```

### Phase 4: Enhanced CLI Integration

#### 4.1 Extend test_theories.py

Add support for granular testing flags:

```python
def add_logos_args(parser):
    """Add logos-specific argument parsing."""
    logos_group = parser.add_argument_group('logos testing options')
    
    # Test type selection
    logos_group.add_argument('--examples', nargs='*', 
                           help='Run example tests only. Optionally specify example names')
    logos_group.add_argument('--unit', action='store_true', 
                           help='Run unit tests only')
    
    # Subtheory selection
    logos_group.add_argument('--extensional', action='store_true',
                           help='Test extensional subtheory only')
    logos_group.add_argument('--modal', action='store_true',
                           help='Test modal subtheory only') 
    logos_group.add_argument('--constitutive', action='store_true',
                           help='Test constitutive subtheory only')
    logos_group.add_argument('--counterfactual', action='store_true',
                           help='Test counterfactual subtheory only')
    logos_group.add_argument('--relevance', action='store_true',
                           help='Test relevance subtheory only')
    
    # Unit test categories
    logos_group.add_argument('--semantics', action='store_true',
                           help='Test semantic methods only')
    logos_group.add_argument('--operators', action='store_true',
                           help='Test operator implementations only')
    logos_group.add_argument('--registry', action='store_true',
                           help='Test registry functionality only')
```

#### 4.2 Implement Test Selection Logic

```python
def build_logos_test_command(args):
    """Build pytest command for logos testing."""
    base_dir = "src/model_checker/theory_lib/logos/tests"
    command = ["pytest"]
    
    # Determine test directories
    if args.examples is not None and not args.unit:
        command.append(f"{base_dir}/test_examples")
    elif args.unit and args.examples is None:
        command.append(f"{base_dir}/test_unit") 
    elif args.examples is None and not args.unit:
        command.append(base_dir)  # All tests
    
    # Handle specific example names
    if args.examples and len(args.examples) > 0:
        # User specified specific examples
        example_names = args.examples
        if len(example_names) == 1 and '*' in example_names[0]:
            # Wildcard pattern
            command.extend(["-k", example_names[0].replace('*', '')])
        else:
            # Exact matches - create OR expression
            test_expr = " or ".join(f"test_logos_examples[{name}]" for name in example_names)
            command.extend(["-k", test_expr])
    elif args.examples is not None:
        # --examples flag without specific names (run all examples)
        # Add subtheory filters if specified
        if args.extensional:
            command.extend(["-k", "extensional or EXT_"])
        elif args.modal:
            command.extend(["-k", "modal or MOD_"])
        elif args.constitutive:
            command.extend(["-k", "constitutive or CON_"])
        elif args.counterfactual:
            command.extend(["-k", "counterfactual or CF_"])
        elif args.relevance:
            command.extend(["-k", "relevance or REL_"])
    
    # Add unit test filters
    if args.unit:
        if args.semantics:
            command.extend(["-k", "semantic"])
        elif args.operators:
            command.extend(["-k", "operator"])
        elif args.registry:
            command.extend(["-k", "registry"])
    
    return command

def validate_example_names(example_names, theory='logos'):
    """Validate that specified example names exist."""
    from model_checker.theory_lib.logos.examples import unit_tests
    
    available_examples = list(unit_tests.keys())
    invalid_names = []
    
    for name in example_names:
        if '*' not in name and name not in available_examples:
            invalid_names.append(name)
    
    if invalid_names:
        print(f"Error: Unknown example names: {', '.join(invalid_names)}")
        print(f"Available examples: {', '.join(sorted(available_examples))}")
        
        # Suggest similar names
        for invalid in invalid_names:
            similar = [ex for ex in available_examples if invalid.lower() in ex.lower()]
            if similar:
                print(f"Did you mean: {', '.join(similar[:3])}?")
        
        return False
    return True
```

### Phase 5: Migration and Testing

#### 5.1 Update Example Files

Update all `examples.py` files to use consistent variable naming:

```python
# In each subtheory's examples.py file:

# Use only 'unit_tests' as the standardized variable name
unit_tests = {
    **extensional_cm_examples,
    **extensional_th_examples,
}

# Remove any legacy variable names like 'test_example_range'
```

This ensures:
- Consistent variable naming across all subtheories
- Clean codebase without legacy naming conventions
- Clear convention for future theories
- Single source of truth for example definitions

#### 5.2 Migration Steps

1. **Update example variable names** in all subtheory examples.py files
2. **Create new directory structure** without removing old files
3. **Implement new test files** with comprehensive coverage
4. **Test new structure** to ensure all functionality works
5. **Update test_theories.py** to use new structure
6. **Remove old test files** after validation
7. **Update documentation** to reflect new structure

#### 5.2 Validation Process

```bash
# Test that the refactored structure works correctly
python test_theories.py --theories logos

# Test new granular options
python test_theories.py --theories logos --examples
python test_theories.py --theories logos --unit
python test_theories.py --theories logos --examples --counterfactual
python test_theories.py --theories logos --unit --operators

# Test specific example selection
python test_theories.py --theories logos --examples CF_CM_1
python test_theories.py --theories logos --examples CF_CM_1 CF_TH_2
python test_theories.py --theories logos --examples "CF_*"
python test_theories.py --theories logos --examples "*_TH_*"

# Compare results to ensure no regressions
```

#### 5.3 Performance Verification

- Measure test execution times before and after refactor
- Ensure parallel testing still works efficiently
- Verify memory usage patterns remain reasonable
- Test timeout handling in new structure

### Phase 6: Documentation and Extension

#### 6.1 Update Documentation

- Update `logos/README.md` with new testing approach
- Create testing examples in documentation
- Update project-level `TESTS.md` with logos as example
- Document CLI usage patterns

#### 6.2 Create Extension Template

Create `THEORY_TESTING_TEMPLATE.md` that other theories can follow:
- Directory structure template
- Test file templates
- CLI integration patterns
- Common fixture patterns

## Expected Outcomes

### Immediate Benefits

1. **Clear Test Separation**: Distinct example vs. unit tests
2. **No Duplication**: Single location for each type of test
3. **Granular Control**: Precise testing through CLI flags
4. **Targeted Example Testing**: Run specific examples by name for rapid debugging
5. **Comprehensive Coverage**: Both integration and unit testing
6. **Maintainable Structure**: Easy to understand and modify

### Long-term Benefits  

1. **Foundation for Other Theories**: Template for systematic testing
2. **Improved Development Workflow**: Faster feedback through targeted testing
3. **Better Error Detection**: Unit tests catch implementation issues early
4. **Easier Debugging**: Clear test isolation helps identify problems
5. **Consistent Testing Standards**: Project-wide testing methodology

## Risk Assessment

### Potential Issues

1. **Migration Complexity**: Moving from 14 files to new structure
2. **CLI Integration**: Ensuring new flags integrate properly with the testing framework
3. **Test Discovery**: Pytest finding all tests in new structure
4. **Performance Impact**: New structure should not slow testing
5. **Workflow Transition**: Users need to adapt to new testing patterns

### Mitigation Strategies

1. **Parallel Implementation**: Build new structure while keeping old temporarily
2. **Extensive Testing**: Validate new structure thoroughly before full transition
3. **Clear Documentation**: Document changes and new workflows comprehensively
4. **Quick Transition**: Remove old structure once new is validated
5. **User Communication**: Clearly communicate improvements and new capabilities

This refactor plan provides a systematic approach to creating a modern, maintainable, and extensible testing framework for the logos theory that can serve as a foundation for the entire ModelChecker project.