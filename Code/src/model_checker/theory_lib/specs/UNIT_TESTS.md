# Unified Test Runner Implementation Plan

## Overview

This document outlines the implementation plan for a new unified test runner (`run_tests.py`) that replaces the current `test_theories.py` and `test_package.py` scripts. Based on comprehensive analysis of the existing codebase, this plan establishes high-quality, consistent testing standards across all theories and components.

## Current Testing Landscape Analysis

### Existing Testing Architecture

The ModelChecker codebase implements a sophisticated dual-testing framework:

**Test Categories:**
1. **Example Tests** (Integration): Test logical arguments end-to-end using real premises/conclusions
2. **Unit Tests** (Component): Test individual classes, methods, and operators
3. **Package Tests** (Infrastructure): Test framework components (builder, settings, iterate)
4. **Validation Tests** (Error conditions): Test input validation and edge cases

**Current Best Practice: Logos Theory**
- 238+ comprehensive tests (129 example + 109 unit tests)
- Advanced pytest fixtures and parametrization
- Subtheory-specific testing (modal, counterfactual, extensional, constitutive, relevance)
- Sophisticated CLI with inclusive-by-default approach

**Quality Gaps Identified:**
- Other theories lack comprehensive unit testing
- Inconsistent variable naming (`test_example_range` vs `unit_tests`)
- Missing documentation in some test directories
- No unified test runner interface

## Design Goals

1. **Standardization**: Bring all theories to logos-level testing quality
2. **Consistency**: Uniform patterns, naming, and structure across codebase
3. **Granular Control**: Target specific theories, subtheories, and test types
4. **Quality Focus**: Comprehensive coverage without backward compatibility constraints
5. **Maintainability**: Clean, extensible architecture for future development

## Unified Test Runner Interface

### Command Structure

#### Primary Test Categories
```bash
# Run everything (examples + unit + package tests, exclude default theory)
./run_tests.py

# Run only example tests (integration tests from examples.py)
./run_tests.py --examples

# Run only unit tests (component/implementation tests)
./run_tests.py --unit

# Run only package tests (framework infrastructure)
./run_tests.py --package

# Combine test types
./run_tests.py --examples --unit        # Examples + unit tests
./run_tests.py --unit --package         # Unit + package tests
```

#### Theory and Subtheory Selection
```bash
# Test specific theories
./run_tests.py logos exclusion bimodal

# Test specific theories with test type restriction
./run_tests.py --examples logos exclusion
./run_tests.py --unit logos bimodal
./run_tests.py --package builder settings

# Test logos subtheories (granular control)
./run_tests.py logos modal                    # All logos modal tests
./run_tests.py logos modal counterfactual     # Modal + counterfactual subtheories
./run_tests.py --examples logos modal         # Only example tests for modal
./run_tests.py --unit logos modal relevance   # Only unit tests for modal + relevance
```

#### Standard Testing Options
```bash
./run_tests.py -v --failfast logos modal      # Verbose, fail-fast
./run_tests.py --cov --cov-report=html        # Coverage reporting
./run_tests.py --markers performance          # Performance tests only
./run_tests.py --durations=10                 # Show slowest 10 tests
```

## Implementation Architecture

### Core Classes

#### `TestRunner` (Main Controller)
```python
class TestRunner:
    """Main test runner coordinating all test execution."""
    
    def __init__(self):
        self.theories = self._discover_theories()          # ['logos', 'exclusion', 'bimodal', 'imposition']
        self.components = self._discover_components()      # ['builder', 'settings', 'iterate', 'theory_lib']
        self.subtheories = self._discover_subtheories()    # {'logos': ['modal', 'counterfactual', ...]}
        self.test_categories = ['examples', 'unit', 'package']
    
    def run(self, config: TestConfig) -> TestResults:
        """Execute tests based on configuration."""
        results = TestResults()
        
        if config.run_examples:
            results.merge(self._run_example_tests(config))
        if config.run_unit:
            results.merge(self._run_unit_tests(config))
        if config.run_package:
            results.merge(self._run_package_tests(config))
            
        return results
    
    def _discover_theories(self) -> List[str]:
        """Discover available theories, excluding 'default' by design."""
        # Returns theories with proper test directories, excludes default
    
    def _discover_subtheories(self) -> Dict[str, List[str]]:
        """Discover subtheories for theories that support them."""
        # Currently only logos supports subtheories
```

#### `TestConfig` (Configuration Management)
```python
@dataclass
class TestConfig:
    """Immutable test configuration."""
    theories: List[str]
    subtheories: Dict[str, List[str]]  # theory -> list of subtheories
    components: List[str]
    run_examples: bool
    run_unit: bool 
    run_package: bool
    verbose: bool
    failfast: bool
    coverage: bool
    markers: List[str]
    pytest_args: List[str]
    
    @classmethod
    def from_args(cls, args) -> 'TestConfig':
        """Create configuration from command line arguments."""
    
    def validate(self, runner: TestRunner) -> None:
        """Validate configuration against available theories/components."""
```

#### `ExampleTestRunner` (Example Test Execution)
```python
class ExampleTestRunner:
    """Runs integration tests from examples.py files."""
    
    def run_example_tests(self, config: TestConfig) -> TestResults:
        """Run example tests for specified theories/subtheories."""
        results = TestResults()
        
        for theory in config.theories:
            test_dir = f"src/model_checker/theory_lib/{theory}/tests"
            filters = self._build_example_filters(theory, config.subtheories.get(theory, []))
            
            result = self._execute_pytest(
                test_dir=test_dir,
                filters=filters,
                markers=['countermodel', 'theorem'],  # Example-specific markers
                config=config
            )
            results.add_theory_result(theory, 'examples', result)
            
        return results
    
    def _build_example_filters(self, theory: str, subtheories: List[str]) -> List[str]:
        """Build pytest -k filters for subtheory selection."""
        if theory != 'logos' or not subtheories:
            return []  # No filtering needed
        
        # Map subtheories to test patterns (based on logos implementation)
        subtheory_patterns = {
            'modal': '(modal or MOD_)',
            'counterfactual': '(counterfactual or CF_)', 
            'extensional': '(extensional or EXT_)',
            'constitutive': '(constitutive or CON_ or CL_)',
            'relevance': '(relevance or REL_)'
        }
        
        patterns = [subtheory_patterns[sub] for sub in subtheories if sub in subtheory_patterns]
        return [f"({' or '.join(patterns)})"] if patterns else []
```

#### `UnitTestRunner` (Unit Test Execution)
```python
class UnitTestRunner:
    """Runs unit tests for theory implementations."""
    
    def run_unit_tests(self, config: TestConfig) -> TestResults:
        """Run unit tests for specified theories/subtheories."""
        results = TestResults()
        
        for theory in config.theories:
            test_dir = f"src/model_checker/theory_lib/{theory}/tests"
            filters = self._build_unit_filters(theory, config.subtheories.get(theory, []))
            
            result = self._execute_pytest(
                test_dir=test_dir,
                filters=filters,
                markers=['unit', 'semantic', 'operator'],  # Unit test markers
                exclude_patterns=['test_*_examples'],  # Exclude example tests
                config=config
            )
            results.add_theory_result(theory, 'unit', result)
            
        return results
    
    def _build_unit_filters(self, theory: str, subtheories: List[str]) -> List[str]:
        """Build pytest filters for unit tests, excluding example tests."""
        filters = ['not test_examples']  # Exclude example test files
        
        if theory == 'logos' and subtheories:
            # Add subtheory filtering for logos unit tests
            subtheory_filters = self._get_subtheory_unit_patterns(subtheories)
            filters.append(f"({' or '.join(subtheory_filters)})")
            
        return filters
```

#### `PackageTestRunner` (Package Test Execution)
```python
class PackageTestRunner:
    """Runs package/infrastructure component tests."""
    
    def run_package_tests(self, config: TestConfig) -> TestResults:
        """Run tests for specified package components."""
        results = TestResults()
        
        for component in config.components:
            test_dir = f"src/model_checker/{component}/tests"
            
            result = self._execute_pytest(
                test_dir=test_dir,
                markers=['infrastructure', 'validation'],
                config=config
            )
            results.add_component_result(component, result)
            
        return results
```

### Directory Structure and Test Organization

#### Standardized Theory Testing Structure
```
src/model_checker/theory_lib/{theory}/tests/
├── conftest.py                    # pytest fixtures and configuration
├── test_{theory}_examples.py      # Example/integration tests (from examples.py)
├── test_semantic_methods.py       # Unit tests for semantic implementation
├── test_operators.py              # Unit tests for all operators
├── test_proposition.py            # Unit tests for proposition functionality
├── test_registry.py               # Unit tests for operator registration
└── README.md                      # Testing documentation
```

#### Package Component Testing Structure
```
src/model_checker/{component}/tests/
├── test_{component}.py            # Main component functionality
├── test_validation.py             # Input validation and error conditions
├── test_integration.py            # Cross-component integration
└── README.md                      # Component testing documentation
```

### Test Standardization Requirements

#### Variable Naming Standardization
```python
# Standardize across all theories (currently inconsistent)
unit_tests = {
    'example_name': (premises, conclusions, settings, expectation),
    # ... 
}

# NOT: test_example_range, example_range, test_cases, etc.
```

#### Pytest Fixture Standardization
```python
# conftest.py pattern for all theories
@pytest.fixture
def basic_settings():
    """Basic settings for theory testing."""
    return {
        'N': 4,
        'contingent': False,
        'non_empty': False,
        'max_time': 1
    }

@pytest.fixture  
def theory_semantics(basic_settings):
    """Create semantics instance for testing."""
    return TheorySemantics(basic_settings, operator_registry)

@pytest.fixture
def theory_proposition(theory_semantics):
    """Create proposition instance for testing.""" 
    return TheoryProposition(theory_semantics)
```

#### Test Pattern Standardization
```python
# Example test pattern (integration)
@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_examples(example_name, example_case, theory_semantics, theory_proposition):
    """Test logical examples from unit_tests."""
    premises, conclusions, settings, expectation = example_case
    result = run_test(premises, conclusions, settings, theory_semantics, theory_proposition, operators)
    assert result == expectation, f"Failed: {example_name}"

# Unit test pattern (component testing)
def test_semantic_method_fusion(theory_semantics):
    """Test semantic fusion operation."""
    world_a = theory_semantics.create_world({'A': True})
    world_b = theory_semantics.create_world({'B': True}) 
    fused = theory_semantics.fusion(world_a, world_b)
    assert fused.verify({'A': True, 'B': True})
```

### Error Handling and Validation

#### Theory/Subtheory Validation
```python
class TestConfigValidator:
    """Validates test configuration before execution."""
    
    def validate_theories(self, theories: List[str], available: List[str]) -> None:
        """Validate requested theories exist."""
        invalid = [t for t in theories if t not in available]
        if invalid:
            available_str = ', '.join(sorted(available))
            raise ValueError(f"Unknown theories: {invalid}. Available: {available_str}")
    
    def validate_subtheories(self, theory: str, subtheories: List[str], 
                           available_subtheories: Dict[str, List[str]]) -> None:
        """Validate subtheories belong to theory."""
        if subtheories and theory not in available_subtheories:
            raise ValueError(f"Theory '{theory}' does not support subtheories")
        
        if subtheories:
            valid = available_subtheories[theory]
            invalid = [s for s in subtheories if s not in valid]
            if invalid:
                valid_str = ', '.join(sorted(valid))
                raise ValueError(f"Unknown subtheories for {theory}: {invalid}. Available: {valid_str}")
    
    def validate_components(self, components: List[str], available: List[str]) -> None:
        """Validate requested components exist."""
        invalid = [c for c in components if c not in available]
        if invalid:
            available_str = ', '.join(sorted(available))
            raise ValueError(f"Unknown components: {invalid}. Available: {available_str}")
```

### Advanced Features

#### Test Discovery and Categorization
```python
def discover_test_capabilities():
    """Discover what tests are available for each theory."""
    capabilities = {}
    
    for theory in ['logos', 'exclusion', 'bimodal', 'imposition']:
        test_dir = f"src/model_checker/theory_lib/{theory}/tests"
        if not os.path.exists(test_dir):
            continue
            
        has_examples = any('example' in f for f in os.listdir(test_dir) if f.endswith('.py'))
        has_units = any('semantic' in f or 'operator' in f for f in os.listdir(test_dir) if f.endswith('.py'))
        
        capabilities[theory] = {
            'has_examples': has_examples,
            'has_unit_tests': has_units,
            'supports_subtheories': theory == 'logos',
            'subtheories': ['modal', 'counterfactual', 'extensional', 'constitutive', 'relevance'] if theory == 'logos' else []
        }
    
    return capabilities
```

#### Coverage Integration
```python
def setup_coverage_reporting(config: TestConfig) -> List[str]:
    """Configure coverage reporting for pytest."""
    if not config.coverage:
        return []
    
    coverage_args = [
        '--cov=src/model_checker',
        '--cov-report=term-missing',
        '--cov-report=html:htmlcov',
        '--cov-fail-under=80'
    ]
    
    # Focus coverage on tested theories/components
    if config.theories:
        for theory in config.theories:
            coverage_args.append(f'--cov=src/model_checker/theory_lib/{theory}')
    
    return coverage_args
```

## Implementation Phases

### Phase 1: Core Infrastructure (High Priority) ✅ COMPLETED
1. **Create `run_tests.py`** with basic TestRunner class ✅
2. **Implement argument parsing** with theory/subtheory support ✅
3. **Add comprehensive validation** for all input combinations ✅
4. **Create TestConfig and TestResults** data structures ✅

**Phase 1 Achievements:**
- ✅ Comprehensive command-line interface with `--examples`, `--unit`, `--package` flags
- ✅ Theory and subtheory parsing (e.g., `logos modal counterfactual`)
- ✅ Automatic discovery of theories (excluding default) and components
- ✅ Robust validation with helpful error messages
- ✅ Clean architecture with TestRunner, TestConfig, TestResults classes
- ✅ Placeholder test execution ready for Phase 2 implementation
- ✅ Comprehensive help documentation and usage examples

**Testing Results:**
- ✅ Discovery works: Found 4 theories (bimodal, exclusion, imposition, logos) and 4 components
- ✅ Theory/subtheory parsing: `./run_tests.py logos modal` correctly parsed
- ✅ Component selection: `./run_tests.py --package --components builder settings` works
- ✅ Error handling: Invalid theories/subtheories provide helpful error messages
- ✅ Default behavior: Running without arguments shows available targets and runs all tests

### Phase 2: Test Execution Engine (High Priority) ✅ COMPLETED
1. **Implement ExampleTestRunner** with subtheory filtering ✅
2. **Implement UnitTestRunner** with component testing ✅
3. **Implement PackageTestRunner** with infrastructure testing ✅
4. **Add pytest command construction** with proper environment setup ✅

**Phase 2 Achievements:**
- ✅ **Real pytest execution**: Full integration with actual test execution
- ✅ **Logos subtheory support**: Proper handling of logos unique directory structure
- ✅ **Smart filtering**: Works with both 'examples' and 'example_cases' patterns
- ✅ **Environment setup**: Proper PYTHONPATH configuration for all tests
- ✅ **Comprehensive test types**: Examples, unit tests, and package tests all working
- ✅ **Subtheory filtering**: Granular control over logos subtheories
- ✅ **Error handling**: Robust error handling with helpful messages
- ✅ **Performance options**: Verbose and failfast support across all test types

**Testing Results:**
- ✅ **Examples**: `./run_tests.py --examples logos modal` (23 tests passed)
- ✅ **Unit tests**: `./run_tests.py --unit logos modal` (3 tests passed, 37 filtered out)  
- ✅ **Package tests**: `./run_tests.py --package --components builder` (32 tests passed)
- ✅ **Standard theories**: `./run_tests.py --examples exclusion` (working correctly)
- ✅ **Command combinations**: All flag combinations tested and working

### Phase 3: Cleanup and Documentation ✅ COMPLETED
1. **Remove legacy test scripts** (test_theories.py, test_package.py) ✅
2. **Update CLAUDE.md** with new unified test runner commands ✅
3. **Comprehensive testing** of all functionality ✅
4. **Final validation** of complete implementation ✅

**Phase 3 Achievements:**
- ✅ **Legacy cleanup**: Removed old test_theories.py and test_package.py scripts
- ✅ **Documentation update**: Updated CLAUDE.md with new command structure
- ✅ **Comprehensive validation**: Tested all combinations successfully
- ✅ **Multiple subtheories**: `logos modal counterfactual` (56 tests) working perfectly
- ✅ **Multiple components**: `builder settings theory_lib` all working correctly
- ✅ **Combined test types**: `--examples --unit` flags working together
- ✅ **Error handling**: Robust validation and helpful error messages
- ✅ **Quality achievement**: Clean, maintainable, extensible implementation

## Implementation Status: ✅ COMPLETE

### Final Implementation Summary

The unified test runner (`run_tests.py`) has been successfully implemented with:

**✅ Core Features Implemented:**
- **Single entry point**: `./run_tests.py` replaces both legacy scripts
- **Three test categories**: `--examples`, `--unit`, `--package` with clear separation
- **Theory/subtheory selection**: Granular control (e.g., `logos modal counterfactual`)
- **Component selection**: Package infrastructure testing
- **Smart filtering**: Works with both 'examples' and 'example_cases' patterns
- **Logos specialization**: Handles unique subtheory directory structure
- **Environment setup**: Proper PYTHONPATH configuration
- **Error handling**: Comprehensive validation with helpful messages

**✅ Testing Results Verified:**
- **Examples**: 23 modal + 33 counterfactual = 56 subtheory tests passing
- **Unit tests**: Modal subtheory filtering (3 tests passed, 37 filtered correctly)
- **Package tests**: Builder (32 tests), settings (6 tests), theory_lib working
- **Combined execution**: `--examples --unit` running both test types successfully
- **Error validation**: Invalid theories/subtheories provide clear error messages

**✅ Quality Standards Achieved:**
- **No backward compatibility**: Clean implementation prioritizing quality
- **Consistent interface**: Uniform patterns across all test types
- **Maintainable architecture**: Easy to extend for new theories/components
- **Comprehensive documentation**: Clear usage examples and help text
- **Performance optimized**: Selective execution for rapid development

### Future Phases (Optional Enhancements)

### Phase 4: Advanced Features (Optional)
1. **Integrate coverage reporting** with focused coverage
2. **Add performance testing** framework and markers  
3. **Implement test discovery** and capability reporting
4. **Add parallel test execution** for performance

### Phase 5: Standardization (Optional)
1. **Standardize variable naming** (`unit_tests` across all theories)
2. **Create conftest.py templates** for theories missing fixtures
3. **Implement missing unit tests** for exclusion, bimodal, imposition theories
4. **Add comprehensive README files** for all test directories

## Quality Standards and Best Practices

### Code Quality Requirements
1. **Type hints**: All new code uses comprehensive type annotations
2. **Error handling**: Comprehensive validation with helpful error messages
3. **Documentation**: Docstrings for all classes and public methods
4. **Testing**: The test runner itself needs comprehensive unit tests

### Testing Standards
1. **Consistent naming**: Use `unit_tests` variable name across all theories
2. **Comprehensive fixtures**: All theories should have conftest.py with standard fixtures
3. **Parametrized testing**: Use pytest.mark.parametrize for systematic coverage
4. **Clear markers**: Use appropriate pytest markers for test categorization

### Performance Requirements
1. **Fast feedback**: Common test combinations should complete within 30 seconds
2. **Parallel execution**: Support pytest-xdist for parallel test execution  
3. **Selective execution**: Ability to run minimal test sets for rapid development
4. **Progress reporting**: Clear indication of test progress for long-running tests

## Expected Usage Patterns

### Development Workflows
```bash
# Quick theory development feedback
./run_tests.py --examples logos modal

# Comprehensive theory testing before commit
./run_tests.py logos

# Component development testing
./run_tests.py --package builder --unit

# Full regression testing
./run_tests.py -v --cov

# Performance testing
./run_tests.py --markers performance -v

# Debugging specific failures
./run_tests.py --examples logos counterfactual -v --failfast
```

### Integration Testing
```bash
# Test all theories (exclude default)
./run_tests.py --examples

# Test all infrastructure
./run_tests.py --package  

# Complete test suite
./run_tests.py --cov --durations=10
```

### Continuous Integration
```bash
# Fast CI feedback (examples only)
./run_tests.py --examples --failfast

# Comprehensive CI testing
./run_tests.py --cov --cov-fail-under=80 --durations=0
```

## Benefits and Quality Improvements

### Immediate Benefits
1. **Single Entry Point**: Unified interface for all testing needs
2. **Granular Control**: Precise targeting of theories, subtheories, and test types
3. **Quality Standardization**: All theories brought to logos-level testing quality
4. **Better Developer Experience**: Intuitive, predictable commands

### Long-term Quality Improvements
1. **Maintainability**: Clean, extensible architecture for future theories
2. **Consistency**: Uniform patterns across entire codebase
3. **Comprehensive Coverage**: Systematic testing of all components
4. **Performance Optimization**: Efficient test execution with selective targeting

### Architectural Advantages
1. **Separation of Concerns**: Clear boundaries between test types and execution
2. **Extensibility**: Easy addition of new theories, subtheories, or test types
3. **Robustness**: Comprehensive validation and error handling
4. **Flexibility**: Multiple ways to combine and target tests for different workflows

This implementation plan provides a comprehensive foundation for building a world-class testing infrastructure that maintains the sophisticated capabilities of the current system while establishing consistent, high-quality standards across the entire ModelChecker codebase.